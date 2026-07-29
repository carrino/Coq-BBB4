#!/usr/bin/env python3
"""UNTRUSTED: the QUAD/QUAD probe -- read the LINEAR-SEARCH CARRY law off a
measured lap and validate it differentially.

`docs/WAVE26_FINDINGS.md` section 7.  The 41 QUAD/QUAD rows of the
`no interior chain` bucket are one shape: a binary increment whose carry is
done by linear search.  To find the first clear digit the head makes ONE
ROUND TRIP PER DIGIT -- out to the digit and back -- before probing one
deeper, so the lap makes Theta(j) excursions and no LapDecider chain (a
FIXED list of window steps, bounded sweeps) can be it at any framing.  What
IS a chain is each individual round trip: its (state, read, write, move)
sequence folds to a fixed pattern with counts affine in the probe index k,
measured 41/41.

The lap's skeleton, read off the trace rather than assumed:

  anchor ->(boot)-> M(1) ->(micro 1)-> M(2) -> ... -> M(j) ->(term)-> succ

where M(k) is the k-th RESTORE POINT: the tape content is EXACTLY the
anchor's again (each probe un-writes itself), the state is one fixed q_r,
and the head sits one stride deeper.  M(j) is the first clear digit; the
terminal sweep writes the carry there and clears the k probed digits on the
way home, so its cost is affine in j -- the FINAL k, which is what the Coq
board's Hterm has to tie to the anchor's carry index (WAVE26 7e).

This module reads (boot, micro, term) as folded step-RLEs with affine count
laws (per k-parity where needed -- the Bp cluster alternates), then
VALIDATES the whole law at unseen carry indices: exact restore times, exact
final time, exact successor tape, j = 2..8, interior AND overflow branch.
Wave-18's discipline: the law is read at one index and believed nowhere.

The Coq route this gates (not built here): the micro hop as a derived chain
(2-3 window steps), composed j times -- the count is KNOWN, so either a
NestedLapCascade-style descent induction or MeasureGlue.mrun with abstract
state (k, m), stepA (k, S m) = Some (S k, m), mu = snd, P = fun x =>
fst x + snd x = j.  Counters/MeasureGlue.v quantifies costs existentially,
so the quadratic total is no obstruction.  Precedent: Bounce_8.v.

Usage:
  quad_probe.py --law SPEC [-J 5]      # print the law, human-readable
  quad_probe.py --gate [--list FILE]   # law + validation over the bucket

UNTRUSTED like everything under tools/: measurement only.
"""
import argparse
import itertools
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

import ovfshape as OV                                          # noqa: E402
import lapcert as LC                                           # noqa: E402
from emit_interleave import parse, ENC, LAB                    # noqa: E402
from mirror_common import mirror_spec                          # noqa: E402


class QuadError(Exception):
    pass


# ------------------------------------------------------ the absolute replay ---

def _content(cfg, col):
    """The tape as a frozenset of (absolute column, symbol) set cells.
    l[i] sits at col-1-i, h at col, r[i] at col+1+i."""
    q, l, h, r = cfg
    out = {(col - 1 - i, s) for i, s in enumerate(l) if s} \
        | {(col + 1 + i, s) for i, s in enumerate(r) if s}
    if h:
        out.add((col, h))
    return frozenset(out)


def replay(tab, cfg0, tmax):
    """[(t, state, headcol, content)] from cfg0, headcol 0 at t=0."""
    cfg, col, out = cfg0, 0, []
    for t in range(tmax + 1):
        out.append((t, cfg[0], col, _content(cfg, col)))
        if t == tmax:
            break
        b = cfg
        cfg = LC.wstep(tab, False, False, cfg)
        col += 1 if len(cfg[1]) > len(b[1]) else -1
    return out


def steps_of(tab, cfg0, n):
    """The n (state, read, write, move) window steps from cfg0."""
    cfg, out = cfg0, []
    for _ in range(n):
        q, l, h, r = cfg
        w, mv, nq = tab[(q, h)]
        out.append((q, h, w, mv))
        cfg = LC.wstep(tab, False, False, cfg)
    return out


def rle_fold(steps):
    """Step-RLE folded one level: maximal repeats of 1- or 2-step blocks.

    (letters, counts): letters a tuple of blocks (each 1 or 2 steps),
    counts how often each block repeats consecutively.  Folding pairs is
    what the plain itertools RLE misses on the 2-cell alphabets, where a
    sweep alternates two states per cell."""
    seq = [(k, len(list(g))) for k, g in itertools.groupby(steps)]
    out, i = [], 0
    while i < len(seq):
        # try to fold an alternating pair (a x1, b x1)* into one block
        if (i + 3 < len(seq) and seq[i][1] == 1 and seq[i + 1][1] == 1
                and seq[i + 2] == seq[i] and seq[i + 3] == seq[i + 1]):
            a, b = seq[i][0], seq[i + 1][0]
            n = 0
            while (i + 1 < len(seq) and seq[i] == (a, 1)
                   and seq[i + 1] == (b, 1)):
                n += 1
                i += 2
            out.append(((a, b), n))
        else:
            out.append(((seq[i][0],), seq[i][1]))
            i += 1
    return tuple(x for x, _ in out), tuple(c for _, c in out)


def parse_counts(steps, blocks):
    """Counts c_i >= 0 with steps == concat(blocks[i] * c_i), or None.

    A tiny DP: folding each segment independently is scale-sensitive (a
    block repeated once never folds), so segments are parsed against ONE
    template -- the folded pattern of the largest-index segment."""
    n = len(steps)
    memo = {}

    def go(pos, bi):
        if (pos, bi) in memo:
            return memo[(pos, bi)]
        if bi == len(blocks):
            r = () if pos == n else None
        else:
            blk = blocks[bi]
            r = None
            c = 0
            while True:
                sub = go(pos + c * len(blk), bi + 1)
                if sub is not None:
                    r = (c,) + sub          # prefer the LARGEST count
                nxt = pos + c * len(blk)
                if steps[nxt:nxt + len(blk)] == list(blk) or                         steps[nxt:nxt + len(blk)] == blk:
                    c += 1
                else:
                    break
        memo[(pos, bi)] = r
        return r

    return go(0, 0)


# --------------------------------------------------------------- the reader ---

def interior_p(j):
    """A value with EXACTLY j trailing set digits: 3*2^j - 1."""
    return 3 * 2 ** j - 1


def overflow_p(j):
    return 2 ** (j + 1) - 1


def anchor_cfg(A, p):
    """The concrete anchor configuration, cascade_validate's convention."""
    return (A['st0'], tuple(A['encf'](p)) + tuple(A['tail']), 0,
            tuple(A['far']))


def lap_marks(tab, A, p, mode=(-1, False), tmax=200000):
    """One lap p -> p+1 from the synthetic anchor: (T, marks, steps).

    T is the exact lap time; marks the restore points [(t, state, col)]
    strictly inside the lap where the tape content is EXACTLY the anchor's
    again; steps the full window-step list."""
    c0 = anchor_cfg(A, p)
    c1 = anchor_cfg(A, p + 1)
    want = _content(c1, 0)
    tr = replay(tab, c0, tmax)
    T = next((t for (t, q, col, ct) in tr
              if t > 0 and q == c1[0] and col == 0 and ct == want), None)
    if T is None:
        raise QuadError('lap p=%d did not close in %d steps' % (p, tmax))
    # one mark per RECORD: the probe reaches each new extreme for the first
    # time exactly once, so the skeleton is the config at each first arrival
    # at a record column.  [mode] = (side, post): side -1 tracks min-col
    # records (leftward probes), +1 max-col; post=True starts the tracking
    # at the lap's global extreme on the OPPOSITE side -- the machines whose
    # round trips pivot on the DEEP end do their whole ladder after one
    # initial walk-out, so their marks are return-side records after the
    # turn.  Nothing about the tape content is assumed -- machines that
    # RESTORE the probed digits and machines that CONVERT them as they go
    # both fit; the template parse plus exact-time validation catch any
    # non-uniformity.
    side, post = mode
    if side == 0:
        # RESTORE-POINT marks, read straight off the tape instead of off the
        # head's column records.  A column record is only a PROXY for a
        # restore point and it fails on the machines whose excursions
        # DESCEND: those walk out to the deepest digit FIRST and then make
        # shrinking round trips, so every record is set inside the opening
        # walk and the ladder that follows is invisible.  The restore points
        # themselves are exactly what the skeleton wants (the docstring's
        # M(k)): the tape content is the anchor's again, letter for letter.
        return T, [(t, q, col) for (t, q, col, ct) in tr[1:T]
                   if ct == _content(c0, 0)], steps_of(tab, c0, T)
    t0 = 0
    if post:
        cols = [col for (_, _, col, _) in tr[:T + 1]]
        t0 = cols.index(min(cols) if side > 0 else max(cols))
    marks, rec = [], tr[t0][2]
    for (t, q, col, ct) in tr[t0 + 1:T]:
        if (col < rec) if side < 0 else (col > rec):
            rec = col
            marks.append((t, q, col))
    return T, marks, steps_of(tab, c0, T)


def segments(T, marks, steps):
    """(boot, micros, term): the step-lists between consecutive marks."""
    cuts = [0] + [t for (t, _, _) in marks] + [T]
    segs = [steps[cuts[i]:cuts[i + 1]] for i in range(len(cuts) - 1)]
    return segs[0], segs[1:-1], segs[-1]


def _fit_affine(pts):
    """pts = [(k, count-tuple)] -> (slope-tuple, icept-tuple) or None.
    Counts must share one letter pattern; the caller checked that."""
    if len(pts) < 2:
        return None
    (k0, c0), (k1, c1) = pts[0], pts[1]
    if k1 == k0:
        return None
    sl = tuple((b - a) // (k1 - k0) for a, b in zip(c0, c1))
    if any((b - a) % (k1 - k0) for a, b in zip(c0, c1)):
        return None
    ic = tuple(a - s * k0 for a, s in zip(c0, sl))
    for k, c in pts:
        if tuple(s * k + i for s, i in zip(sl, ic)) != c:
            return None
    return sl, ic


def fit_parity(pts):
    """Affine fit, plain first, then per parity class.  Returns
    ('affine', fit) or ('parity', (fit_even, fit_odd)) or raises."""
    f = _fit_affine(pts)
    if f is not None:
        return ('affine', f)
    ev = _fit_affine([(k, c) for k, c in pts if k % 2 == 0])
    od = _fit_affine([(k, c) for k, c in pts if k % 2 == 1])
    if ev is not None and od is not None:
        return ('parity', (ev, od))
    raise QuadError('counts fit no affine law: %r' % (pts,))


def law_cost(classes, k):
    """Step cost of segment k under a per-parity-class law."""
    c = classes[0] if len(classes) == 1 else \
        next(x for x in classes if x['par'] == k % 2)
    i = (k - c['k0']) // c['step']
    return sum(len(b) * (s * i + z)
               for b, s, z in zip(c['blocks'], c['sl'], c['ic']))


def read_law_side(spec, mode, Js=(4, 5, 6, 7, 8, 9), mkey='k'):
    """The whole law: anchor, q_r, stride, boot, micro, and the two
    terminals -- each a (letters, count-law) pair.  Read across several j so
    the j-dependence is measured rather than assumed."""
    r = OV.classify(spec)
    if r.get('overflow') == 'no-anchor':
        raise QuadError('no anchor')

    dspec = mirror_spec(spec) if r.get('mirror') else spec
    tab = parse(dspec)
    A = dict(st0=LAB.index(r['edge']), encf=ENC[r['enc']], tail=r['tail'],
             far=r['far'], enc=r['enc'], mirror=bool(r.get('mirror')),
             dspec=dspec)

    nints, novfs = {}, {}
    micro_segs, term_segs, ovf_segs = {}, {}, {}
    bootint_segs, bootovf_segs = {}, {}
    col0s = {}
    qr, stride = None, None
    for J in Js:
        T, marks, steps = lap_marks(tab, A, interior_p(J), mode)
        To, mo, so = lap_marks(tab, A, overflow_p(J), mode)
        # a leading mark can belong to the BOOT (the landing walks through
        # a record in a different state) -- strip the shortest prefix that
        # leaves the remaining mark states 1- or 2-periodic in BOTH branches
        ok0 = None
        for k0 in (0, 1, 2):
            sq = tuple(q for (_, q, _) in marks[k0:])
            so_ = tuple(q for (_, q, _) in mo[k0:])
            # a 2-cell alphabet puts TWO rungs per digit and some machines
            # three or four; the emitter picks which of them is the ladder's
            # own, so all the reader has to do is find the period
            per = next((n for n in (1, 2, 3, 4)
                        if all(x == sq[i % n] for i, x in enumerate(sq))
                        and all(x == sq[i % n] for i, x in enumerate(so_))),
                       None)
            if per is not None:
                ok0 = (k0, sq[:per])
                break
        if ok0 is None:
            raise QuadError('mark states vary: %r' % (
                tuple(q for (_, q, _) in marks),))
        k0, q0 = ok0
        marks, mo = marks[k0:], mo[k0:]
        if len(marks) < 2 or len(mo) < 2:
            raise QuadError('too few marks on this side')
        if qr is None:
            qr = q0
        elif q0 != qr:
            raise QuadError('mark states moved across j')
        nints[J], novfs[J] = len(marks), len(mo)
        cols = [col for (_, _, col) in marks]
        # the inter-mark strides must be a constant (1- or 2-periodic)
        # pattern; the FIRST column is j-dependent on the deep-pivot
        # machines (the first return record sits near the deep end), so it
        # is recorded as an affine law rather than a constant
        dif = tuple(b - a for a, b in zip(cols, cols[1:]))
        st = dif[:2] if len(dif) >= 2 else dif
        if any(x != st[i % len(st)] for i, x in enumerate(dif)):
            raise QuadError('mark stride varies: %r' % cols)
        if stride is None:
            stride = st
        elif stride != st[:len(stride)] and st != stride[:len(st)]:
            raise QuadError('stride moved across j: %r vs %r' % (st, stride))
        col0s[J] = cols[0]
        # The micro hop is indexed by the PROBE DEPTH when the round trip
        # pivots on the anchor (cost Theta(k)) and by the REMAINING COUNT
        # when it pivots on the deepest unprobed digit (cost Theta(m)).
        # Which one it is is read off the machine: [mkey] picks the keying
        # and the interior/overflow agreement test decides.
        def mk(k, n):
            return k if mkey == 'k' else n - k
        b_, micros, term = segments(T, marks, steps)
        bootint_segs[J] = b_
        for k, m in enumerate(micros, 1):
            if micro_segs.setdefault(mk(k, len(marks)), m) != m:
                raise QuadError('micro %d varies across j' % k)
        term_segs[J] = term
        bo, mio, tmo = segments(To, mo, so)
        bootovf_segs[J] = bo
        for k, m in enumerate(mio, 1):
            if micro_segs.setdefault(mk(k, len(mo)), m) != m:
                raise QuadError('overflow micro %d differs' % k)
        ovf_segs[J] = tmo

    def law_of(segs, what):
        """One template per k-parity class, collapsed to a single class
        when both parities share the template and one affine fit covers
        them.  The Bp cluster alternates LETTERS between parities, not just
        counts, so per-class templates are the general form.  Counts are
        fit affine in the CLASS ORDINAL (k = k0 + step*i), not in k -- on
        a parity class a count that grows by one per class member has
        slope 1/2 in k, which no integer fit expresses."""
        def cls(par, step):
            ks = sorted(k for k in segs if par is None or k % 2 == par)
            if len(ks) < 3:
                raise QuadError('%s: parity class too thin' % what)
            if any(b - a != step for a, b in zip(ks, ks[1:])):
                raise QuadError('%s: class ks not consecutive: %r'
                                % (what, ks))
            kmax = max(ks)
            blocks, _ = rle_fold(segs[kmax])
            pts = []
            for k in ks:
                c = parse_counts(segs[k], blocks)
                if c is None:
                    raise QuadError('%s %d does not parse against the '
                                    'template' % (what, k))
                pts.append(((k - ks[0]) // step, c))
            f = _fit_affine(pts)
            if f is None:
                raise QuadError('%s counts fit no affine law: %r'
                                % (what, pts))
            return dict(par=par, blocks=blocks, k0=ks[0], step=step,
                        sl=f[0], ic=f[1])
        try:
            return [cls(None, 1)]
        except QuadError:
            return [cls(0, 2), cls(1, 2)]

    def count_law(d, what):
        f = _fit_affine([(J, (d[J],)) for J in Js])
        if f is None:
            raise QuadError('%s mark counts fit no affine law: %r'
                            % (what, d))
        return (f[0][0], f[1][0])

    return dict(spec=spec, anchor=A, qr=qr, stride=stride,
                mode=mode, mkey=mkey,
                nint=count_law(nints, 'interior'),
                col0=count_law(col0s, 'first column'),
                novf=count_law(novfs, 'overflow'),
                bootint=law_of(bootint_segs, 'boot-int'),
                bootovf=law_of(bootovf_segs, 'boot-ovf'),
                micro=law_of(micro_segs, 'micro'),
                term=law_of(term_segs, 'term'),
                ovf=law_of(ovf_segs, 'ovf-term'))


def read_skeletons(spec, Js=(5, 6, 7)):
    """EVERY viable ladder skeleton, in mode order: (anchor, mode, rung states, mark counts).

    [read_law] additionally fits the boot/micro/terminal step patterns as
    affine laws, and that fit fails whenever the rungs cycle through more
    than two states -- the segment between two consecutive marks then
    depends on the rung's residue, and no single template covers it.  The
    EMITTER does not need those fits: it re-derives every chain from the
    measured configurations and validates them against the raw simulator.
    So it asks for the skeleton, which is the part the law reader gets right
    on every machine in the bucket.  The mode order and the leading-mark
    strip are [read_law_side]'s, so a machine both readers accept is read
    the same way by both."""
    r = OV.classify(spec)
    if r.get('overflow') == 'no-anchor':
        raise QuadError('no anchor')
    dspec = mirror_spec(spec) if r.get('mirror') else spec
    tab = parse(dspec)
    A = dict(st0=LAB.index(r['edge']), encf=ENC[r['enc']], tail=r['tail'],
             far=r['far'], enc=r['enc'], mirror=bool(r.get('mirror')),
             dspec=dspec)
    errs, out = [], []
    for mode in ((-1, False), (0, False), (1, True), (1, False), (-1, True)):
        try:
            qr, nints, novfs = None, {}, {}
            for J in Js:
                _, marks, _ = lap_marks(tab, A, interior_p(J), mode)
                _, mo, _ = lap_marks(tab, A, overflow_p(J), mode)
                ok0 = None
                for k0 in (0, 1, 2):
                    sq = tuple(q for (_, q, _) in marks[k0:])
                    so_ = tuple(q for (_, q, _) in mo[k0:])
                    per = next((n for n in (1, 2, 3, 4)
                                if sq and all(x == sq[i % n]
                                              for i, x in enumerate(sq))
                                and all(x == sq[i % n]
                                        for i, x in enumerate(so_))), None)
                    if per is not None:
                        ok0 = (k0, sq[:per])
                        break
                if ok0 is None:
                    raise QuadError('mark states vary')
                k0, q0 = ok0
                if qr is None:
                    qr = q0
                elif q0 != qr:
                    raise QuadError('mark states moved across j')
                nints[J], novfs[J] = len(marks) - k0, len(mo) - k0
            f = _fit_affine([(J, (nints[J],)) for J in Js])
            g = _fit_affine([(J, (novfs[J],)) for J in Js])
            if f is None or g is None:
                raise QuadError('mark counts fit no affine law')
            out.append(dict(spec=spec, anchor=A, qr=qr, mode=mode,
                            nint=(f[0][0], f[1][0]),
                            novf=(g[0][0], g[1][0])))
        except QuadError as e:
            errs.append('%r: %s' % (mode, e))
    if not out:
        raise QuadError(' // '.join(errs))
    return out


def read_law(spec, Js=(4, 5, 6, 7, 8, 9)):
    """Try the four skeletons in order: anchor-pivot probes leftward, then
    the deep-pivot ladders (records on the return side after the turn),
    then the rightward mirrors.  The first mode whose law closes wins; the
    error reported is the first mode's."""
    errs = []
    for mode in ((-1, False), (0, False), (1, True), (1, False), (-1, True)):
        for mkey in ('k', 'm'):
            try:
                return read_law_side(spec, mode, Js, mkey)
            except QuadError as e:
                errs.append('%r/%s: %s' % (mode, mkey, e))
    raise QuadError(' // '.join(errs))


# ------------------------------------------------------------ the validator ---

def predict(law, j, ovf):
    """(restore times, total) for the lap at carry j, from the law alone."""
    t = law_cost(law['bootovf'] if ovf else law['bootint'], j)
    times = []
    a, b = law['novf'] if ovf else law['nint']
    nm = a * j + b
    for k in range(1, nm):
        times.append(t)
        t += law_cost(law['micro'], k if law.get('mkey', 'k') == 'k'
                      else nm - k)
    times.append(t)
    t += law_cost(law['ovf'] if ovf else law['term'], j)
    return times, t


def validate(law, jlo=2, jhi=11, jconc=4):
    """Replay every lap at j = jlo..jhi, both branches, and check the
    predicted restore times, the total time and the successor tape EXACTLY.

    The smallest indices may be genuinely irregular -- degenerate ladders,
    exactly like the offset route's concrete j = 0 device -- so failures at
    j < [jconc] raise the reported floor instead of failing the gate: a
    small-j lap is one vm_compute in the board.  The floor is recorded in
    the verdict; a failure at or above [jconc] fails."""
    A = law['anchor']
    tab = parse(A['dspec'])
    floor = jlo
    for j in range(jlo, jhi + 1):
        for ovf in (False, True):
            p = overflow_p(j) if ovf else interior_p(j)
            T, marks, _ = lap_marks(tab, A, p, law['mode'])
            nb = law_cost(law['bootovf'] if ovf else law['bootint'], j)
            marks = [m for m in marks if m[0] >= nb]
            times, tot = predict(law, j, ovf)
            got = [t for (t, _, _) in marks]
            bad = None
            if got != times:
                bad = ('j=%d %s: restore times %r want %r'
                       % (j, 'ovf' if ovf else 'int', got, times))
            elif T != tot:
                bad = ('j=%d %s: T=%d want %d'
                       % (j, 'ovf' if ovf else 'int', T, tot))
            if bad:
                if j < jconc:
                    floor = j + 1
                    break
                raise QuadError(bad)
    law['jmin'] = floor
    return ('quad: validated j=%d..%d, interior+overflow, exact times'
            % (floor, jhi)) + \
        ('' if floor == jlo else ' (j<%d concrete)' % floor)


# ----------------------------------------------------------------- drivers ---

def show_law(law):
    A = law['anchor']
    print('%s  mir=%s enc=%s@%s tail=%r far=%r' %
          (law['spec'], A['mirror'], A['enc'], LAB[A['st0']], A['tail'],
           A['far']))
    print('  q_r=%s stride=%r mode=%r  marks %r int / %r ovf (a*j+b)'
          % ('/'.join(LAB[q] for q in law['qr']), law['stride'], law['mode'],
             law['nint'], law['novf']))

    def blk(name, classes):
        for c in classes:
            print('  %-5s%s letters=%s  k0=%d step=%d slopes=%r icepts=%r' %
                  (name,
                   '' if c['par'] is None else '[par%d]' % c['par'],
                   '|'.join(''.join('%s%d%s%d' % (LAB[q], h, 'LR'[mv > 0], w)
                                    for (q, h, w, mv) in b)
                            for b in c['blocks']),
                   c['k0'], c['step'], c['sl'], c['ic']))
    blk('bootI', law['bootint'])
    blk('bootO', law['bootovf'])
    blk('micro', law['micro'])
    blk('term', law['term'])
    blk('ovf', law['ovf'])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--law')
    ap.add_argument('--gate', action='store_true')
    ap.add_argument('--list')
    ap.add_argument('-J', type=int, default=5)
    a = ap.parse_args()

    if a.law:
        law = read_law(a.law)
        show_law(law)
        print('  ' + validate(law))
        return

    if a.gate:
        if a.list:
            specs = [l.split()[0] for l in open(a.list) if l.strip()]
        else:
            tsv = os.path.join(REPO, 'tools/closeout/residue_map.tsv')
            unp = os.path.join(REPO, 'tools/closeout/frozen_unproven.txt')
            left = {l.strip() for l in open(unp) if l.strip()}
            specs = [l.split('\t')[0] for l in open(tsv)
                     if l.split('\t')[0] in left
                     and '\tQUAD\tQUAD\t' in l]
        nok = 0
        import collections
        tot = collections.Counter()
        for i, spec in enumerate(specs):
            try:
                law = read_law(spec)
                v = validate(law)
            except Exception as e:                             # noqa: BLE001
                msg = str(e)[:80]
                print('%3d/%d %-40s %s' % (i + 1, len(specs), spec, msg),
                      flush=True)
                tot[str(e)[:40]] += 1
                continue
            ncl = (len(law['micro']), len(law['term']), len(law['ovf']))
            print('%3d/%d %-40s GATED %s mode=%r classes=%r jmin=%d'
                  % (i + 1, len(specs), spec, law['anchor']['enc'],
                     law['mode'], ncl, law['jmin']), flush=True)
            nok += 1
            tot['GATED'] += 1
        print('%d / %d gated' % (nok, len(specs)))
        print(tot)
        return

    ap.error('one of --law / --gate is required')


if __name__ == '__main__':
    main()
