#!/usr/bin/env python3
"""UNTRUSTED probe: do the CLASS ARMS derive for the rows the closure REFUSES?

LADDER_PLAN 4k's guard, and 4l's closing instruction: before building the
theorem that consumes the arms, run the arm builder over the rows and COUNT.
`emit_ladder.closure_data` refuses `code = gray` at its first line, a step
other than 1 at its second and a two-phase family at its third.  This relaxes
exactly those three refusals -- in a PROBE, not in the emitter -- and reports,
per row, whether every class arm it would need has a chain.

Three things are generalised here relative to `closure_data`, and each is a
shape the kernel's own definitions already carry:

  * the interior class may have a FIXED WORD before the run ([cs_u]).  The
    `(Binary, 1)` classes have none, so `LadderCheck.cls_side` does not carry
    one; three of `(Gray, 2)`'s four do.
  * the TOP of a width need not be the all-max run.  For a reflected code it
    is `0^(k-1) ++ [1]`, so the fill arm's left-hand side is a run with a
    fixed word after it -- which is `run_side`'s `w2`, already there.
  * the terminator is read at the fill's OWN phase and its target at the
    phase the fill lands in.  Interior arms never see a terminator at all
    (it is inside the opaque tail), so they are phase-independent.

The classes are NOT assumed.  They are fitted from the family's own successor
by enumerating the orbit, and a fit is reported only if every class law holds
on every string it matches AND the classes together cover every interior
string the orbit reached.  A row whose classes do not fit is reported as
`no class fit` and is NOT counted as an arm failure -- they are different
answers and 4g's lesson is that collapsing them is how a search's label
becomes a property of the machine.

`--selftest` runs the whole probe over a row that is already boarded and
checks it recovers the classes and arms the emitter built -- the discipline
`bounce.py --selftest` exists for: a probe whose miss you intend to report
needs a known-positive case.

Usage:  armprobe.py SWEEP.jsonl [--rows FILE] [--spec SPEC] [--out OUT.json]
        armprobe.py SWEEP.jsonl --selftest
"""
import argparse
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'counters'))

from ladderarm import parse_tm                                       # noqa: E402
from emit_ladder import ARM_GRID, blk, _splits                       # noqa: E402
from valfam import gray_decode, gray_encode                          # noqa: E402
import lapcert as LC                                                 # noqa: E402


class NoFit(Exception):
    pass


# ------------------------------------------------------------- the family --

class Fam:
    """The family, read out of the certificate JSON.  `value`/`of_value` are
    `valfam.Fam`'s, transcribed onto the JSON rather than the walk, so the
    probe reads the same numeration the prover certified."""

    def __init__(self, cert):
        f = cert['family']
        self.spec = cert['spec']
        self.b = f['base']
        self.code = f.get('code', 'binary')
        self.step = f.get('value_step_per_anchor_visit', 1)
        self.digs = [tuple(w) for w in f['digits']]
        self.pre = tuple(f['near_head_prefix'])
        self.tails = [tuple(t) for t in
                      (f.get('terminators_by_phase') or [f['terminator']])]
        self.q = ord(f['state']) - 65
        self.hs = f['head']
        self.left = f['side'] == 'L'
        self.other = tuple(f['other_side_cells'])
        self.weights = f.get('weights')
        self.fills = cert.get('fill_by_phase') or [cert['fill']]
        self.boot = cert['boot']

    # -- the numeration -----------------------------------------------------

    def value(self, ds):
        if self.weights is not None:
            if len(ds) > len(self.weights):
                return None
            return sum(d * self.weights[i] for i, d in enumerate(ds))
        xs = gray_decode(list(ds), self.b) if self.code == 'gray' else list(ds)
        v = 0
        for d in reversed(xs):
            v = v * self.b + d
        return v

    def of_value(self, v, k):
        ns, x = [], v
        for _ in range(k):
            ns.append(x % self.b)
            x //= self.b
        if x:
            return None
        return gray_encode(ns, self.b) if self.code == 'gray' else ns

    def maxval(self, k):
        """The largest value width `k` can spell.

        For a WEIGHTED numeration that is not `b^k - 1`: the digits are
        weighted by `fm_weights` and not by `b^i`, so the top of a width is
        the sum of the weights it covers.  With `b^k - 1` here a Fibonacci
        row's `is_top` is false at every string it ever stands on, `next_ds`
        asks `of_value` for a positional string the counter never spells, and
        the orbit walks off the family after five steps."""
        if self.weights is not None:
            if k > len(self.weights):
                return None
            return sum((self.b - 1) * w for w in self.weights[:k])
        return self.b ** k - 1

    def fill(self, ph):
        return self.fills[ph] if ph < len(self.fills) else self.fills[0]

    def fill_target(self, ph, k):
        """The fill law's target digit string, leaving width `k` in phase
        `ph`.  `Fill.apply`, on the JSON."""
        f = self.fill(ph)
        pre, suf = list(f['target_prefix']), list(f['target_suffix'])
        n = k + f['widens_by'] - len(pre) - len(suf)
        if n < 0:
            return None
        return pre + [f['target_fill_digit']] * n + suf

    def is_top(self, ds):
        v = self.value(ds)
        mx = self.maxval(len(ds))
        return v is None or mx is None or v + self.step > mx

    def next_ds(self, ds, ph):
        if self.is_top(ds):
            return self.fill_target(ph, len(ds)), self.fill(ph)['lands_in_phase']
        return self.of_value(self.value(ds) + self.step, len(ds)), ph

    def top(self, k):
        """The width-k string the fill leaves from -- NOT the all-max string
        for a reflected code."""
        return self.of_value(self.maxval(k), k)

    # -- cells --------------------------------------------------------------

    def cells(self, ds):
        out = []
        for d in ds:
            out.extend(self.digs[d])
        return tuple(out)

    def conf(self, sd):
        other = (self.other, (), 0, 0, ())
        return (self.q, sd, self.hs, other) if self.left else \
               (self.q, other, self.hs, sd)

    def boot_conf(self, tab):
        """The anchor's cconf, by simulating `CTape.ctape_move` from the blank
        tape to the boot index.  This is the ONE place the far side can be
        read exactly.

        It matters because `RuleSound` is an equation on `cconf` and
        `ctape_move` does not normalise: a blank the head materialises by
        stepping back over it is `S0 :: r` and not `r`.  `valfam` reads the far
        side through `block_rle` off a run-length view that has already dropped
        a trailing blank run, so `other_side_cells` can be short by exactly
        those cells -- the same TAPE under `lift` (which is why the boot
        premise, stated on `lift`, does not notice), and a different `cconf`,
        which is what every arm is stated on."""
        l, h, r, q = [], 0, [], 0
        for _ in range(self.boot['steps_from_blank']):
            e = tab.get((q, h))
            if e is None:
                return None
            w, d, q2 = e
            if d > 0:
                l, h, r = [w] + l, (r[0] if r else 0), r[1:]
            else:
                r, h, l = [w] + r, (l[0] if l else 0), l[1:]
            q = q2
        return q, tuple(l), h, tuple(r)

    def parse_counter(self, ctr):
        """`(digit string, phase)` for a counter side, or None.

        The inverse of `fam_cells`: the near-head prefix, then digit words,
        then the terminator of SOME phase, then blanks.  A digit word can be
        a prefix of a terminator, so the terminator is taken only where the
        rest of the side is blank -- which is what makes the parse unique."""
        if tuple(ctr[:len(self.pre)]) != tuple(self.pre):
            return None
        body, ds, j = tuple(ctr[len(self.pre):]), [], 0
        while True:
            for ph, tl in enumerate(self.tails):
                if body[j:j + len(tl)] == tuple(tl) and \
                   all(c == 0 for c in body[j + len(tl):]):
                    return tuple(ds), ph
            hit = None
            for di, dw in enumerate(self.digs):
                if body[j:j + len(dw)] == tuple(dw):
                    hit = (di, len(dw))
                    break
            if hit is None or j >= len(body):
                return None
            ds.append(hit[0])
            j += hit[1]

    def walk(self, tab, nsteps, kmax):
        """The `(digit string, phase)` the counter stands on at every ANCHOR
        visit, read off the machine's own tape.

        This is the orbit `of_value` cannot compute.  `of_value` is positional
        -- `v % b` down the widths -- and a weighted numeration is not: the
        Fibonacci rows spell 2, 3, 5, 8, 13, 21 members at widths 1..6 and the
        positional inverse names strings that are not members of any of them.
        Read off the machine there is nothing to invert."""
        l, h, r, q, out = [], 0, [], 0, []
        for _ in range(nsteps):
            if (q, h) == (self.q, self.hs):
                got = self.parse_counter(tuple(l) if self.left else tuple(r))
                if got is not None and len(got[0]) <= kmax:
                    out.append(got)
            e = tab.get((q, h))
            if e is None:
                break
            w, d, q2 = e
            if d > 0:
                l, h, r = [w] + l, (r[0] if r else 0), r[1:]
            else:
                r, h, l = [w] + r, (l[0] if l else 0), l[1:]
            q = q2
        return out

    def read_other(self, tab):
        """The far sides to try for `fm_other`: the certificate's, and the one
        the machine actually spells at the anchor.

        Both are the same TAPE and they are different `cconf`s, and which one
        an arm needs is not a choice -- it is whether the head materialises
        that blank inside the arm's own run.  So the probe tries both and says
        which it used.  The counter side is checked the same way and is NOT
        overridden: the fill arm is stated on the family's spelling, because
        that is what `fam_cells` produces and what the lap equation is on."""
        bc = self.boot_conf(tab)
        if bc is None:
            raise NoFit('the boot index halts')
        q, l, h, r = bc
        if (q, h) != (self.q, self.hs):
            raise NoFit('the boot index is not the anchor (%s%d, not %s%d)'
                        % (chr(65 + q), h, chr(65 + self.q), self.hs))
        ctr, far = (l, r) if self.left else (r, l)
        want = self.pre + self.cells(self.boot['digits_lsb_first']) \
            + self.tails[self.boot.get('phase', 0)]
        n = min(len(ctr), len(want))
        if ctr[:n] != want[:n] or any(c != 0 for c in ctr[n:] + want[n:]):
            raise NoFit('the boot counter side is %r, the family spells %r '
                        'and they differ by more than trailing blanks'
                        % (ctr, want))
        n = min(len(far), len(self.other))
        if far[:n] != self.other[:n] or any(c != 0 for c in far[n:]
                                            + self.other[n:]):
            raise NoFit('the boot far side is %r, the family carries %r and '
                        'they differ by more than trailing blanks'
                        % (far, self.other))
        out = [self.other]
        if far != self.other:
            out.append(far)
        return out


def orbit_machine(F, tab, kmax=11, nsteps=400000):
    """The orbit and its interior successors, read off the MACHINE.

    Used where `of_value` cannot serve: a weighted numeration is not
    positional, so the successor of a member cannot be computed by dividing
    down the base.  `value` IS trustworthy there -- it is the weighted sum --
    so the members of a width are collected from the walk and ordered by
    value, and the successor of a member is the next member of its width.
    That is the same relation `fam_succ` denotes and it is read, not guessed.
    """
    vis = F.walk(tab, nsteps, kmax)
    if not vis:
        raise NoFit('the machine reaches no parseable anchor visit')
    byk = {}
    for ds, ph in vis:
        byk.setdefault((len(ds), ph), {})[ds] = F.value(ds)
    orb, pairs = [], []
    for (k, ph), mem in sorted(byk.items()):
        if any(v is None for v in mem.values()):
            raise NoFit('width %d spells a string with no value' % k)
        order = sorted(mem, key=lambda ds: mem[ds])
        if len(set(mem.values())) != len(order):
            raise NoFit('width %d spells two members with the same value' % k)
        for i, ds in enumerate(order):
            orb.append((ds, ph))
            if i + 1 < len(order):
                pairs.append((ds, order[i + 1]))
    return orb, pairs


def orbit(F, kmax=11):
    """Every (digit string, phase) the counter reaches from the boot, out to
    width `kmax`.  The membership question a step > 1 raises (4g: only part of
    each width is a member) is answered by the machine and not by a predicate
    guessed here."""
    ds = list(F.boot['digits_lsb_first'])
    ph, seen, out = F.boot.get('phase', 0), set(), []
    for _ in range(200000):
        if len(ds) > kmax:
            break
        k = (tuple(ds), ph)
        if k in seen:
            break
        seen.add(k)
        out.append((tuple(ds), ph))
        nd, nph = F.next_ds(ds, ph)
        if nd is None:
            break
        ds, ph = list(nd), nph
    return out


# ---------------------------------------------------------- class fitting --

def _matches(ds, u, t, w):
    """Every n with ds = u ++ t^n ++ w ++ rest."""
    lu, lw = len(u), len(w)
    if tuple(ds[:lu]) != tuple(u):
        return
    for n in range(0, len(ds) - lu - lw + 1):
        if any(x != t for x in ds[lu:lu + n]):
            return
        if tuple(ds[lu + n:lu + n + lw]) == tuple(w):
            yield n


def _fit_one(pairs, u, t, w):
    """(u', t', w') for the class (u, t, w), or None if the data contradict
    it.  Every match at every n has to agree, and the tail beyond the class
    has to be carried across untouched -- that is what makes it a class."""
    lu, lw = len(u), len(w)
    up = tp = wp = None
    hits = 0
    for ds, nx in pairs:
        for n in _matches(ds, u, t, w):
            hits += 1
            if tuple(nx[lu + n + lw:]) != tuple(ds[lu + n + lw:]):
                return None
            cu = tuple(nx[:lu])
            cw = tuple(nx[lu + n:lu + n + lw])
            run = nx[lu:lu + n]
            ct = None
            if n:
                if len(set(run)) != 1:
                    return None
                ct = run[0]
            if up is None:
                up, wp = cu, cw
            elif (up, wp) != (cu, cw):
                return None
            if ct is not None:
                if tp is None:
                    tp = ct
                elif tp != ct:
                    return None
    if not hits or up is None:
        return None
    return (up, t if tp is None else tp, wp)


def fit_classes(F, pairs, maxu=3, maxw=3):
    """A set of classes of `LadderCheck.Class`'s shape covering every interior
    successor in `pairs`.  Greedy, cheapest (shortest fixed words) first."""
    if not pairs:
        raise NoFit('no interior successors in the orbit')
    cands = []
    seen = set()
    for lu in range(0, maxu + 1):
        for lw in range(0, maxw + 1):
            for ds, _ in pairs:
                if len(ds) < lu + lw:
                    continue
                u = tuple(ds[:lu])
                for t in range(F.b):
                    # the fixed word after the run is read off the data at
                    # every position the run could end
                    for n in range(0, len(ds) - lu - lw + 1):
                        if any(x != t for x in ds[lu:lu + n]):
                            break
                        w = tuple(ds[lu + n:lu + n + lw])
                        key = (u, t, w)
                        if key in seen:
                            continue
                        seen.add(key)
                        got = _fit_one(pairs, u, t, w)
                        if got is not None:
                            cands.append((u, t, w) + got)
    if not cands:
        raise NoFit('no class of the record shape fits any successor')

    def covered(c):
        u, t, w = c[0], c[1], c[2]
        out = set()
        for i, (ds, nx) in enumerate(pairs):
            for _ in _matches(ds, u, t, w):
                out.add(i)
                break
        return out

    cands.sort(key=lambda c: (len(c[0]) + len(c[2]), len(c[0]), c[1]))
    cov = {c: covered(c) for c in cands}
    need = set(range(len(pairs)))
    chosen = []
    while need:
        best = max(cands, key=lambda c: (len(cov[c] & need),
                                         -len(c[0]) - len(c[2])))
        if not (cov[best] & need):
            raise NoFit('%d of %d interior successors are in no class'
                        % (len(need), len(pairs)))
        chosen.append(best)
        need -= cov[best]
        cands = [c for c in cands if c is not best]
        if len(chosen) > 12:
            raise NoFit('more than 12 classes')
    return chosen


def fit_top_shape(tops):
    """The top of a width as `w1 ++ t^n ++ w2`, fitted over the tops the ORBIT
    actually reaches.

    Read, not computed.  The top of a width is the last string the fill leaves
    from, and with a step other than 1 that is the largest MEMBER of the width
    and not the largest value it can spell: at `(Gray, 2)` the value `b^k - 1`
    is odd and therefore not a member at all, and its string
    `[] ++ 0^(k-1) ++ [1]` is a shape the counter never stands on.  The real
    one is `[1] ++ 0^(k-2) ++ [1]`, and an arm built on the other has no chain
    for the good reason that the machine is never in that configuration."""
    tops = sorted(tops.items())
    if len(tops) < 3:
        raise NoFit('fewer than three tops in the orbit')
    a = tops[-1][1]
    for lw1 in range(0, 3):
        for lw2 in range(0, 3):
            w1, w2 = tuple(a[:lw1]), tuple(a[len(a) - lw2:] if lw2 else ())
            mid = a[lw1:len(a) - lw2] if lw2 else a[lw1:]
            if not mid or len(set(mid)) != 1:
                continue
            t = mid[0]
            if all(tuple(top) == tuple(w1) + (t,) * (k - lw1 - lw2) + tuple(w2)
                   for k, top in tops):
                return w1, t, w2
    raise NoFit('the top of a width is not a run with fixed words either side')


# ------------------------------------------------------------- the arms ----

def derive(tab, el, er, c0, c1, what, md=32, nm=120):
    ch = LC.derive_chain(tab, el, er, c0, c1, maxdepth=md, nmax=nm, lift=True)
    if ch is None:
        raise NoFit('%s: no chain' % what)
    got = LC.srun(tab, el, er, ch, c0)
    if got is None or got[0] != c1:
        raise NoFit('%s: chain lands off the rhs' % what)
    if got[2] == 0:
        raise NoFit('%s: zero-step rule' % what)
    return ch, got[1], got[2]


def interior_arms(F, tab, cls, n0, stride):
    """One arm per class per ARM INDEX, exactly `closure_data`'s scheme with
    the class's fixed word `u` in front of the run."""
    el, er = (not F.left), F.left
    got = []
    for ci, (u, t, w, u2, t2, w2) in enumerate(cls):
        for r in range(n0 + stride):
            s = 0 if r < n0 else stride
            c0 = F.conf(blk(F.pre + F.cells(u) + F.digs[t] * r,
                            F.digs[t], s, F.cells(w)))
            c1 = F.conf(blk(F.pre + F.cells(u2) + F.digs[t2] * r,
                            F.digs[t2], s, F.cells(w2)))
            if c0 == c1:
                raise NoFit('interior class %d r=%d: lhs = rhs' % (ci, r))
            ch, ca, cb = derive(tab, el, er, c0, c1,
                                'interior class %d r=%d' % (ci, r))
            got.append((ci, r, s, c0, c1, ch, ca, cb))
    return got


def fill_arms(F, tab, tops, n0, stride, kmin=1):
    """The fill arm at each index and each PHASE.  Its left-hand side is the
    top of the width -- a run with a fixed word either side, not necessarily
    the all-max string -- and its right-hand side is the phase's fill target
    at the phase the fill lands in."""
    got = []
    for ph in range(len(F.tails)):
        if ph not in tops:
            raise NoFit('phase %d has no top in the orbit' % ph)
        w1, t, w2 = tops[ph]
        f = F.fill(ph)
        to = f['lands_in_phase']
        fpre, fsuf = list(f['target_prefix']), list(f['target_suffix'])
        mid = f['target_fill_digit']
        mf = len(fpre) + len(fsuf)
        for r in range(1, n0 + stride):
            s = 0 if r < n0 else stride
            run = r - len(w1) - len(w2)
            total = r + f['widens_by'] - mf
            if s == 0 and r < kmin:
                continue        # a FLAT arm at a width the counter never has
            if run < 0 or total < 0:
                raise NoFit('fill ph=%d r=%d: width %d cannot be spelled'
                            % (ph, r, r))
            hit = None
            why = None
            for m1 in _splits(run):
                lhs = F.conf(blk(F.pre + F.cells(w1) + F.digs[t] * m1,
                                 F.digs[t], s,
                                 F.digs[t] * (run - m1) + F.cells(w2)
                                 + F.tails[ph]))
                for m2 in _splits(total):
                    rhs = F.conf(blk(F.pre + F.cells(fpre) + F.digs[mid] * m2,
                                     F.digs[mid], s,
                                     F.digs[mid] * (total - m2)
                                     + F.cells(fsuf) + F.tails[to]))
                    if lhs == rhs:
                        continue
                    try:
                        ch, ca, cb = derive(tab, True, True, lhs, rhs,
                                            'fill ph=%d r=%d' % (ph, r))
                    except NoFit as e:
                        why = str(e)
                        continue
                    hit = (ph, r, s, m1, m2, lhs, rhs, ch, ca, cb)
                    break
                if hit:
                    break
            if hit is None:
                raise NoFit('fill ph=%d r=%d: no chain at any copy split (%s)'
                            % (ph, r, why))
            got.append(hit)
    return got


def probe(cert, kmax=11, grid=None, verbose=False):
    """The whole question, for one row: do the class arms exist?"""
    F = Fam(cert)
    tab = parse_tm(cert['spec'])
    out = {'spec': cert['spec'], 'code': F.code, 'step': F.step,
           'phases': len(F.fills), 'b': F.b,
           'digit_len': len(F.digs[0]) if F.digs else 0}
    try:
        fars = F.read_other(tab)
    except NoFit as e:
        out['stop'] = 'boot: %s' % e
        return out
    out['other_cert'] = list(F.other)
    out['other_tried'] = [list(x) for x in fars]
    if F.weights is not None:
        # a weighted numeration has no positional inverse; read it off the
        # machine rather than off `of_value` (which names non-members)
        # the certificate carries finitely many weights, and a width past the
        # last one has no value -- read out to the widths it does cover
        kw = min(kmax, len(F.weights))
        out['kmax_used'] = kw
        try:
            orb, pairs = orbit_machine(F, tab, kw)
        except NoFit as e:
            out['stop'] = 'orbit: %s' % e
            return out
        out['orbit_read'] = 'machine'
    else:
        orb = orbit(F, kmax)
        pairs, seenp = [], set()
        for ds, ph in orb:
            if F.is_top(ds):
                continue
            nx, _ = F.next_ds(list(ds), ph)
            if nx is None or len(nx) != len(ds):
                continue
            if ds in seenp:
                continue
            seenp.add(ds)
            pairs.append((tuple(ds), tuple(nx)))
        out['orbit_read'] = 'of_value'
    out['orbit'] = len(orb)
    out['interior_strings'] = len(pairs)
    try:
        cls = fit_classes(F, pairs)
    except NoFit as e:
        out['classes'] = None
        out['stop'] = 'no class fit: %s' % e
        return out
    out['classes'] = [{'u': list(c[0]), 't': c[1], 'w': list(c[2]),
                       'u2': list(c[3]), 't2': c[4], 'w2': list(c[5])}
                      for c in cls]
    seen_tops = {}
    for ds, ph in orb:
        if F.is_top(ds):
            seen_tops.setdefault(ph, {})[len(ds)] = ds
    tops = {}
    try:
        for ph in range(len(F.tails)):
            tops[ph] = fit_top_shape(seen_tops.get(ph, {}))
    except NoFit as e:
        out['stop'] = 'no top shape: %s' % e
        return out
    out['top_shape'] = {str(ph): {'w1': list(t[0]), 't': t[1],
                                  'w2': list(t[2])}
                        for ph, t in tops.items()}

    kmin = min(len(ds) for ds, _ in orb) if orb else 1
    t0 = time.time()
    best = None
    for far in fars:
        F.other = far
        got = {'other': list(far), 'ifail': [], 'ffail': []}
        for n0, st in (grid or ARM_GRID):
            try:
                arms = interior_arms(F, tab, cls, n0, st)
            except NoFit as e:
                got['ifail'].append('N0=%d st=%d: %s' % (n0, st, e))
                continue
            got['interior'] = {'N0': n0, 'st': st, 'arms': len(arms)}
            break
        for n0, st in (grid or ARM_GRID):
            if n0 < 1 or n0 + st < 2:
                continue
            try:
                arms = fill_arms(F, tab, tops, n0, st, kmin)
            except NoFit as e:
                got['ffail'].append('N0=%d st=%d: %s' % (n0, st, e))
                continue
            got['fill'] = {'N0': n0, 'st': st, 'arms': len(arms)}
            break
        score = ('interior' in got) + ('fill' in got)
        if best is None or score > best[0]:
            best = (score, got)
        if score == 2:
            break
    score, got = best
    out['other_used'] = got['other']
    out['seconds'] = round(time.time() - t0, 1)
    if 'interior' in got:
        out['interior'] = got['interior']
    if 'fill' in got:
        out['fill'] = got['fill']
    if score == 2:
        out['both_arms'] = True
        return out
    which = 'interior' if 'interior' not in got else 'fill'
    fails = got['ifail'] if which == 'interior' else got['ffail']
    out['stop'] = '%s arm: %s' % (which, fails[-1] if fails else '?')
    out['grid_failures'] = fails
    return out


SELFTEST = '1RB1LA_0LA0RC_0LD0RB_1LD1RC'


def selftest(rows):
    """A known-positive case: the first row 4i boarded.  The probe has to
    recover the `(Binary, 1)` classes -- one per digit below the top, no fixed
    word before the run -- and both arms.  A probe whose miss you intend to
    report needs one of these (`bounce.py --selftest`)."""
    cert = rows.get(SELFTEST)
    if cert is None:
        print('selftest: %s not in the sweep' % SELFTEST)
        return 1
    r = probe(cert)
    ok = True
    if not r.get('both_arms'):
        print('selftest FAILED: %s' % r.get('stop'))
        ok = False
    want = [{'u': [], 't': 1, 'w': [0], 'u2': [], 't2': 0, 'w2': [1]}]
    if r.get('classes') != want:
        print('selftest FAILED: classes %s, wanted %s' % (r.get('classes'), want))
        ok = False
    if r.get('top_shape') != {'0': {'w1': [], 't': 1, 'w2': []}}:
        print('selftest FAILED: top shape %s' % r.get('top_shape'))
        ok = False
    print('selftest %s: %s' % ('OK' if ok else 'FAILED', json.dumps(r)))
    return 0 if ok else 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('sweep')
    ap.add_argument('--rows')
    ap.add_argument('--spec', action='append')
    ap.add_argument('--out')
    ap.add_argument('--kmax', type=int, default=11)
    ap.add_argument('--selftest', action='store_true')
    a = ap.parse_args()

    rows = {}
    for l in open(a.sweep):
        if l.strip():
            o = json.loads(l)
            rows[o['spec']] = o
    if a.selftest:
        return selftest(rows)

    want = list(a.spec or [])
    if a.rows:
        want += [l.strip() for l in open(a.rows) if l.strip()]
    if not want:
        want = sorted(rows)

    out = []
    for spec in want:
        cert = rows.get(spec)
        if cert is None or not cert.get('closed'):
            print('%-33s SKIP (not a closed row of this sweep)' % spec)
            continue
        r = probe(cert, kmax=a.kmax)
        out.append(r)
        if r.get('both_arms'):
            print('%-33s BOTH ARMS  %d classes, interior N0=%d st=%d (%d arms),'
                  ' fill N0=%d st=%d (%d arms)  %.0fs'
                  % (spec, len(r['classes']), r['interior']['N0'],
                     r['interior']['st'], r['interior']['arms'],
                     r['fill']['N0'], r['fill']['st'], r['fill']['arms'],
                     r.get('seconds', 0)))
        else:
            print('%-33s STOP  %s  %.0fs'
                  % (spec, r.get('stop'), r.get('seconds', 0)))
    if a.out:
        with open(a.out, 'w') as fh:
            for r in out:
                fh.write(json.dumps(r) + '\n')
    n = sum(1 for r in out if r.get('both_arms'))
    print('\n%d of %d rows have both class arms' % (n, len(out)))
    return 0


if __name__ == '__main__':
    sys.exit(main())
