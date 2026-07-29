#!/usr/bin/env python3
"""UNTRUSTED diagnostic: WHY the interior chain search fails.

`no interior chain` is the residue's second-largest label, and it is the one
nickdrozd read off the published residue map and called solvable.  He is
right, and this file says why: the label is THREE different gaps wearing one
name, and none of them is about the machine.

For each row it takes the anchor family `emit_lapcert.anchors` already finds,
builds the interior branch's three framings (one-chain, and the SPLIT's
`j = 0` and `j = S j'`), closes the symbolic reachable set under the step
language, and reports which of these is true:

  lift        the chain EXISTS up to trailing blanks -- `derive` never tries
              it, because it only ever derives the SPLIT chains EXACTLY
              (`derive_chain(Z0, Z1)` / `(P0, P1)` with no `lift=True`), and
              the `lift` last resort is wired for the ONE-chain mode only.
              Wiring split x lift is a template combination, not new theory.

  cycR-gap    the search dead-ends at a state whose RIGHT side still carries
              the repeated block and whose LEFT prefix is NON-EMPTY.  That is
              a MISSING PRIMITIVE, and it is the mirror of one that exists:
              [WTape.cycL] deposits past a concrete right window (`rw`, which
              is `SCycL n m`'s `m`), and [WTape.cycLW] generalises it on both
              sides -- but [WTape.cycR] requires the left window EMPTY and
              `SCycR n` has no offset at all.  A lap that walks the block back
              rightward past a concrete left prefix cannot be written down.

  unreachable the reachable set is closed and contains the target in no form.
              These need a different anchor or a different decomposition.

Usage
  intgap.py --list FILE [--out JSON]
  intgap.py --spec SPEC
"""
import argparse
import collections
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

import emit_lapcert as EL                                          # noqa: E402
import lapcert as LC                                               # noqa: E402
from emit_interleave import parse, LAB                             # noqa: E402
from mirror_common import mirror_spec                              # noqa: E402

JMAX = 5


def _den(side, j):
    pre, u, a, b, post = side
    return tuple(pre) + tuple(u) * (a * j + b) + tuple(post)


def _closure(tab, src, tgt, cap=20000):
    """The symbolic states reachable from [src] under the whole step language,
    and the dead ends (states with no legal step at all)."""
    q, seen, dead = collections.deque([src]), {src}, []
    while q and len(seen) < cap:
        c = q.popleft()
        cand = (LC._win_candidates(tab, False, True, c, 64, tgt, False)
                + LC._cyc_candidates(tab, False, True, c, 64)
                + LC._rot_candidates(c))
        n = 0
        for stp in cand:
            r = LC.sstep(tab, False, True, stp, c)
            if r is None:
                continue
            n += 1
            if r[0] not in seen:
                seen.add(r[0])
                q.append(r[0])
        if n == 0:
            dead.append(c)
    return seen, dead


def _cycr_gap(dead):
    """A dead end whose RIGHT side still carries the rep block and whose LEFT
    prefix is non-empty.

    HISTORICAL NAME, and a warning.  Wave-29 section 10a read this shape as a
    MISSING PRIMITIVE -- the mirror of `WTape.cycLW`, which would let a lap
    walk the block back rightward past a concrete left prefix -- and wave-30
    was scoped to build it.  Measured (wave-30 section 1): wiring in every
    SOUND instance of that mirror derives ZERO new chains on all 17 rows this
    predicate selects.  The shape is necessary for a `cycRW` step and nowhere
    near sufficient.

    What actually blocks these dead ends is `_cross_period` below.  Keep this
    predicate only as the SELECTOR for that measurement."""
    return [c for c in dead if c[3][1] and c[1][0] and not c[1][1]]


def _cross_period(tab, c, rmax=8, nmax=64):
    """The STATE PERIOD of the rightward crossing at a `_cycr_gap` dead end.

    `WTape.cycR` (and any windowed mirror of it) needs ONE unit of the right
    block to return the machine to the state and head it entered with: that is
    the induction hypothesis, and it is what makes `rep u k` cost `P * k`.
    Measure how many units it actually takes.

      1     one unit closes -- a `cycR`-shaped step exists in principle
      2     the state ALTERNATES over single-cell units, so no `cycR` at unit
            size 1 can close and the block's count must be made even first:
            a PARITY device, not a new cycle lemma
      None  the state never returns within `rmax` units -- the crossing
            drifts, and the lap is not affine at all (these rows come out
            HIGHER/EXP/QUAD under `ovfshape`)
    """
    q, L, h, R = c
    st, seq = q, []
    for r in range(1, rmax + 1):
        cfg, got = (st, L[0], h, R[1]), None
        for _ in range(nmax):
            try:
                cfg = LC.wstep(tab, True, True, cfg)
            except LC.Halt:
                return None, seq
            if cfg is None:
                return None, seq
            if not cfg[3] and cfg[2] == h:
                got = cfg
                break
        if got is None:
            return None, seq
        st = got[0]
        seq.append(st)
        if st == q:
            return r, seq
    return None, seq


def _cross(tab, dead):
    """The crossing periods over every `_cycr_gap` dead end of a framing."""
    return [_cross_period(tab, c)[0] for c in _cycr_gap(dead)]


def _same(a, b, strip):
    for j in range(JMAX):
        x, y = _den(a, j), _den(b, j)
        if strip:
            x, y = LC.rstrip0(x), LC.rstrip0(y)
        if x != y:
            return False
    return True


def _equal_in_set(seen, tgt, strip):
    return [c for c in seen if c[0] == tgt[0] and c[2] == tgt[2]
            and _same(c[1], tgt[1], strip) and _same(c[3], tgt[3], strip)]


def probe(spec):
    """The FIRST anchor family the flat route offers, and why its interior
    branch does not derive."""
    for mir in (False, True):
        ds = mirror_spec(spec) if mir else spec
        tab = parse(ds)
        for (edge, tail, p0, enc, far) in EL.anchors(ds):
            d = EL.ENCDATA[enc]
            uS, sS = tuple(d['uS']), tuple(d['sS'])
            uD, sD = tuple(d['uD']), tuple(d['sD'])
            F = (tuple(far), (), 0, 0, ())
            st = LAB.index(edge)
            frames = {
                'one': ((st, ((), uS, 1, 0, sS), 0, F),
                        (st, ((), uD, 1, 0, sD), 0, F)),
                'z': ((st, (sS, (), 0, 0, ()), 0, F),
                      (st, (sD, (), 0, 0, ()), 0, F)),
                'p': ((st, (uS, uS, 1, 0, sS), 0, F),
                      (st, (uD, uD, 1, 0, sD), 0, F)),
            }
            out = dict(spec=spec, mirror=mir, enc=enc, edge=edge,
                       tail=list(tail), far=list(far))
            for name, (a, b) in frames.items():
                exact = LC.derive_chain(tab, False, True, a, b)
                lift = (None if exact is not None
                        else LC.derive_chain(tab, False, True, a, b, lift=True))
                seen, dead = _closure(tab, a, b)
                cross = _cross(tab, dead)
                out[name] = dict(
                    exact=exact is not None, lift=lift is not None,
                    reach=len(seen), dead=len(dead),
                    cycr=len(_cycr_gap(dead)),
                    cross=cross,
                    denot=len(_equal_in_set(seen, b, False)),
                    liftable=len(_equal_in_set(seen, b, True)))
            out['verdict'] = verdict(out)
            return out
    return dict(spec=spec, verdict='no anchor family')


def verdict(o):
    z, p, one = o['z'], o['p'], o['one']
    if one['exact'] or (z['exact'] and p['exact']):
        return 'derives (already boarded or another gate)'
    if (z['exact'] or z['lift']) and (p['exact'] or p['lift']):
        return 'lift: split x lift is not wired'
    # The dead-end SHAPE is not the diagnosis -- the crossing PERIOD is.
    # Wave-30 section 1: the sound mirror of `cycLW` derives 0 new chains on
    # every row the shape selects, and the periods say why.
    cross = [x for k in ('p', 'z', 'one') for x in o[k].get('cross') or []]
    if cross:
        if any(x == 2 for x in cross):
            return ('parity-cross: rightward crossing has state period 2 '
                    '(needs an even block count, not a new cycle lemma)')
        if all(x is None for x in cross):
            return ('drift-cross: rightward crossing never returns to its '
                    'entry state (the lap is not affine)')
        return 'cross-period %s' % sorted({str(x) for x in cross})
    return 'unreachable: target in no form'


def _families(dspec):
    """EVERY anchor family this repo can offer for one (already-mirrored) spec:
    the flat enumeration, `restscan`'s TOLERANT key (which reads the family off
    the machine's own rests, so it finds tails the enumeration never offers),
    and `tailcert.two_form`'s PARITY-SPLIT pair.

    Yields (source, enc, state, tail, far).  `probe` only ever looked at the
    FIRST of the first source, which is why 26 rows were filed `unreachable`:
    that verdict was about one family, not about the machine."""
    seen = set()

    def add(src, enc, st, tail, far):
        k = (enc, st, tuple(tail), tuple(far))
        if k in seen:
            return
        seen.add(k)
        out.append((src,) + k)

    out = []
    for (edge, tail, p0, enc, far) in EL.anchors(dspec):
        add('anchors', enc, LAB.index(edge), tail, far)
    try:
        import restscan as RS
        b = RS.best_key(dspec)
        if b is not None:
            enc, q, tl, far = b[1]
            if enc in EL.ENCDATA:
                add('restscan', enc, q, tl, far)
    except Exception:                                          # noqa: BLE001
        pass
    try:
        import tailcert as TC
        enc, frames, ks = TC.two_form(dspec)
        for bb in frames:
            add('two_form', enc, frames[bb][0], frames[bb][1], frames[bb][2])
    except Exception:                                          # noqa: BLE001
        pass
    return out


def probe_every(spec):
    """Is the interior target reachable at ANY anchor family, in either mirror?

    Prompt item (5): four of wave-29's seven sub-classes dissolved on exactly
    this move, so MEASURE before designing anything for the `unreachable` 26."""
    best, tried = None, []
    for mir in (False, True):
        dspec = mirror_spec(spec) if mir else spec
        tab = parse(dspec)
        for (src, enc, st, tail, far) in _families(dspec):
            d = EL.ENCDATA[enc]
            uS, sS = tuple(d['uS']), tuple(d['sS'])
            uD, sD = tuple(d['uD']), tuple(d['sD'])
            F = (tuple(far), (), 0, 0, ())
            frames = {
                'one': ((st, ((), uS, 1, 0, sS), 0, F),
                        (st, ((), uD, 1, 0, sD), 0, F)),
                'z': ((st, (sS, (), 0, 0, ()), 0, F),
                      (st, (sD, (), 0, 0, ()), 0, F)),
                'p': ((st, (uS, uS, 1, 0, sS), 0, F),
                      (st, (uD, uD, 1, 0, sD), 0, F)),
            }
            hit = {}
            for name, (a, b) in frames.items():
                e = LC.derive_chain(tab, False, True, a, b)
                l = (None if e is not None
                     else LC.derive_chain(tab, False, True, a, b, lift=True))
                hit[name] = 'exact' if e else 'lift' if l else '-'
            rank = (0 if hit['one'] == 'exact'
                    or (hit['z'] == 'exact' and hit['p'] == 'exact')
                    else 1 if hit['one'] != '-'
                    or (hit['z'] != '-' and hit['p'] != '-')
                    else 2)
            rec = dict(src=src, mirror=mir, enc=enc, state=LAB[st],
                       tail=list(tail), far=list(far), hit=hit, rank=rank)
            tried.append(rec)
            if best is None or rank < best['rank']:
                best = rec
            if rank == 0:
                break
        if best is not None and best['rank'] == 0:
            break
    if best is None:
        return dict(spec=spec, verdict='no anchor family at all', tried=0)
    v = ('DERIVES at %s (%s@%s tail=%s)' % (best['src'], best['enc'],
                                            best['state'], best['tail'])
         if best['rank'] == 0 else
         'reachable up to lift at %s' % best['src'] if best['rank'] == 1
         else 'unreachable at every family')
    return dict(spec=spec, verdict=v, tried=len(tried), best=best,
                families=tried)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list')
    ap.add_argument('--spec')
    ap.add_argument('--out')
    ap.add_argument('--every', action='store_true',
                    help='probe EVERY anchor family (prompt item 5)')
    a = ap.parse_args()
    specs = ([a.spec] if a.spec else
             [x.strip() for x in open(a.list) if x.strip()])
    res, cnt = [], collections.Counter()
    for i, spec in enumerate(specs):
        try:
            r = probe_every(spec) if a.every else probe(spec)
        except Exception as e:                                 # noqa: BLE001
            r = dict(spec=spec, verdict='ERR %s: %s' % (type(e).__name__, e))
        res.append(r)
        cnt[r['verdict'].split(':')[0].split(' at ')[0]] += 1
        print('%4d/%d %-40s %-16s %s' % (
            i + 1, len(specs), spec,
            r.get('enc') or (r.get('best') or {}).get('enc', '-'),
            r['verdict']), flush=True)
    print()
    for k, v in cnt.most_common():
        print('%5d  %s' % (v, k))
    if a.out:
        json.dump(res, open(a.out, 'w'), indent=1)


if __name__ == '__main__':
    main()
