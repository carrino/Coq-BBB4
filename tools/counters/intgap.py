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
    prefix is non-empty: exactly what `SCycR n m` would consume."""
    return [c for c in dead if c[3][1] and c[1][0] and not c[1][1]]


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
                out[name] = dict(
                    exact=exact is not None, lift=lift is not None,
                    reach=len(seen), dead=len(dead),
                    cycr=len(_cycr_gap(dead)),
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
    if p['cycr'] or z['cycr']:
        return 'cycR-gap: SCycR has no left-prefix offset'
    return 'unreachable: target in no form'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list')
    ap.add_argument('--spec')
    ap.add_argument('--out')
    a = ap.parse_args()
    specs = ([a.spec] if a.spec else
             [x.strip() for x in open(a.list) if x.strip()])
    res, cnt = [], collections.Counter()
    for i, spec in enumerate(specs):
        try:
            r = probe(spec)
        except Exception as e:                                 # noqa: BLE001
            r = dict(spec=spec, verdict='ERR %s: %s' % (type(e).__name__, e))
        res.append(r)
        cnt[r['verdict'].split(':')[0]] += 1
        print('%4d/%d %-40s %-16s %s' % (
            i + 1, len(specs), spec, r.get('enc', '-'), r['verdict']),
            flush=True)
    print()
    for k, v in cnt.most_common():
        print('%5d  %s' % (v, k))
    if a.out:
        json.dump(res, open(a.out, 'w'), indent=1)


if __name__ == '__main__':
    main()
