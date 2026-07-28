#!/usr/bin/env python3
"""The exponential exit is a DESCENDING-OCTAVE CASCADE -- the wave-23 probe.

WAVE18 section 4b measured the `no exit chain` / `no boot chain` halves
EXPONENTIAL and diagnosed a family-identification gap; wave-22 measured the
fixed-N multi-count route at 0 of 87.  This probe shows why, and what the
structure actually is:

  one outer overflow phase =
      main count   2^j     .. 2^(j+1)-1        tail T0
      then, for level l = j-1 down to 2:
          TWO counts 2^l .. 2^(l+1)-1          tails growing by one unit
      then the closing sweep to the outer successor

(`timeline` on 0RB1LA_0LC1RD_1LA1LD_1RB0LA at K=7 prints it verbatim.)
The step cost is Theta(2^j) -- section 4b's exponential -- but the number
of counts per phase is AFFINE in j, which is why no fixed-N chain list can
express it and the N-count search measured 0.  The cascade was invisible to
`nestcert.families` for two mechanical reasons:

  * it only searches octaves >= 0 (`2^(K-1+o)` with `o >= 0`); the cascade
    counts run BELOW the main octave (o < 0);
  * its key tails are capped at MAXTAIL = 3; the cascade tails grow by one
    unit per level (5, 7, 9, ... cells).

Boarding these needs a LEVEL INDUCTION (the fractal lesson, HOLDOUTS_FRACTAL
section: "a carry of length m is not a gadget -- it IS the machine one level
down"): a `NestedLapCascade` composition theorem inducting over the level,
whose per-level pieces are ordinary chains UNIFORM IN THE LEVEL INDEX (the
tails are `rep unit l ++ base`, an sside), plus `inner_to_fill_lift` at
`v0 = pow2 l` -- already stated at arbitrary `v0`.

Usage:
  cascade_probe.py --classify            # the whole no-exit/no-boot bucket
  cascade_probe.py --timeline SPEC [-K 7]

UNTRUSTED like everything under tools/: measurement only.
"""
import argparse
import collections
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

import emit_lapcert as E                                       # noqa: E402
import nestcert as NC                                          # noqa: E402
from emit_interleave import parse, LAB, ENC as ENCF            # noqa: E402


def gather_idx(mid, maxtail, encs=None):
    """(key -> [(mid index, decoded value)]) over deep tails."""
    hits = collections.defaultdict(list)
    for i, (q, l, r) in enumerate(mid):
        for name in (encs or E.ENCS):
            d = E.ENCDATA[name]
            if d['obS'] != 0:
                continue
            A, B, C = tuple(d['uD']), tuple(d['uS']), tuple(d['soD'])
            for k in range(maxtail + 1):
                if k > len(l) - 1:
                    break
                head, tl = (l[:len(l) - k], l[len(l) - k:]) if k else (l, ())
                v = NC.decode(head, A, B, C)
                if v is not None:
                    hits[(name, q, tl, r)].append((i, v))
    return hits


def segments(mid, maxtail=40, minlen=4, encs=None):
    """Maximal consecutive-ascending count segments, longest-range kept when
    one octave shadows another over the same interval."""
    segs = []
    for key, iv in gather_idx(mid, maxtail, encs).items():
        i0 = 0
        while i0 < len(iv):
            j = i0
            while j + 1 < len(iv) and iv[j + 1][1] == iv[j][1] + 1:
                j += 1
            if j - i0 + 1 >= minlen:
                segs.append((iv[i0][0], iv[j][0], iv[i0][1], iv[j][1], key))
            i0 = j + 1
    segs.sort()
    return [s for s in segs
            if not any(o[0] <= s[0] and s[1] <= o[1]
                       and (o[3] - o[2]) > (s[3] - s[2]) for o in segs)]


def phase(spec, K, maxT=1500000):
    """First anchor candidate (mirror searched) whose overflow phase closes."""
    for mirrored in (False, True):
        dspec = E.mirror_spec(spec) if mirrored else spec
        tab = parse(dspec)
        for (edge, tail, p0, enc, far) in E.anchors(dspec):
            st0 = LAB.index(edge)
            try:
                mid = NC.phase_mid(tab, st0, ENCF[enc], tail, far, K=K,
                                   maxT=maxT)
            except Exception:                                  # noqa: BLE001
                continue
            return mid, mirrored, enc, edge
    return None, None, None, None


def octave_profile(mid):
    """How many full-octave runs 2^p .. 2^(p+1)-1 occur, per p."""
    octs = collections.Counter()
    for (a, b, v0, v1, key) in segments(mid):
        p = v0.bit_length() - 1
        if v0 == 2 ** p and v1 == 2 ** (p + 1) - 1:
            octs[p] += 1
    return octs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--classify', action='store_true')
    ap.add_argument('--timeline')
    ap.add_argument('-K', type=int, default=6)
    a = ap.parse_args()

    if a.timeline:
        mid, mir, enc, edge = phase(a.timeline, a.K, maxT=3000000)
        if mid is None:
            print('no phase'); return
        print('%s K=%d mir=%s outer=%s@%s |mid|=%d'
              % (a.timeline, a.K, mir, enc, edge, len(mid)))
        for (i0, i1, v0, v1, key) in segments(mid):
            print('  mid[%4d..%4d]  %5d..%5d   %s@%s tail=%s far=%s'
                  % (i0, i1, v0, v1, key[0], LAB[key[1]],
                     ''.join(map(str, key[2])), ''.join(map(str, key[3]))))
        return

    tsv = os.path.join(REPO, 'tools/closeout/residue_map.tsv')
    specs = [l.split('\t')[0] for l in open(tsv)
             if 'no exit chain' in l or 'no boot chain' in l]
    tot = collections.Counter()
    for spec in specs:
        mid, mir, enc, edge = phase(spec, a.K)
        if mid is None:
            print('%-40s NO PHASE' % spec); tot['no-phase'] += 1; continue
        octs = octave_profile(mid)
        ndesc = len([p for p in octs if p < a.K - 1])
        casc = ndesc >= 3
        tot['cascade' if casc else 'other'] += 1
        print('%-40s |mid|=%4d  %s  %s'
              % (spec, len(mid),
                 ' '.join('2^%d:x%d' % (p, octs[p])
                          for p in sorted(octs, reverse=True)),
                 'CASCADE' if casc else ''))
    print(tot)


if __name__ == '__main__':
    main()
