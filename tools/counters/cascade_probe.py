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
  cascade_probe.py --endpoints SPEC [-K 7]   # the LAW + the gated chains
  cascade_probe.py --gate                    # --endpoints over the bucket

The run/segment scan and every endpoint framing live in `nestcert.py`, beside
`phase_mid`: section 4c of the brief measured two ad-hoc trace scripts
disagreeing on blank-head numbering, so the conventions are single-sourced
there and this file only drives them.

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
    return NC._gather_idx(mid, E.ENCDATA, E.ENCS, maxtail, encs)


def segments(mid, maxtail=40, minlen=4, encs=None):
    """Maximal consecutive-ascending count segments, longest-range kept when
    one octave shadows another over the same interval."""
    return NC.cascade_segments(mid, E.ENCDATA, E.ENCS, maxtail, minlen, encs)


def anchor(spec, K, maxT=1500000):
    """The first anchor candidate (mirror searched) whose overflow phase
    closes, with everything [nestcert.cascade_endpoints] needs to re-derive
    it."""
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
            return dict(tab=tab, mid=mid, mirrored=mirrored, enc=enc,
                        edge=edge, st0=st0, tail=tail, far=far)
    return None


def phase(spec, K, maxT=1500000):
    """First anchor candidate (mirror searched) whose overflow phase closes."""
    a = anchor(spec, K, maxT)
    if a is None:
        return None, None, None, None
    return a['mid'], a['mirrored'], a['enc'], a['edge']


def octave_profile(mid):
    """How many full-octave runs 2^p .. 2^(p+1)-1 occur, per p."""
    octs = collections.Counter()
    for (a, b, v0, v1, key) in segments(mid):
        p = v0.bit_length() - 1
        if v0 == 2 ** p and v1 == 2 ** (p + 1) - 1:
            octs[p] += 1
    return octs


def endpoints(spec, K, jhi=8, quiet=False):
    """Gate one machine: read the law, check it against the phase, derive the
    boot / lap / transition chains, and replay them all against the raw
    simulator.  Returns the record, or raises."""
    A = anchor(spec, K, maxT=4000000)
    if A is None:
        raise NC.NestError('no overflow phase at K=%d' % K)
    d = NC.cascade_endpoints(A['tab'], E.ENCDATA, E.ENCS, E.ENC, A['enc'],
                             A['st0'], A['tail'], A['far'], K=K)
    d['nval'] = NC.cascade_validate(A['tab'], E.ENC, E.ENCDATA, A['enc'],
                                    A['st0'], A['tail'], A['far'], d,
                                    2, jhi)
    d['anchor'] = A
    if not quiet:
        law = d['law']
        print('%s  K=%d  mir=%s  outer=%s@%s' % (spec, K, A['mirrored'],
                                                 A['enc'], A['edge']))
        print('  law  inner=%s@%s far=%r  unit=%r extraA=%r extraB=%r '
              'M-j=%d  main_is_B=%s'
              % (law['inner'], LAB[law['st_in']], law['far_in'], law['unit'],
                 law['extraA'], law['extraB'], law['M'] - law['j'],
                 law['main_is_B']))
        print('  levels found in the phase: %s'
              % ' '.join('%d' % l for l, _ in law['found']))
        print('  boot cost=%d*j+%d  lap cost=%d*i+%d'
              % (d['cb'][0], d['cb'][1], d['cn'][0], d['cn'][1]))
        for k in ('ENTRY', 'AB', 'BA', 'CLOSE', 'CLOSEA', 'CLOSEB'):
            if k not in d['trans']:
                continue
            t = d['trans'][k]
            print('  %-6s i=n%+d peel=%s post=%d el=%s lift=%s cost=%d*i+%d  %s'
                  % (k, t['ioff'], t['peel'], t['post'], t['el'], t['lift'],
                     t['cost'][0], t['cost'][1],
                     ' '.join(E.cstep_str(s) for s in t['chain'])))
        print('  %s' % d['nval'])
    return d


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--classify', action='store_true')
    ap.add_argument('--timeline')
    ap.add_argument('--endpoints')
    ap.add_argument('--gate', action='store_true')
    ap.add_argument('-K', type=int, default=6)
    a = ap.parse_args()

    if a.endpoints:
        endpoints(a.endpoints, a.K if a.K != 6 else 7)
        return

    if a.gate:
        tsv = os.path.join(REPO, 'tools/closeout/residue_map.tsv')
        specs = [l.split('\t')[0] for l in open(tsv)
                 if 'no exit chain' in l or 'no boot chain' in l]
        tot = collections.Counter()
        for spec in specs:
            try:
                d = endpoints(spec, a.K if a.K != 6 else 7, quiet=True)
            except Exception as e:                             # noqa: BLE001
                msg = str(e)[:64]
                print('%-40s %s' % (spec, msg))
                tot[msg] += 1
                continue
            print('%-40s GATED  %s' % (spec, d['nval']))
            tot['GATED'] += 1
        print(tot)
        return

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
