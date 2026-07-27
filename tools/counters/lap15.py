#!/usr/bin/env python3
"""The micro-lap of 1RB0RC_0LC1LB_0LD1LC_1RD0RA (wave4 #15), measured.

#15 is the mod-4 wave odometer.  Sampled at the LEFT RECORD -- head on the
leftmost visited cell, StC, reading blank, left list empty -- the tape is

    (StC, ([], S0, 1^lead 0 1^v0 0 1^v1 0 ... 0 1^vn 0))

with `lead` alternating 1 / 2 (BBB's lead-1/2 micro-period) and `v` the block
vector, frontier-first.  Two rules alternate:

  A  lead 1 -> 2:  v[0] += 1                                   10 steps
  B  lead 2 -> 1:  let i = least index with v[i] mod 4 /= 0
       v[i] mod 4 = 1:  v[i] += 2, v[i+1] += 1   4*sum(v[..i]) + 4i + 18
       v[i] mod 4 = 3:  v[i] += 1, append 2      4*sum(v[..i]) + 4i + 22

Rule B is the mod-4 analogue of `WaveCounter.carry`: the scan walks the
vector until it finds a block that is not 0 mod 4, deposits there, and the
residue-3 case is the SPAWN (a new length-2 block at the far end) exactly as
the mod-2 family's all-even case spawns a length-1 block.

Measured facts this file checks, over every anchor out to the step budget:

  * both rules and all three step counts, exactly (0 mismatches to t = 4e5);
  * the scan never runs off the end (some block is /= 0 mod 4);
  * the residue at the stop is never 2 -- residue 2 is what would make the
    deposit ill-defined, and it is what the safety invariant has to exclude;
  * a residue-3 stop is always at the LAST index, so the spawn is always at
    the far end.

Those last three are what the Coq invariant must imply -- the mod-4
replacement for `pbits`/`fp`/`carry_ok`/`WInv` in `theories/Counters/
WaveCounter.v`.  NOTE the invariant is a statement about the FIRST nonzero
residue only: interior residue 3 does occur (e.g. the residue word `1312`),
it is simply never reached by the scan.

UNTRUSTED, like everything under tools/.  Usage: `python3 lap15.py [budget]`.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe15 import cstep, A, B, C, D, S0, S1, c0


def blocks(R):
    """Run lengths of the 1-runs of a right half-tape list."""
    out, i, n = [], 0, len(R)
    while i < n:
        if R[i] == S1:
            j = i
            while j < n and R[j] == S1:
                j += 1
            out.append(j - i)
            i = j
        else:
            i += 1
    return out


def anchors(budget):
    """Every left record, as (t, lead, vector)."""
    c, out = c0, []
    for t in range(budget):
        q, (L, h, R) = c
        if q == C and L == [] and h == S0 and R and R[0] == S1:
            b = blocks(R)
            out.append((t, b[0], b[1:]))
        c = cstep(c)
        if c is None:
            break
    return out


def stop(v):
    """(index, residue) of the first block that is not 0 mod 4."""
    for i, x in enumerate(v):
        if x % 4:
            return i, x % 4
    return None, None


def nextA(lead, v):
    """The abstract successor, and the step count it costs."""
    if lead == 1:
        return 2, [v[0] + 1] + v[1:], 10
    i, r = stop(v)
    assert i is not None, ('carry ran off the end', v)
    assert r != 2, ('residue 2 at the stop', v)
    base = 4 * sum(v[:i + 1]) + 4 * i
    if r == 1:
        assert i + 1 < len(v), ('residue 1 at the last index', v)
        return 1, v[:i] + [v[i] + 2, v[i + 1] + 1] + v[i + 2:], base + 18
    assert i == len(v) - 1, ('residue 3 away from the last index', v)
    return 1, v[:i] + [v[i] + 1, 2], base + 22


def main():
    budget = int(sys.argv[1]) if len(sys.argv) > 1 else 400000
    rows = anchors(budget)
    bad, kinds, maxi = [], {}, 0
    for k in range(len(rows) - 1):
        (t, lead, v), (t2, lead2, v2) = rows[k], rows[k + 1]
        if not v:
            continue          # the boot anchor, before the vector exists
        if lead == 2:
            i, r = stop(v)
            kinds[r] = kinds.get(r, 0) + 1
            maxi = max(maxi, i if i is not None else 0)
        try:
            nl, nv, n = nextA(lead, v)
        except AssertionError as e:
            bad.append('t=%d %s: %s' % (t, v, e.args[0]))
            continue
        if (nl, nv) != (lead2, v2):
            bad.append('t=%d lead=%d %s -> %s, predicted %d %s'
                       % (t, lead, v, v2, nl, nv))
        elif t2 - t != n:
            bad.append('t=%d lead=%d %s: %d steps, predicted %d'
                       % (t, lead, v, t2 - t, n))
    print('#15 micro-lap over %d anchors (t <= %d)' % (len(rows), rows[-1][0]))
    print('  rule-B stops by residue: %s   deepest scan: index %d'
          % (kinds, maxi))
    for m in bad[:8]:
        print('  FAIL %s' % m)
    print('#15 lap: %s' % ('OK' if not bad else '%d FAILURES' % len(bad)))
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
