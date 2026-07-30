#!/usr/bin/env python3
"""UNTRUSTED measurement: the WALL's displacement per overflow, and the growth
rate of the phase between overflows.

John's read of `1RB1RD_1LC1RA_0RB0LC_1LA0RD`: "a counter with 0s to the left of
each bit with a wall on the right, msb on the right, when the msb overflows the
wall moves over 4", and then the clarification that settles where to look --
"the msb butts up against the wall but doesn't include it".

The wall is a SEPARATE object just beyond the top of the word, which is why
`digitwidth.py` (which measures the WORD) sees 2 cells per octave and no wall
motion at all.  Track the wall instead: the first run of >= 2 ones outward from
the head (two adjacent ones cannot be counter digits under a dig0=00/dig1=01
style alphabet), its absolute column, and the time between successive
displacements.

    wall_step   cells the wall moves per overflow
    ratio       phase(k+1)/phase(k), i.e. how the overflow arm's cost grows

`nestcert`'s register step is built for an inner counter that RE-COUNTS the
counter, which is Theta(2^k).  A phase growing ~4x per octave is not that shape,
and a search for a 2^k inner family will not find it -- which is what
`register step does not close` looks like from the outside.

Usage
  wallstep.py --list FILE [--out JSON] [--maxt N]
  wallstep.py --spec SPEC
"""
import argparse
import collections
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import lapcert as LC                                               # noqa: E402
from emit_interleave import parse                                  # noqa: E402
from mirror_common import mirror_spec                              # noqa: E402


def _wall(seq):
    """(start, end) of the first run of >= 2 ones, or None."""
    for i in range(len(seq) - 1):
        if seq[i] == 1 and seq[i + 1] == 1:
            j = i
            while j + 1 < len(seq) and seq[j + 1] == 1:
                j += 1
            return i, j
    return None


def _side(spec, maxt, right):
    """First sighting of each distinct wall start column, on one side."""
    tab = parse(spec)
    cfg, pos, seen = (0, (), 0, ()), 0, {}
    for t in range(1, maxt):
        q, l, h, r = cfg
        if h == 0:
            seq = list(r) if right else list(l)
            w = _wall(seq)
            if w is not None:
                col = pos + 1 + w[0] if right else pos - 1 - w[0]
                if col not in seen:
                    seen[col] = (t, w[1] - w[0] + 1)
        nx = LC.wstep(tab, False, False, cfg)
        if nx is None:
            break
        pos += 1 if len(nx[1]) > len(l) else -1
        cfg = nx
    return seen


def probe(spec, maxt=200000):
    best = None
    for mir in (False, True):
        ds = mirror_spec(spec) if mir else spec
        for right in (True, False):
            seen = _side(ds, maxt, right)
            if len(seen) < 4:
                continue
            cols = sorted(seen, reverse=not right)
            steps = [abs(cols[i + 1] - cols[i]) for i in range(len(cols) - 1)]
            ts = [seen[c][0] for c in cols]
            gaps = [ts[i + 1] - ts[i] for i in range(len(ts) - 1)]
            ratio = [round(gaps[i + 1] / gaps[i], 2)
                     for i in range(len(gaps) - 1) if gaps[i]]
            st = collections.Counter(steps).most_common(1)[0]
            cand = dict(spec=spec, mirror=mir, side='R' if right else 'L',
                        walls=len(cols), wall_step=st[0],
                        step_regular=st[1] == len(steps),
                        steps=steps[:8], gaps=gaps[:8], ratio=ratio[:6],
                        median_ratio=(sorted(ratio)[len(ratio) // 2]
                                      if ratio else None))
            # prefer a side whose displacement is REGULAR and whose phase
            # GROWS: the left side of a leftward-growing counter is full of
            # incidental `11` pairs and yields a step of 1 with a flat ratio.
            def rank(c):
                return (0 if c['step_regular'] and c['wall_step'] > 1 else 1,
                        0 if (c['median_ratio'] or 0) > 1.2 else 1,
                        -c['walls'])
            if best is None or rank(cand) < rank(best):
                best = cand
    if best is None:
        return dict(spec=spec, verdict='no wall found')
    r = best['median_ratio']
    best['verdict'] = (
        'wall +%d/overflow, phase ratio ~%s' % (best['wall_step'], r)
        if r is not None else 'wall +%d/overflow' % best['wall_step'])
    return best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list')
    ap.add_argument('--spec')
    ap.add_argument('--out')
    ap.add_argument('--maxt', type=int, default=200000)
    a = ap.parse_args()
    specs = ([a.spec] if a.spec else
             [x.strip() for x in open(a.list) if x.strip()])
    res, cnt = [], collections.Counter()
    for i, spec in enumerate(specs):
        try:
            o = probe(spec, a.maxt)
        except Exception as e:                                 # noqa: BLE001
            o = dict(spec=spec, verdict='ERR %s: %s' % (type(e).__name__, e))
        res.append(o)
        cnt['step=%s ratio~%s' % (o.get('wall_step', '-'),
                                  o.get('median_ratio', '-'))] += 1
        print('%3d/%d %-30s %-4s walls=%-3s %s' % (
            i + 1, len(specs), spec, o.get('side', '-'),
            o.get('walls', '-'), o['verdict']), flush=True)
    print()
    for k, v in cnt.most_common():
        print('%5d  %s' % (v, k))
    if a.out:
        json.dump(res, open(a.out, 'w'), indent=1)


if __name__ == '__main__':
    main()
