#!/usr/bin/env python3
"""UNTRUSTED measurement: is the counter's fill expensive because the family
reads only ONE PHASE of it?

`fillcost.py` measures that on the `overflow leaves the family` rows the
INTERIOR increment is affine while the FILL costs `Theta(2^p)` -- one whole lap
of the counter.  A rung-two arm's step count is a sum of affine `fired`
expressions, so an exponential fill is not an arm that a wider search finds; it
is either rung three or a misreading.

This tool tests the misreading.  `Fam` pins ONE terminator (`Fam.tail`), read
off the common suffix of the anchor visits that share the commonest far side.
If the machine runs the same digit alphabet through several terminators in
turn -- lap in phase 0, lap in phase 1, then widen -- then every visit the
one-tail family calls undecodable is an ordinary member of another phase, the
`Theta(2^p)` "fill" is two whole laps the reader could not see, and the real
fill (top of phase i -> bottom of phase i+1) is short.

So: walk the anchor visits, decode what the family can, and try to explain the
REST by varying the terminator alone -- everything else (anchor, digits, base,
far side) stays exactly as the family read it.  Report how many phases it takes
to explain the visits, the transition table at the tops, and the per-member gap
that results.

Usage: phases.py --list rows.txt [--out phases.jsonl] [--steps 200000]
       phases.py --spec SPEC [--verbose]
"""

import argparse
import copy
import json
import os
import statistics
import sys
import time
from collections import Counter

from discover import build_ladder, mine_shapes
from engine import parse_tm
from trace import block_rle, simulate

import valfam as V

HERE = os.path.dirname(os.path.abspath(__file__))


def visits(fam, tm, steps):
    """[(t, counter-side cells, p)] at every anchor visit of the raw run."""
    tape, pos, q, lo, hi = {}, 0, 0, 0, 0
    out = []
    for t in range(steps):
        h = tape.get(pos, 0)
        if q == fam.q and h == fam.h:
            gl = [tape.get(pos - 1 - i, 0) for i in range(pos - lo)]
            gr = [tape.get(pos + 1 + i, 0) for i in range(hi - pos)]
            while gl and gl[-1] == 0:
                gl.pop()
            while gr and gr[-1] == 0:
                gr.pop()
            cfg = (q, h, block_rle(gl), block_rle(gr))
            pp = fam.far_p(cfg)
            if pp is not None:
                c = V.runs_cells(fam.counter_side(cfg))
                if c is not None:
                    out.append((t, tuple(c), pp))
        tr = tm.get((q, h))
        if tr is None:
            break
        w, d, q = tr
        tape[pos] = w
        pos += d
        lo, hi = min(lo, pos), max(hi, pos)
    return out


def with_tail(fam, tail):
    g = copy.copy(fam)
    g.tail = tuple(tail)
    return g


def candidate_tails(fam, cells, maxlen=None):
    """Terminators worth trying: the suffixes of the cell strings the family
    itself cannot read.  Nothing is curated -- the alternatives come out of the
    same trace, and a tail that explains nothing is dropped by the count."""
    maxlen = maxlen if maxlen is not None else 2 * fam.l + 1
    out = Counter()
    for c in cells:
        for tl in range(maxlen + 1):
            out[tuple(c[len(c) - tl:]) if tl else ()] += 1
    return [t for t, _ in out.most_common()]


def phase_split(fam, obs, max_phases=4, min_visits=6):
    """Greedy: the family's own tail is phase 0; then repeatedly take the tail
    that reads the most still-unread visits."""
    phases = [fam.tail]
    readers = [fam]
    unread = [c for _, c, _ in obs if fam.decode(list(c)) is None]
    while len(phases) < max_phases and unread:
        best, bestn = None, 0
        for t in candidate_tails(fam, unread)[:24]:
            if t in phases:
                continue
            g = with_tail(fam, t)
            n = sum(1 for c in unread if g.decode(list(c)) is not None)
            if n > bestn:
                best, bestn = t, n
        if best is None or bestn < min_visits:
            break
        phases.append(best)
        readers.append(with_tail(fam, best))
        unread = [c for c in unread
                  if all(r.decode(list(c)) is None for r in readers)]
    return phases, readers, len(unread)


def read_all(readers, obs):
    """[(t, phase, digits, p)] for every visit some phase reads."""
    out = []
    for t, c, pp in obs:
        for i, r in enumerate(readers):
            ds = r.decode(list(c))
            if ds is not None:
                out.append((t, i, ds, pp))
                break
    return out


def measure(spec, steps=200000, trace=20000, ladder_cap=60.0, which=0):
    t0 = time.time()
    tm = parse_tm(spec)
    snaps = simulate(tm, trace)
    if snaps and snaps[-1][1] is None:
        return {'spec': spec, 'verdict': 'halts'}
    rules = build_ladder(tm, mine_shapes(snaps), time_cap=ladder_cap)
    fams = V.find_families(tm, snaps, rules)
    if not fams:
        return {'spec': spec, 'verdict': 'no family'}
    fam = fams[min(which, len(fams) - 1)][0]
    obs = visits(fam, tm, steps)
    if not obs:
        return {'spec': spec, 'verdict': 'no anchor visit'}
    phases, readers, n_unread = phase_split(fam, obs)
    seq = read_all(readers, obs)
    # the transition table: what a phase's TOP string goes to
    trans = Counter()
    gaps = []
    for (t, ph, ds, pp), (t2, ph2, ds2, pp2) in zip(seq, seq[1:]):
        gaps.append(t2 - t)
        if all(d == fam.b - 1 for d in ds):
            trans['%d/p -> %d/p%+d  %s' % (ph, ph2, len(ds2) - len(ds),
                                           'zero' if not any(ds2) else
                                           ''.join(map(str, ds2))[:8])] += 1
    fills = []
    for (t, ph, ds, pp), (t2, _, _, _) in zip(seq, seq[1:]):
        if all(d == fam.b - 1 for d in ds):
            fills.append((len(ds), t2 - t))
    from fillcost import verdict
    v, r = verdict(fills)
    # Per PHASE, because the phases do different things and a row can have a
    # cheap handover in one phase and a nested fill in another -- that second
    # case is a register, not a phase cycle, and mixing the widths of all
    # phases into one ratio hides it.  A phase's fill has to be an ARM, so
    # what matters is how many anchor visits the arm's replay must cross:
    # bounded is a rule, growing with the width is rung three.
    byph = {}
    for i, (t, ph, ds, pp) in enumerate(seq):
        if not all(d == fam.b - 1 for d in ds):
            continue
        for j in range(i + 1, len(seq)):
            if seq[j][1:3] == (ph, ds):
                continue
            byph.setdefault((ph, len(ds)), j - i)
            break
    per_phase, worst = {}, 'affine'
    for ph in range(len(phases)):
        pts = sorted((k, g) for (p, k), g in byph.items() if p == ph)
        pv, pr = verdict(pts)
        per_phase[ph] = {'visit_gap_by_width': pts[:8], 'verdict': pv,
                         'ratio': pr}
        if pv == 'exponential':
            worst = 'exponential'
        elif pv == 'superlinear' and worst == 'affine':
            worst = 'superlinear'
    max_gap = max(byph.values()) if byph else None
    return {'spec': spec, 'verdict': v, 'per_digit_ratio': r,
            'fill_arm_verdict': worst,
            'max_fill_visit_gap': max_gap,
            'per_phase': per_phase,
            'n_phases': len(phases),
            'phases': [list(p) for p in phases],
            'visits': len(obs), 'read': len(seq), 'unread': n_unread,
            'read_frac': round(len(seq) / len(obs), 3),
            'max_member_gap_steps': max(gaps) if gaps else None,
            'median_member_gap_steps': (int(statistics.median(gaps))
                                        if gaps else None),
            'fills': fills[:8], 'transitions': dict(trans),
            'base': fam.b, 'digits': [list(d) for d in fam.digs],
            'anchor': chr(65 + fam.q) + str(fam.h),
            'seconds': round(time.time() - t0, 1)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--spec')
    ap.add_argument('--list')
    ap.add_argument('--out')
    ap.add_argument('--steps', type=int, default=200000)
    ap.add_argument('--which', type=int, default=0)
    ap.add_argument('--verbose', action='store_true')
    a = ap.parse_args()
    specs = [a.spec] if a.spec else \
        [l.split()[0] for l in open(a.list) if l.strip()]
    out = []
    for s in specs:
        try:
            r = measure(s, a.steps, which=a.which)
        except Exception as e:                             # noqa: BLE001
            r = {'spec': s, 'verdict': 'crash: %s' % type(e).__name__,
                 'detail': str(e)[:160]}
        out.append(r)
        print('%-32s phases=%s read=%-5s fill_arm=%-12s max_gap=%-5s %s'
              % (s, r.get('n_phases'), r.get('read_frac'),
                 r.get('fill_arm_verdict', r['verdict']),
                 r.get('max_fill_visit_gap'),
                 [(k, d['verdict']) for k, d in
                  sorted((r.get('per_phase') or {}).items())]))
        if a.verbose:
            print(json.dumps(r, indent=1))
        sys.stdout.flush()
    if a.out:
        with open(a.out, 'w') as f:
            for r in out:
                f.write(json.dumps(r) + '\n')
    print('\n== phases needed ==')
    for k, n in Counter(r.get('n_phases') for r in out).most_common():
        print('  %-6s %3d' % (k, n))
    print('== is every phase fill an ARM (bounded anchor stops)? ==')
    for k, n in Counter(r.get('fill_arm_verdict', r['verdict'])
                        for r in out).most_common():
        print('  %-14s %3d' % (k, n))
    ok = [r for r in out if r.get('fill_arm_verdict') == 'affine'
          and (r.get('max_fill_visit_gap') or 99) <= 8]
    print('  cycle closes with every fill inside 8 anchor stops: %d' % len(ok))


if __name__ == '__main__':
    main()
