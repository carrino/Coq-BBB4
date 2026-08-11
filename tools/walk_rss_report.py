#!/usr/bin/env python3
"""Summarise census_probes/walk-rss.tsv -- the per-unit peak RSS and CPU
the walk recorded (Makefile, WALK_RSS).

Why this exists.  docs/CENSUS_RUNTIME.md turns the "<1 h on regular
hardware" goal into ONE number: per-unit peak RSS, because

    WALK_JOBS = min(cores, (RAM - 2 GB) / RSS_per_unit)

and on 8 cores / 32 GB the difference between 6.8 GB and 3.75 GB per
unit is the difference between 4 jobs (1 h 43 m) and 8 jobs (~52 m).
The 6.8 GB in the Makefile is ONE unit measured by hand in July 2026;
the distribution over the other 143 has never been recorded.  This
prints it, and answers the question the number exists to answer: how
many jobs does THIS walk's memory profile support on a given box.

Usage:
  python3 tools/walk_rss_report.py [FILE] [--cores N] [--ram-gb N] [--top N]

Untrusted build-hygiene tooling: no proof weight.
"""
import argparse
import os
import re
import sys

DEFAULT = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       os.pardir, 'census_probes', 'walk-rss.tsv')
RESERVE_GB = 2.0          # the Makefile's headroom term


def unit_of(cmd):
    """Last .v path on the recorded coqc command line."""
    m = re.findall(r'(\S+\.v)\b', cmd)
    return m[-1] if m else cmd.strip()


def layer_of(unit):
    b = os.path.basename(unit)
    for pfx, name in (('Run_Split_', 'Run_Split_<tag>'),
                      ('Run_Split2', 'Run_Split2'), ('Run_Split', 'Run_Split'),
                      ('GG_1LC_', 'GG_1LC'), ('GGH_', 'GGH'), ('G_', 'G'),
                      ('Census_Theorem', 'theorem')):
        if b.startswith(pfx):
            return name
    return 'other'


# the walk's layer order (Makefile, _census-walk).  Each layer is a
# BARRIER: xargs -P returns before the next `ls | xargs' starts, so a
# layer costs its makespan, not its average.
LAYER_ORDER = ['Run_Split', 'Run_Split2', 'Run_Split_<tag>', 'GG_1LC',
               'GGH', 'G', 'theorem', 'other']


def makespan(times, jobs):
    """Longest-processing-time list schedule onto `jobs` slots."""
    slots = [0.0] * max(1, jobs)
    for t in sorted(times, reverse=True):
        i = min(range(len(slots)), key=lambda k: slots[k])
        slots[i] += t
    return max(slots)


def schedule(rows, jobs):
    """Predicted wall for the whole layered walk at `jobs` parallelism."""
    per = {}
    for u, (r, w, c) in rows.items():
        per.setdefault(layer_of(u), []).append(c)
    return sum(makespan(per[L], jobs) for L in LAYER_ORDER if L in per)


def pct(xs, p):
    if not xs:
        return 0.0
    s = sorted(xs)
    i = min(len(s) - 1, int(round((p / 100.0) * (len(s) - 1))))
    return s[i]


def main():
    ap = argparse.ArgumentParser(add_help=False)
    ap.add_argument('file', nargs='?', default=DEFAULT)
    ap.add_argument('--cores', type=int, default=os.cpu_count() or 4)
    ap.add_argument('--ram-gb', type=float, default=None)
    ap.add_argument('--top', type=int, default=10)
    a = ap.parse_args()

    if a.ram_gb is None:
        a.ram_gb = 32.0
        try:
            with open('/proc/meminfo') as f:
                for line in f:
                    if line.startswith('MemTotal:'):
                        a.ram_gb = int(line.split()[1]) / 1048576.0
        except OSError:
            pass

    if not os.path.exists(a.file):
        print(f"no walk-rss record at {a.file}\n"
              f"  a walk records one automatically: make census-verify\n"
              f"  (needs /usr/bin/time -- apt-get install time)", file=sys.stderr)
        return 2

    rows = {}   # unit -> (rss_gb, wall_s, user_s); last record wins (resumes)
    bad = 0
    with open(a.file) as f:
        for line in f:
            parts = line.rstrip('\n').split('\t', 3)
            if len(parts) < 4 or parts[0] == 'peak_rss_kb':
                continue
            try:
                rss, wall, user = (float(parts[0]) / 1048576.0,
                                   float(parts[1]), float(parts[2]))
            except ValueError:
                bad += 1
                continue
            rows[unit_of(parts[3])] = (rss, wall, user)

    if not rows:
        print(f"{a.file}: no usable records ({bad} unparsable lines)",
              file=sys.stderr)
        return 2

    rss = [v[0] for v in rows.values()]
    wall = sum(v[1] for v in rows.values())
    user = sum(v[2] for v in rows.values())
    peak = max(rss)

    print(f"walk units recorded : {len(rows)}"
          + (f"  ({bad} unparsable lines skipped)" if bad else ""))
    print(f"peak RSS  max/p90/median/min : "
          f"{peak:.2f} / {pct(rss, 90):.2f} / {pct(rss, 50):.2f} / "
          f"{min(rss):.2f} GB")
    print(f"core-time (user, summed)     : {user / 60:.1f} min")
    print(f"unit wall (summed)           : {wall / 60:.1f} min")

    print(f"\nby layer (units, max RSS, core-min):")
    layers = {}
    for u, (r, w, c) in rows.items():
        L = layers.setdefault(layer_of(u), [0, 0.0, 0.0])
        L[0] += 1
        L[1] = max(L[1], r)
        L[2] += c
    for name, (n, r, c) in sorted(layers.items(), key=lambda kv: -kv[1][2]):
        print(f"  {name:<16} {n:>4} units   {r:>6.2f} GB   {c / 60:>7.1f} min")

    print(f"\ntop {a.top} by peak RSS:")
    for u, (r, w, c) in sorted(rows.items(), key=lambda kv: -kv[1][0])[:a.top]:
        print(f"  {r:>6.2f} GB  {c / 60:>7.1f} core-min  {os.path.basename(u)}")

    print(f"\nWALK_JOBS this profile supports "
          f"({a.cores} cores, {a.ram_gb:.0f} GB):")
    usable = a.ram_gb - RESERVE_GB
    for label, r in (("measured max", peak), ("measured p90", pct(rss, 90))):
        j = max(1, min(a.cores, int(usable / r))) if r > 0 else a.cores
        print(f"  {label:<13} {r:>5.2f} GB/unit -> WALK_JOBS={j} "
              f"-> ~{schedule(rows, j) / 60:.0f} min wall")
    print(f"  set it: make census-verify WALK_RSS_GB={peak:.1f}"
          f"   (Makefile default assumes 7)")

    print(f"\npredicted wall by job count (layer barriers modelled, "
          f"LPT schedule of the measured per-unit CPU):")
    ideal = user
    jobs_hi = 8
    for j in (1, 2, 4, 6, 8, 12, 16):
        w = schedule(rows, j)
        print(f"  {j:>3} jobs  {w / 60:>7.1f} min"
              f"   ({ideal / j / w:.0%} of perfect scaling)")
    # WHERE the gap is, rather than a guess about it.  This used to
    # assert "Run_Split and Run_Split2 are one unit each and
    # Run_Split_<tag> is seven, so no job count helps those layers" --
    # true, and irrelevant: measured, those three layers are 1.2 core-min
    # between them and cannot account for a 17-minute gap.  A layer's
    # wall can never go below its LONGEST SINGLE UNIT however many cores
    # you have, so that is what to print.
    print(f"\nwhere the scaling goes, per layer (at {jobs_hi} jobs):")
    per = {}
    for u, (r, w, c) in rows.items():
        per.setdefault(layer_of(u), []).append((c, u))
    print(f"  {'layer':<18}{'core-min':>9}{'makespan':>10}{'longest unit':>13}"
          f"   floor set by")
    for L in LAYER_ORDER:
        if L not in per:
            continue
        ts = [c for c, _ in per[L]]
        mk = makespan(ts, jobs_hi)
        cmax, umax = max(per[L])
        why = "its longest unit" if abs(mk - cmax) < 1e-6 else "load spread"
        print(f"  {L:<18}{sum(ts)/60:>9.1f}{mk/60:>10.1f}{cmax/60:>10.1f} min"
              f"   {why} ({umax})")
    print("  -- a layer whose floor is 'its longest unit' cannot be sped up\n"
          "     by more cores at all; only splitting that unit helps\n"
          "     (tools/gen_gsplit_heavy.py).  That is the M3 target, and it\n"
          "     is NOT the tiny Run_Split layers.")
    return 0


if __name__ == '__main__':
    sys.exit(main())
