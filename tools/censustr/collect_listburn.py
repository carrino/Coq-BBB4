#!/usr/bin/env python3
"""Collect list-burn shard outputs into verdict counts + a survivors list.

UNTRUSTED tooling: zips each ListBurn_XX.out's printed tag list against
its ListBurn_XX.machines file.  Tag 5 (UNKNOWN) machines are the
survivors, written one per line to stdout or --survivors.

Usage: collect_listburn.py DIR [--survivors FILE]
"""

import argparse
import glob
import os
import re
import sys

TAGS = ["halt", "neverqh", "qh", "leaf", "deferred", "UNKNOWN"]


def parse_tags(path):
    """All verdicts printed by a shard, in order.

    A shard prints ONE list per sublist (gen_listburn emits a
    Time Definition + Compute per chunk), so a shard killed part way
    through still yields every chunk it finished -- concatenate them.
    A missing .out is an unstarted shard: no verdicts, not an error."""
    if not os.path.exists(path):
        return []
    text = open(path).read()
    tags = []
    for m in re.finditer(r"=\s*\[(.*?)\]\s*:\s*list nat", text, re.S):
        tags.extend(int(x) for x in re.findall(r"\d+", m.group(1)))
    return tags


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("dir")
    ap.add_argument("--survivors")
    ap.add_argument(
        "--unburned",
        help="write ONLY the machines no shard reached "
             "(failed or unrun shards) here, so they can be "
             "re-burned without redoing the whole list")
    args = ap.parse_args()

    counts = [0] * 6
    nunburned = 0
    survivors = []
    unburned_all = []
    shards = sorted(glob.glob(os.path.join(args.dir, "ListBurn_*.machines")))
    if not shards:
        raise SystemExit(f"no ListBurn_*.machines in {args.dir}")
    for mfile in shards:
        out = mfile[: -len(".machines")] + ".out"
        machines = [l.strip() for l in open(mfile) if l.strip()]
        tags = parse_tags(out)
        if len(tags) > len(machines):
            raise SystemExit(
                f"{out}: {len(tags)} verdicts vs {len(machines)} machines"
            )
        for m, t in zip(machines, tags):
            counts[t] += 1
            if t == 5:
                survivors.append(m)
        # A shard that died or has not run yet leaves a tail with no
        # verdict.  Those machines are UNDECIDED, not decided-unknown:
        # they stay on the burn-down list (else a crash would silently
        # drop machines from the census), and they are counted apart so
        # the run's coverage is visible.
        unburned = machines[len(tags):]
        survivors.extend(unburned)
        unburned_all.extend(unburned)
        nunburned += len(unburned)

    total = sum(counts)
    print(f"burned: {total}")
    for i, name in enumerate(TAGS):
        pct = (100.0 * counts[i] / total) if total else 0.0
        print(f"  {name:9s} {counts[i]:8d}  ({pct:5.1f}%)")
    if nunburned:
        print(f"  {'UNBURNED':9s} {nunburned:8d}  "
              f"(shards incomplete; kept as survivors)")
    print(f"survivors (next list): {len(survivors)}")
    if args.unburned:
        with open(args.unburned, "w") as f:
            f.write("\n".join(unburned_all))
            if unburned_all:
                f.write("\n")
        print(f"unburned -> {args.unburned}")
    if args.survivors:
        with open(args.survivors, "w") as f:
            f.write("\n".join(survivors) + ("\n" if survivors else ""))
        print(f"survivors -> {args.survivors}")


if __name__ == "__main__":
    main()
