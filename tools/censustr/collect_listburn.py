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
    text = open(path).read()
    # the Compute output: a Coq nat list [t0; t1; ...] (possibly wrapped)
    m = re.search(r"=\s*\[(.*?)\]\s*:\s*list nat", text, re.S)
    if not m:
        # empty list prints as [] too; treat missing as failure
        if re.search(r"=\s*\[\s*\]\s*:\s*list nat", text, re.S):
            return []
        raise SystemExit(f"{path}: no verdict list found (shard failed?)")
    return [int(x) for x in re.findall(r"\d+", m.group(1))]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("dir")
    ap.add_argument("--survivors")
    args = ap.parse_args()

    counts = [0] * 6
    survivors = []
    shards = sorted(glob.glob(os.path.join(args.dir, "ListBurn_*.machines")))
    if not shards:
        raise SystemExit(f"no ListBurn_*.machines in {args.dir}")
    for mfile in shards:
        out = mfile[: -len(".machines")] + ".out"
        machines = [l.strip() for l in open(mfile) if l.strip()]
        tags = parse_tags(out)
        if len(tags) != len(machines):
            raise SystemExit(
                f"{out}: {len(tags)} verdicts vs {len(machines)} machines"
            )
        for m, t in zip(machines, tags):
            counts[t] += 1
            if t == 5:
                survivors.append(m)

    total = sum(counts)
    print(f"total: {total}")
    for i, name in enumerate(TAGS):
        print(f"  {name:9s} {counts[i]:8d}  ({100.0 * counts[i] / total:5.1f}%)")
    if args.survivors:
        with open(args.survivors, "w") as f:
            f.write("\n".join(survivors) + ("\n" if survivors else ""))
        print(f"survivors -> {args.survivors}")


if __name__ == "__main__":
    main()
