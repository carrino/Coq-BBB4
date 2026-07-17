#!/usr/bin/env python3
"""Coverage report: which BBB holdout machines have a Coq theorem.

Cross-checks tools/bulk_manifest.tsv (the generated theorem table)
against the BBB repo's holdout list and committed certificates:

  - every manifest machine must be on the holdout list;
  - every holdout machine is classified: Coq-proven / C-certified
    only (by cert type) / open upstream.

Usage: BBB_REPO=/path/to/BBB python3 tools/check_coverage.py
"""
import collections
import glob
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
BBB = os.environ.get("BBB_REPO", os.path.join(ROOT, "..", "BBB"))


def cert_types():
    """machine -> set of committed C cert types (all results dirs)."""
    out = collections.defaultdict(set)
    for d in sorted(glob.glob(BBB + "/results/certs*")) + [BBB + "/results"]:
        for f in glob.glob(d + "/*.cert"):
            m = ty = None
            for line in open(f):
                if line.startswith("machine "):
                    m = line.split()[1]
                elif line.startswith("type "):
                    ty = line.split()[1]
            if m and ty:
                out[m].add(ty)
    return out


def main():
    holdouts = [l.strip() for l in open(BBB + "/BBB4_holdouts_3713.txt")
                if l.strip()]
    hset = set(holdouts)
    manifest = {}
    qh_count = 0
    for mfname in ("bulk_manifest.tsv", "tcyc_manifest.tsv",
                   "bulkr_manifest.tsv", "wrap_manifest.tsv",
                   "counters_manifest.tsv", "fuel_manifest.tsv",
                   "irules_manifest.tsv", "repwl_manifest.tsv",
                   "drift_manifest.tsv"):
        path = os.path.join(HERE, mfname)
        if not os.path.exists(path):
            continue
        with open(path) as f:
            next(f)
            for line in f:
                parts = line.rstrip("\n").split("\t")
                manifest[parts[0]] = parts[1]
                if mfname == "wrap_manifest.tsv":
                    qh_count += 1
    stray = [m for m in manifest if m not in hset]
    if stray:
        print("ERROR: %d proven machines NOT on the holdout list:" % len(stray))
        for m in stray[:10]:
            print(" ", m)
        sys.exit(1)

    types = cert_types()
    open_machines = [m for m in holdouts if m not in types]
    remaining = collections.Counter()
    for m in holdouts:
        if m in manifest or m in open_machines:
            continue
        remaining[tuple(sorted(types[m]))] += 1

    print("holdout list:          %5d" % len(holdouts))
    print("Coq-proven:            %5d  (%d never-QH, %d QH with exact score)"
          % (len(manifest), len(manifest) - qh_count, qh_count))
    print("open upstream:         %5d" % len(open_machines))
    print("C-certified, no Coq:   %5d"
          % (len(holdouts) - len(manifest) - len(open_machines)))
    print("\nremaining by C cert type:")
    for k, v in sorted(remaining.items(), key=lambda kv: -kv[1]):
        print("  %5d  %s" % (v, ",".join(k)))
    print("\nopen machines (no certificate upstream):")
    for m in open_machines:
        print(" ", m)


if __name__ == "__main__":
    main()
