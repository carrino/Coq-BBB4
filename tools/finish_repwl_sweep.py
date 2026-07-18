#!/usr/bin/env python3
"""Convert the streaming RepWL sweep output into the census artifacts.

Reads repwl_sweep_stream.tsv (machine / hit|miss|err / "L,T,t" / nseen)
and writes repwl_residue_caught.tsv + repwl_residue_survivors.txt,
restricted to the (L, T, t) rung list and node cap the census ladder
actually ships (drop-listed catches become survivors -- they stay
deferred).  Prints the rung histogram and nseen quantiles that drive
those choices.

Usage: finish_repwl_sweep.py [--rungs L,T,t;L,T,t;...] [--cap N]
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def main():
    rungs = None
    cap = None
    args = sys.argv[1:]
    while args:
        a = args.pop(0)
        if a == "--rungs":
            rungs = {tuple(map(int, r.split(",")))
                     for r in args.pop(0).split(";")}
        elif a == "--cap":
            cap = int(args.pop(0))
        else:
            raise SystemExit(f"unknown arg {a}")
    hits = {}
    nseen = {}
    misses = []
    errs = []
    with open(os.path.join(HERE, "repwl_sweep_stream.tsv")) as f:
        for line in f:
            parts = line.rstrip("\n").split("\t")
            if len(parts) < 2 or not parts[0]:
                continue
            m, st = parts[0], parts[1]
            if st == "hit":
                hits[m] = tuple(map(int, parts[2].split(",")))
                nseen[m] = int(parts[3])
            elif st == "miss":
                misses.append(m)
            else:
                errs.append(m)
    total = len(hits) + len(misses) + len(errs)
    print(f"stream rows: {total} (hit {len(hits)} miss {len(misses)} "
          f"err {len(errs)})")
    hist = {}
    for m, r in hits.items():
        hist[r] = hist.get(r, 0) + 1
    print("rung histogram:")
    for r in sorted(hist):
        print(f"  {r}: {hist[r]}")
    ns = sorted(nseen.values())
    if ns:
        for q in (0.5, 0.9, 0.99, 1.0):
            print(f"  nseen q{q}: {ns[min(len(ns)-1, int(q*len(ns)))]}")
    caught = []
    survivors = list(misses) + list(errs)
    for m, r in sorted(hits.items()):
        if (rungs is not None and r not in rungs) or \
           (cap is not None and nseen[m] > cap):
            survivors.append(m)
        else:
            caught.append((m,) + r + (nseen[m],))
    survivors.sort()
    with open(os.path.join(HERE, "repwl_residue_caught.tsv"), "w") as f:
        f.write("machine\tL\tT\tt\tnseen\n")
        for row in caught:
            f.write("\t".join(map(str, row)) + "\n")
    open(os.path.join(HERE, "repwl_residue_survivors.txt"), "w").write(
        "\n".join(survivors) + ("\n" if survivors else ""))
    print(f"kept {len(caught)} catches; {len(survivors)} survivors")


if __name__ == "__main__":
    main()
