#!/usr/bin/env python3
"""Opportunistic sweep: try the n-gram/rank pipeline on the never-QH
machines the upstream harness boarded with STRONGER cert types
(fuel/drift/rwl*/irules).  Our pipeline is slightly stronger than the
upstream neverqh_rank prover in three ways -- relaxed pattern-window
constraints, free t choice, and free n choice -- so some machines may
fall out.  Every hit is a machine the existing Coq checker can board
with zero new checker code.

Writes remaining_hits.tsv: machine, n, t, contexts.
"""
import collections
import glob
import os
import sys
import time
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import bulk_prover as bp

BBB = os.environ.get("BBB_REPO", os.path.join(HERE, "..", "..", "BBB"))

NEVERQH_TYPES = {"neverqh_fuel", "neverqh_drift", "neverqh_rwl",
                 "neverqh_rwlrank", "neverqh_rwlsilent"}


def collect_targets():
    """never-QH machines with no rank/ngram cert: fuel/drift/rwl* by
    type, plus irules certs claiming neverqh."""
    info = collections.defaultdict(dict)
    for d in sorted(glob.glob(BBB + "/results/certs*")):
        for f in glob.glob(d + "/*.cert"):
            m = ty = status = None
            for line in open(f):
                p = line.split()
                if not p:
                    continue
                if p[0] == "machine":
                    m = p[1]
                elif p[0] == "type":
                    ty = p[1]
                elif p[0] == "claim_status":
                    status = p[1]
            if m and ty:
                info[m][ty] = status
    boarded = set()
    with open(os.path.join(HERE, "bulk_manifest.tsv")) as f:
        next(f)
        for line in f:
            boarded.add(line.split("\t")[0])
    targets = []
    for m, tys in info.items():
        if m in boarded or "tcycler" in tys:
            continue
        if NEVERQH_TYPES & set(tys):
            targets.append(m)
        elif "irules" in tys and tys.get("irules") == "neverqh":
            targets.append(m)
    return sorted(targets)


def work(mtext):
    st = time.time()
    for n in (2, 3, 4, 5):
        r = bp.decide(mtext, n, {},
                      t_cands=(0, 256, 4096, 65536, 500000))
        if r is not None:
            t, seen, lset, rset, comps, rounds = r
            return (mtext, n, t, len(seen), time.time() - st)
    return (mtext, None, None, None, time.time() - st)


def main():
    targets = collect_targets()
    print(len(targets), "targets", flush=True)
    hits = 0
    out = open(os.path.join(HERE, "remaining_hits.tsv"), "w")
    t0 = time.time()
    with Pool(3) as pool:
        for i, (m, n, t, ns, el) in enumerate(pool.imap_unordered(work, targets)):
            if n is not None:
                hits += 1
                out.write("%s\t%d\t%d\t%d\n" % (m, n, t, ns))
                out.flush()
                print("HIT", m, "n=%d t=%d ctxs=%d" % (n, t, ns), flush=True)
            if (i + 1) % 50 == 0:
                print("%d/%d hits=%d (%.0fs)" % (i + 1, len(targets), hits,
                                                 time.time() - t0), flush=True)
    out.close()
    print("DONE: %d hits of %d" % (hits, len(targets)))


if __name__ == "__main__":
    main()
