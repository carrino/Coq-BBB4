#!/usr/bin/env python3
"""Sweep decide() over all neverqh_rank + neverqh_ngram certs and
record which machines the (extended) Python prover can certify, with
which parameters.  Output: TSV machine, n, t, |seen|, items."""
import glob
import os
import sys
import time
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import bulk_prover as bp

BBB = os.environ.get("BBB_REPO", os.path.join(HERE, "..", "..", "BBB"))


def work(path):
    mtext, n, per_state = bp.parse_cert_measures(path)
    st = time.time()
    r = bp.decide(mtext, n, per_state)
    el = time.time() - st
    if r is None:
        return (mtext, n, None, el)
    t, seen, lset, rset, comps = r
    items = sum(sum(len(c[1]) if c[0] == "rank" else len(c[4]) + len(c[5])
                    for c in cl) for cl in comps.values())
    return (mtext, n, (t, len(seen), items), el)


def main():
    files = sorted(glob.glob(BBB + "/results/certs_rank/*.cert")) + \
        sorted(glob.glob(BBB + "/results/certs_neverqh/*.cert"))
    seen_m = set()
    uniq = []
    for f in files:
        m = os.path.basename(f)[:-5]
        if m not in seen_m:
            seen_m.add(m)
            uniq.append(f)
    print(f"{len(uniq)} machines", flush=True)
    out = open(os.path.join(HERE, "sweep_results.tsv"), "w")
    t0 = time.time()
    nok = nfail = 0
    with Pool(4) as pool:
        for i, (mtext, n, r, el) in enumerate(pool.imap_unordered(work, uniq, chunksize=8)):
            if r is None:
                nfail += 1
                out.write(f"{mtext}\t{n}\tFAIL\t\t\t{el:.2f}\n")
            else:
                nok += 1
                t, nseen, items = r
                out.write(f"{mtext}\t{n}\tOK\t{t}\t{nseen}\t{items}\t{el:.2f}\n")
            if (i + 1) % 100 == 0:
                out.flush()
                print(f"{i+1}/{len(uniq)} ok={nok} fail={nfail} "
                      f"({time.time()-t0:.0f}s)", flush=True)
    out.close()
    print(f"DONE ok={nok} fail={nfail} in {time.time()-t0:.0f}s", flush=True)


if __name__ == "__main__":
    main()
