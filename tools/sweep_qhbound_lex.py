#!/usr/bin/env python3
"""Full lex-gated QHBound sweep over qhbound_survivors.txt (UNTRUSTED).

Mirror of the census qhbound-lex tier: for each wrap-QH machine the
plain acyclicity gate rejects, search a lexicographic liveness
certificate over the wrapped closure (gen_qhbound_lex.find_lex --
bulk_prover.procedure with the count-of-1s measures, n in (2,3,4),
t in (64,256,1024)).  A hit means ngram_check_qhbound_lex with the
in-Coq RankSearch certificates decides the machine at census-walk
time, so it can leave the deferred list.

Writes qhbound_lex_caught.tsv (machine, q, s, n, t) and
qhbound_lex_survivors.txt.

Usage: sweep_qhbound_lex.py [SURVIVORS_TXT] [OUT_DIR] [NPROC]
"""
import os
import sys
import multiprocessing as mp

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

# gen_qhbound_lex.py runs its emitter at import time; load only the
# search half (everything above the CLI block).
_src = open(os.path.join(HERE, "gen_qhbound_lex.py")).read()
_g = {}
exec(_src.split("ms=[l.strip()")[0], _g)
find_lex = _g["find_lex"]


def work(m):
    try:
        r = find_lex(m)
        if r is None:
            return (m, None)
        qq, s, n, t = r[0], r[1], r[2], r[3]
        return (m, (qq, s, n, t))
    except Exception:
        return (m, None)


def main():
    src = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
        HERE, "qhbound_survivors.txt")
    outdir = sys.argv[2] if len(sys.argv) > 2 else HERE
    nproc = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    machines = [l.strip() for l in open(src) if l.strip()]
    caught = []
    survivors = []
    with mp.Pool(nproc) as pool:
        for i, (m, r) in enumerate(pool.imap_unordered(work, machines,
                                                       chunksize=16)):
            if r is None:
                survivors.append(m)
            else:
                caught.append((m,) + r)
            if (i + 1) % 2000 == 0:
                print(f"{i+1}/{len(machines)} lex={len(caught)}", flush=True)
    caught.sort()
    survivors.sort()
    with open(os.path.join(outdir, "qhbound_lex_caught.tsv"), "w") as f:
        f.write("machine\tquiet_state\ts\tn\tt\n")
        for m, qq, s, n, t in caught:
            f.write(f"{m}\t{chr(65+qq)}\t{s}\t{n}\t{t}\n")
    open(os.path.join(outdir, "qhbound_lex_survivors.txt"), "w").write(
        "\n".join(survivors) + ("\n" if survivors else ""))
    print(f"DONE total={len(machines)} lex_caught={len(caught)} "
          f"survivors={len(survivors)}")


if __name__ == "__main__":
    main()
