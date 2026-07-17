#!/usr/bin/env python3
"""RepWL census-tier sweep over the never-QH residue core (UNTRUSTED).

The 31,758 machines of tools/wrap_residue_survivors.txt are the
census residue's hard never-QH core (wrap-QH machines excluded).  The
planned census RepWL tier is parameter-closed: fixed (L, T) block /
threshold rungs, prefix rungs t, and the in-Coq rules-(a)/(b) search
over the five built-in measures (no per-machine certificates).  This
sweep mirrors that tier exactly through tools/repwl_prover.decide
(the Python mirror of Checkers/RepWL.v) with per_state = {} -- a
machine counts as caught only if the built-in measure vocabulary
discharges every state, which is what the in-Coq search can find.

Writes repwl_residue_caught.tsv (machine, L, T, t, nseen) and
repwl_residue_survivors.txt, plus a per-rung kill histogram on
stdout.  Machines whose closure exceeds the node cap at every rung
are survivors (the census walk cannot afford unbounded closures).

Usage: sweep_repwl_residue.py [SURVIVORS_TXT] [OUT_DIR] [NPROC]
"""
import os
import sys
import multiprocessing as mp

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import repwl_prover as rp

# (L, T) rungs in measured coverage-per-cost order; t rungs mirror the
# rank tier's ladder (Census/Run.v rank_rungs_census).
RUNGS = ((2, 2), (2, 3), (3, 2), (4, 2))
T_CANDS = (0, 64, 256, 1024)
CAP = 50000


def try_rung(tbl, L, T):
    for t in T_CANDS:
        r = rp.build_closure(tbl, L, T, t, cap=CAP)
        if r is None:
            continue
        a0, seen = r
        adj = {a: rp.rw_succs(tbl, L, T, a) for a in seen}
        states = sorted({a[0] for a in seen} | rp.warmup_states(tbl, t))
        ok = True
        for qq in states:
            comps = rp.procedure(tbl, seen, adj, qq, rp.MEAS)
            if comps is None or not rp.lex_check(tbl, adj, seen, qq, comps):
                ok = False
                break
        if ok:
            return t, len(seen)
    return None


def work(m):
    try:
        tbl = rp.parse(m)
        for (L, T) in RUNGS:
            r = try_rung(tbl, L, T)
            if r is not None:
                return (m, L, T, r[0], r[1])
        return (m, None, None, None, None)
    except Exception as e:
        return (m, "ERR", repr(e), None, None)


def main():
    src = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
        HERE, "wrap_residue_survivors.txt")
    outdir = sys.argv[2] if len(sys.argv) > 2 else HERE
    nproc = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    limit = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    machines = [l.strip() for l in open(src) if l.strip()]
    if limit:
        machines = machines[:limit]
    caught = []
    survivors = []
    errs = []
    hist = {}
    with mp.Pool(nproc) as pool:
        for i, r in enumerate(pool.imap_unordered(work, machines,
                                                  chunksize=8)):
            m = r[0]
            if r[1] is None:
                survivors.append(m)
            elif r[1] == "ERR":
                errs.append((m, r[2]))
                survivors.append(m)
            else:
                caught.append(r)
                hist[(r[1], r[2], r[3])] = hist.get((r[1], r[2], r[3]), 0) + 1
            if (i + 1) % 2000 == 0:
                print(f"{i+1}/{len(machines)} caught={len(caught)} "
                      f"survive={len(survivors)}", flush=True)
    caught.sort()
    survivors.sort()
    with open(os.path.join(outdir, "repwl_residue_caught.tsv"), "w") as f:
        f.write("machine\tL\tT\tt\tnseen\n")
        for m, L, T, t, ns in caught:
            f.write(f"{m}\t{L}\t{T}\t{t}\t{ns}\n")
    open(os.path.join(outdir, "repwl_residue_survivors.txt"), "w").write(
        "\n".join(survivors) + ("\n" if survivors else ""))
    print("rung histogram (L,T,t -> kills):")
    for k in sorted(hist):
        print(f"  {k}: {hist[k]}")
    for m, e in errs[:20]:
        print(f"ERR {m}: {e}")
    print(f"DONE total={len(machines)} caught={len(caught)} "
          f"survivors={len(survivors)} errs={len(errs)}")


if __name__ == "__main__":
    main()
