#!/usr/bin/env python3
"""RepWL census-tier sweep over the never-QH residue core (UNTRUSTED).

The 31,758 machines of tools/wrap_residue_survivors.txt are the
census residue's hard never-QH core (wrap-QH machines excluded).  The
planned census RepWL tier is parameter-closed: fixed (L, T, t) block /
threshold / prefix rungs and the in-Coq rules-(a)/(b) search over the
five built-in measures (no per-machine certificates).  This sweep
mirrors that tier exactly through tools/repwl_prover.py (the Python
mirror of Checkers/RepWL.v) with per_state = {} -- a machine counts
as caught only if the built-in measure vocabulary discharges every
state, which is what the in-Coq search can find.

The node cap mirrors the census tier's closure fuel budget: the walk
pays up to [fuel] pops per FAILING rung, so catches needing closures
beyond the cap are not worth their walk cost and stay deferred.
Rungs run t=0 across the (L, T) grid first (cheapest, and measured to
carry most of the yield), then the t > 0 variants; the recorded
first-catch rung feeds the census ladder's ordering.

Results stream to the output TSV as they arrive (crash-safe); re-runs
resume past already-swept machines.

Usage: sweep_repwl_residue.py [SURVIVORS_TXT] [OUT_DIR] [NPROC]
"""
import os
import sys
import multiprocessing as mp

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import repwl_prover as rp

# t = 0 only: the full 16-rung grid measured ZERO catches at t > 0
# over the first ~750 machines while quadrupling the per-miss cost,
# so the census ladder ships without prefix rungs.  The cap mirrors
# the census rw_fuel budget (8192 >= 2*4000 + 1); every catch so far
# sits under 1,700 nodes, while completed-but-failing closures near a
# larger cap dominate the sweep cost.
RUNGS = [(2, 2, 0), (2, 3, 0), (3, 2, 0), (4, 2, 0)]
CAP = 4000


def try_rung(tbl, L, T, t):
    r = rp.build_closure(tbl, L, T, t, cap=CAP)
    if r is None:
        return None
    a0, seen = r
    adj = {a: rp.rw_succs(tbl, L, T, a) for a in seen}
    states = sorted({a[0] for a in seen} | rp.warmup_states(tbl, t))
    for qq in states:
        comps = rp.procedure(tbl, seen, adj, qq, rp.MEAS)
        if comps is None or not rp.lex_check(tbl, adj, seen, qq, comps):
            return None
    return len(seen)


def work(m):
    try:
        tbl = rp.parse(m)
        for (L, T, t) in RUNGS:
            ns = try_rung(tbl, L, T, t)
            if ns is not None:
                return (m, L, T, t, ns)
        return (m, None, None, None, None)
    except Exception as e:
        return (m, "ERR", repr(e), None, None)


def main():
    src = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
        HERE, "wrap_residue_survivors.txt")
    outdir = sys.argv[2] if len(sys.argv) > 2 else HERE
    nproc = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    out_path = os.path.join(outdir, "repwl_sweep_stream.tsv")
    done = set()
    if os.path.exists(out_path):
        with open(out_path) as f:
            for line in f:
                if line.strip():
                    done.add(line.split("\t")[0])
    machines = [l.strip() for l in open(src)
                if l.strip() and l.strip() not in done]
    print(f"sweeping {len(machines)} (skipping {len(done)} done)",
          flush=True)
    ncaught = 0
    with open(out_path, "a") as out, mp.Pool(nproc) as pool:
        for i, r in enumerate(pool.imap_unordered(work, machines,
                                                  chunksize=4)):
            m, L, T, t, ns = r
            if L is None:
                out.write(f"{m}\tmiss\t\t\t\n")
            elif L == "ERR":
                out.write(f"{m}\terr\t{T}\t\t\n")
            else:
                ncaught += 1
                out.write(f"{m}\thit\t{L},{T},{t}\t{ns}\t\n")
            out.flush()
            if (i + 1) % 1000 == 0:
                print(f"{i+1}/{len(machines)} caught={ncaught}", flush=True)
    print(f"DONE swept={len(machines)} caught_this_run={ncaught}",
          flush=True)


if __name__ == "__main__":
    main()
