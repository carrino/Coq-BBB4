#!/usr/bin/env python3
"""Which wrap-caught residue machines are QHBound-decidable (UNTRUSTED).

sweep_wrap_residue.py finds the residue machines that are prefix-quiet
quasihalters (QuasiHaltsSt).  The census contract, however, needs
QHBound B: EVERY eventually-quiet state's last visit is <= B, not just
the wrapped one.  The Coq tier ngram_check_qhbound (Wrap.v) supplies it
by adding the engine's PLAIN-ACYCLICITY rank liveness (live_ok /
compute_ranks) over the wrapped closure: if every state that appears in
the closure recurs (its q'-avoiding subgraph is acyclic), the only
quiet states are the ones that vanish by t, so QHBound (S t) holds.

This mirrors that gate exactly -- for every appearing state q', the
subgraph on nodes with state != q' (edges not into q') must be acyclic,
which is exactly when compute_ranks assigns a valid rank and rank_ok
passes.  It searches n in 2..6 for a (q, n, t) where the wrapped
closure is BOTH halt-free AND per-state acyclic.

Reads tools/wrap_residue_caught.tsv (from sweep_wrap_residue.py) and
writes qhbound_caught.tsv (machine, q, s, n, t : QHBound-decidable) and
qhbound_survivors.txt (wrap-QH but needs measure-based liveness, still
undecided at the census contract).

Usage: sweep_qhbound_residue.py [CAUGHT_TSV] [OUT_DIR] [NPROC]
"""
import os
import sys
import multiprocessing as mp

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import bulk_prover as bp

CAND_N = (2, 3, 4, 5, 6)
CAND_T = (64, 256, 1024)


def wrapped_closure(tbl, qq, n, t, cap=200000):
    """(seen, lset, rset, wrapped_tbl) for the halt-free wrapped
    closure, or None."""
    tape = {}
    pos = 0
    q = 0
    for _ in range(t):
        tr = tbl[(q, tape.get(pos, 0))]
        if tr is None:
            return None
        w, d, nq = tr
        tape[pos] = w
        pos += 1 if d == "R" else -1
        q = nq
    if q == qq:
        return None
    tw = dict(tbl)
    tw[(qq, 0)] = None
    tw[(qq, 1)] = None
    minp = min([pos] + list(tape))
    maxp = max([pos] + list(tape))
    Lf = lambda i: tape.get(pos - 1 - i, 0)
    Rf = lambda i: tape.get(pos + 1 + i, 0)
    win = lambda f, d: tuple(f(d + i) for i in range(n))
    depth = max(pos - minp, maxp - pos) + n + 2
    lset = {win(Lf, d) for d in range(1, depth)}
    rset = {win(Rf, d) for d in range(1, depth)}
    a0 = (q, tape.get(pos, 0), win(Lf, 0), win(Rf, 0))
    for _ in range(400):
        seen = set()
        todo = [a0]
        while todo:
            a = todo.pop()
            if a in seen:
                continue
            seen.add(a)
            if len(seen) > cap:
                return None
            q1, s1, lw, rw = a
            tr = tw[(q1, s1)]
            if tr is None:
                continue
            w, d, q2 = tr
            if d == "R":
                for x in (0, 1):
                    rw2 = rw[1:] + (x,)
                    if rw2 in rset:
                        todo.append((q2, rw[0], (w,) + lw[:-1], rw2))
            else:
                for x in (0, 1):
                    lw2 = lw[1:] + (x,)
                    if lw2 in lset:
                        todo.append((q2, lw[0], lw2, (w,) + rw[:-1]))
        newl = {a[2] for a in seen if tw[(a[0], a[1])] and tw[(a[0], a[1])][1] == "R"}
        newr = {a[3] for a in seen if tw[(a[0], a[1])] and tw[(a[0], a[1])][1] == "L"}
        if newl <= lset and newr <= rset:
            if any(tw[(a[0], a[1])] is None for a in seen):
                return None
            return seen, lset, rset, tw
    return None


def _has_cycle(nodes, adj):
    color = {v: 0 for v in nodes}
    for s in nodes:
        if color[s] != 0:
            continue
        stack = [(s, iter(adj.get(s, ())))]
        color[s] = 1
        while stack:
            v, it = stack[-1]
            adv = False
            for w in it:
                cw = color.get(w, 0)
                if cw == 1:
                    return True
                if cw == 0:
                    color[w] = 1
                    stack.append((w, iter(adj.get(w, ()))))
                    adv = True
                    break
            if not adv:
                color[v] = 2
                stack.pop()
    return False


def live_ok(seen, lset, rset, tw):
    """The Coq live_ok gate: every appearing state's q'-avoiding
    subgraph is acyclic."""
    succ = {}
    for a in seen:
        q1, s1, lw, rw = a
        tr = tw[(q1, s1)]
        out = []
        if tr:
            w, d, q2 = tr
            if d == "R":
                for x in (0, 1):
                    rw2 = rw[1:] + (x,)
                    b = (q2, rw[0], (w,) + lw[:-1], rw2)
                    if rw2 in rset and b in seen:
                        out.append(b)
            else:
                for x in (0, 1):
                    lw2 = lw[1:] + (x,)
                    b = (q2, lw[0], lw2, (w,) + rw[:-1])
                    if lw2 in lset and b in seen:
                        out.append(b)
        succ[a] = out
    for qq in set(a[0] for a in seen):
        sub = [a for a in seen if a[0] != qq]
        subset = set(sub)
        adj = {a: [b for b in succ[a] if b[0] != qq and b in subset] for a in sub}
        if _has_cycle(sub, adj):
            return False
    return True


def find_qhbound(m):
    """(q, s, n, t) for a valid QHBound cert, or None."""
    tbl = bp.parse(m)
    tape = {}
    pos = 0
    q = 0
    vis = set()
    for _ in range(1024):
        vis.add(q)
        tr = tbl[(q, tape.get(pos, 0))]
        if tr is None:
            break
        w, d, nq = tr
        tape[pos] = w
        pos += 1 if d == "R" else -1
        q = nq
    for qq in sorted(vis, key=lambda x: (x == 0, x)):
        for n in CAND_N:
            for t in CAND_T:
                r = wrapped_closure(tbl, qq, n, t)
                if r is None:
                    continue
                if not live_ok(*r):
                    continue
                # last visit of qq strictly before t
                tp = {}
                p = 0
                qc = 0
                s = None
                for i in range(t):
                    if qc == qq:
                        s = i
                    w, d, nq = tbl[(qc, tp.get(p, 0))]
                    tp[p] = w
                    p += 1 if d == "R" else -1
                    qc = nq
                if s is None or s >= t:
                    continue
                return (qq, s, n, t)
    return None


def work(m):
    try:
        return (m, find_qhbound(m))
    except Exception:
        return (m, None)


def main():
    caught_tsv = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
        HERE, "wrap_residue_caught.tsv")
    outdir = sys.argv[2] if len(sys.argv) > 2 else HERE
    nproc = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    os.makedirs(outdir, exist_ok=True)
    machines = []
    with open(caught_tsv) as f:
        next(f)
        for line in f:
            machines.append(line.split("\t")[0])
    caught = []
    survivors = []
    with mp.Pool(nproc) as pool:
        for i, (m, r) in enumerate(pool.imap_unordered(work, machines, chunksize=16)):
            if r is None:
                survivors.append(m)
            else:
                caught.append((m,) + r)
            if (i + 1) % 5000 == 0:
                print(f"{i+1}/{len(machines)} qhbound={len(caught)} "
                      f"needs_measures={len(survivors)}", flush=True)
    caught.sort()
    survivors.sort()
    with open(os.path.join(outdir, "qhbound_caught.tsv"), "w") as f:
        f.write("machine\tquiet_state\ts\tn\tt\n")
        for m, qq, s, n, t in caught:
            f.write(f"{m}\t{chr(65+qq)}\t{s}\t{n}\t{t}\n")
    open(os.path.join(outdir, "qhbound_survivors.txt"), "w").write(
        "\n".join(survivors) + "\n")
    print(f"DONE wrap_caught={len(machines)} qhbound_decidable={len(caught)} "
          f"needs_measure_liveness={len(survivors)}")


if __name__ == "__main__":
    main()
