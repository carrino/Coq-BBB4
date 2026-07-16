#!/usr/bin/env python3
"""Sweep the census residue for prefix-quiet quasihalters (UNTRUSTED).

The v2 census deferred list is D_census = 3,713 holdouts + 52,326
residue.  A large fraction of the residue are QUASIHALTERS: one state
goes quiet in the prefix and the machine then runs forever without it.
Each is witnessed by the halt-redirect construction the Coq checker
`ngram_check_quiet` (theories/Checkers/Wrap.v) verifies: wrap the quiet
state to halt, and a halt-free n-gram closure of the wrapped machine
from the real machine's step-t configuration proves the state never
fires after t.

This tool (a) materializes the residue from the committed Deferred
tables minus the holdout list, (b) runs the wrapped-closure search over
it mirroring the Coq checker's premise EXACTLY (same closure the
verifier re-builds, and the s < t / q-not-revisited-in-(s,t] side
conditions), and (c) writes the caught machines (with their
(q, s, n, t) parameters, ready for gen_residue_wrap.py) and the
survivors -- the residue's hard never-QH core.

Every catch is UNTRUSTED: the Coq wrap checker re-derives the closure
and only its `= true` carries soundness.  On a 414-machine random
sample every catch re-verified through the Coq checker under
vm_compute.

Usage: sweep_wrap_residue.py [OUT_DIR] [NPROC]
  OUT_DIR/residue.txt    all 52,326 residue machines
  OUT_DIR/caught.tsv     machine \t q \t s \t n \t t   (wrap-decidable)
  OUT_DIR/survivors.txt  the residue that survives the wrap sweep
"""
import glob
import os
import re
import sys
import multiprocessing as mp

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import bulk_prover as bp

BBB = os.environ.get("BBB_REPO", os.path.join(ROOT, "..", "BBB"))
CAND_N = (2, 3, 4)
CAND_T = (64, 256, 1024)


def slot(tok):
    tok = tok.strip()
    if tok == "tN":
        return "---"
    m = re.fullmatch(r"t([01])([LR])([ABCD])", tok)
    return f"{m.group(1)}{m.group(2)}{m.group(3)}"


def deferred_machines():
    """Decode every row of the committed Deferred_*.v tables to text."""
    out = []
    for f in sorted(glob.glob(os.path.join(
            ROOT, "theories", "Census", "Deferred_0*.v"))):
        for line in open(f):
            m = re.fullmatch(r"\[(t[^\]]+)\];?", line.strip())
            if not m:
                continue
            toks = m.group(1).split(";")
            if len(toks) != 8:
                continue
            s = [slot(t) for t in toks]
            out.append("_".join(s[2 * i] + s[2 * i + 1] for i in range(4)))
    return out


def wrapped_closure(tbl, qq, n, t, cap=200000):
    """Halt-free n-gram closure of the wrapped machine from the real
    machine's step-t config.  True iff the wrapped machine provably
    never halts (never re-fires qq) after t."""
    tape = {}
    pos = 0
    q = 0
    for _ in range(t):
        tr = tbl[(q, tape.get(pos, 0))]
        if tr is None:
            return False
        w, d, nq = tr
        tape[pos] = w
        pos += 1 if d == "R" else -1
        q = nq
    if q == qq:
        return False
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
                return False
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
            return not any(tw[(a[0], a[1])] is None for a in seen)
        lset |= newl
        rset |= newr
    return False


def last_visit_before(tbl, qq, t):
    tape = {}
    pos = 0
    q = 0
    last = None
    for i in range(t):
        if q == qq:
            last = i
        tr = tbl[(q, tape.get(pos, 0))]
        if tr is None:
            return last
        w, d, nq = tr
        tape[pos] = w
        pos += 1 if d == "R" else -1
        q = nq
    if q == qq:
        last = t
    return last


def find_wrap(m):
    """Return (q, s, n, t) for a valid wrap cert, or None."""
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
                if wrapped_closure(tbl, qq, n, t):
                    s = last_visit_before(tbl, qq, t)
                    if s is None or s >= t:
                        continue
                    return (qq, s, n, t)
    return None


def work(m):
    try:
        r = find_wrap(m)
    except Exception:
        r = None
    return (m, r)


def main():
    outdir = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "wrap_residue")
    nproc = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    os.makedirs(outdir, exist_ok=True)
    holdouts = set(l.strip() for l in
                   open(os.path.join(BBB, "BBB4_holdouts_3713.txt")) if l.strip())
    residue = sorted(set(deferred_machines()) - holdouts)
    open(os.path.join(outdir, "residue.txt"), "w").write("\n".join(residue) + "\n")
    print(f"residue: {len(residue)}")
    caught = []
    survivors = []
    with mp.Pool(nproc) as pool:
        for i, (m, r) in enumerate(pool.imap_unordered(work, residue, chunksize=64)):
            if r is None:
                survivors.append(m)
            else:
                caught.append((m,) + r)
            if (i + 1) % 10000 == 0:
                print(f"{i+1}/{len(residue)} caught={len(caught)} "
                      f"survivors={len(survivors)}", flush=True)
    caught.sort()
    survivors.sort()
    with open(os.path.join(outdir, "caught.tsv"), "w") as f:
        f.write("machine\tquiet_state\ts\tn\tt\n")
        for m, qq, s, n, t in caught:
            f.write(f"{m}\t{chr(65+qq)}\t{s}\t{n}\t{t}\n")
    open(os.path.join(outdir, "survivors.txt"), "w").write(
        "\n".join(survivors) + "\n")
    print(f"DONE residue={len(residue)} wrap_caught={len(caught)} "
          f"survivors={len(survivors)}")


if __name__ == "__main__":
    main()
