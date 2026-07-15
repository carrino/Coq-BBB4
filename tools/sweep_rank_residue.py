#!/usr/bin/env python3
"""Sweep the census residue through the rank pipeline (UNTRUSTED).

Runs bulk_prover.decide with the DEFAULT count-of-1s measures at the
exact (n, t) rungs the Coq census rank tier uses -- n=3,
t in (0, 64, 256, 1024) -- and writes the machines that still fail.
Those plus the holdouts form the v2 deferred list.

Usage: sweep_rank_residue.py RESIDUE_FILE OUT_FAIL [NPROC]
"""
import sys, multiprocessing as mp
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import bulk_prover as bp

RUNGS_T = (0, 64, 256, 1024)
N = 3

def visited_states(tbl, t):
    """States visited in the simulated prefix (the Coq checker's
    cvisits premise) -- bulk_prover.decide only checks states present
    in the closure, which overclaims on machines whose quiet states
    (visited early, never again) vanish from it."""
    tape = {}; pos = 0; q = 0; vis = {0}
    for _ in range(t):
        tr = tbl[(q, tape.get(pos, 0))]
        if tr is None:
            return None
        w, d, nq = tr
        tape[pos] = w
        pos += 1 if d == 'R' else -1
        q = nq
        vis.add(q)
    return vis

def decide_strict(m, n, t_cands):
    tbl = bp.parse(m)
    for t in t_cands:
        r = bp.build_closure(tbl, n, t)
        if r is None:
            continue
        seen, lset, rset, _a0, _rounds = r
        vis = visited_states(tbl, t)
        if vis is None:
            continue
        states = sorted(vis | {a[0] for a in seen})
        ok = True
        for qq in states:
            comps = bp.procedure(tbl, n, seen, lset, rset, qq,
                                 bp.DEFAULT_MEASURES)
            if comps is None:
                ok = False
                break
            good, _bad = bp.lex_check(tbl, n, seen, lset, rset, qq, comps)
            if not good:
                ok = False
                break
        if ok:
            return t
    return None

def work(m):
    try:
        return (m, decide_strict(m, N, RUNGS_T) is not None)
    except Exception:
        return (m, False)

def main():
    residue, out = sys.argv[1], sys.argv[2]
    nproc = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    ms = [l.strip() for l in open(residue) if l.strip()]
    fails = []
    kills = 0
    with mp.Pool(nproc) as pool:
        for i, (m, ok) in enumerate(pool.imap_unordered(work, ms, chunksize=64)):
            if ok:
                kills += 1
            else:
                fails.append(m)
            if (i + 1) % 5000 == 0:
                print(f'{i+1}/{len(ms)} kills={kills} fails={len(fails)}',
                      flush=True)
    fails.sort()
    with open(out, 'w') as f:
        f.write('\n'.join(fails) + '\n')
    print(f'DONE total={len(ms)} kills={kills} fails={len(fails)}')

if __name__ == '__main__':
    main()
