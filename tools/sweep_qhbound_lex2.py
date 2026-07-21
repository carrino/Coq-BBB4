#!/usr/bin/env python3
"""EXTENDED lex-gated QHBound sweep (UNTRUSTED measurement mirror).

Mirrors an EXTENDED in-Coq RankSearch that, per quiet state q, first
runs the CURRENT count-of-1s vocabulary (MAll/MLeft/MRight ==
((1,),A/L/R)), and ONLY IF that fails, retries with the pattern/digram
(NgPattE-class) vocabulary that the verified checker
(ngram_check_qhbound_lex via ng_comp_denote / pm_delta / pm_ok)
already accepts.

The count pass is IDENTICAL to the committed sweep (bp.procedure with
DEFAULT_MEASURES); the digram pass is a strict ADD-ON, run only where
count fails, so no currently-caught machine can regress (the
rule-(a)-before-rule-(b) ordering means a digram tried first could
divert the reduction, hence the two-pass ladder rather than one merged
candidate list).

Everything here is UNTRUSTED: bp.procedure/bp.lex_check re-derive the
same decision the Coq engine's live_lex_ok runs; a hit requires BOTH
the procedure to succeed AND lex_check to re-verify every q-avoiding
edge -- conservative (when unsure, reject).

Per machine records: caught?, winning rung (n,t), gate/measure class
(rank / count-lex / digram), wall ms, closure size (contexts).
"""
import os
import sys
import time

TOOLS = "/home/user/Coq-BBB4/tools"
sys.path.insert(0, TOOLS)
import bulk_prover as bp
import sweep_qhbound_residue as sq

# --- vocabulary -----------------------------------------------------------
# count-of-1s: exactly MAll/MLeft/MRight (bp.pdelta((1,),reg) == ngm_delta)
COUNT = [((1,), 'A'), ((1,), 'L'), ((1,), 'R')]
# digrams: the gen_bulk_certs EXTRA_CANDS pattern/digram vocabulary
DIGRAM = [((1, 1), 'A'), ((1, 1), 'L'), ((1, 1), 'R'),
          ((1, 0), 'A'), ((1, 0), 'L'), ((1, 0), 'R'),
          ((0, 1), 'A'), ((0, 1), 'L'), ((0, 1), 'R')]
# extended = count first (so the count reduction path is preferred),
# then digrams. Only used in the fallback pass.
EXT = COUNT + DIGRAM


def cands_for(cands, n):
    """Deterministic, coverage-filtered candidate list (mirrors
    pm_ok: pattern must contain S1; |p|-1<=n for A, |p|<=n for L/R)."""
    return [c for c in cands if bp.meas_ok(c[0], c[1], n)]


def run_pass(tw, n, seen, lset, rset, states, cands_n):
    """Try to discharge EVERY appearing state with the given candidate
    list. Returns comps_by_state on full success, else None."""
    comps_by_state = {}
    for qq2 in states:
        comps = bp.procedure(tw, n, seen, lset, rset, qq2, cands_n)
        if comps is None:
            return None
        good, _ = bp.lex_check(tw, n, seen, lset, rset, qq2, comps)
        if not good:
            return None
        comps_by_state[qq2] = comps
    return comps_by_state


def classify(comps_by_state):
    """rank (pure acyclicity) / count-lex (only (1,) measures) /
    digram (any length>=2 pattern measure used)."""
    has_digram = False
    has_count = False
    for comps in comps_by_state.values():
        for c in comps:
            if c[0] == 'meas':
                if len(c[1]) >= 2:
                    has_digram = True
                else:
                    has_count = True
    if has_digram:
        return 'digram'
    if has_count:
        return 'count-lex'
    return 'rank'


def last_visit_before(tbl, qq, t):
    """Last step index < t at which state qq is the current state
    (mirrors last_visit ... requires Some s with s < t)."""
    tp = {}
    p = 0
    qc = 0
    s = None
    for i in range(t):
        if qc == qq:
            s = i
        tr = tbl[(qc, tp.get(p, 0))]
        if tr is None:
            return None
        w, d, nq = tr
        tp[p] = w
        p += 1 if d == 'R' else -1
        qc = nq
    if s is None or s >= t:
        return None
    return s


def try_rung(tbl, qq, n, t, mode):
    """Build the wrapped closure once; try count pass, then (if
    mode=='ext') the extended pass. Returns (class, closure_size,
    comps_by_state) or None. Also enforces the s<t quiet-prefix gate."""
    r = sq.wrapped_closure(tbl, qq, n, t)
    if r is None:
        return None
    seen, lset, rset, tw = r
    states = sorted(set(a[0] for a in seen))
    # count-only pass (identical to committed sweep)
    cc = run_pass(tw, n, seen, lset, rset, states, cands_for(COUNT, n))
    if cc is not None:
        if last_visit_before(tbl, qq, t) is None:
            return None
        return (classify(cc), len(seen), cc)
    if mode == 'count':
        return None
    # extended (digram) fallback pass
    ec = run_pass(tw, n, seen, lset, rset, states, cands_for(EXT, n))
    if ec is not None:
        if last_visit_before(tbl, qq, t) is None:
            return None
        return (classify(ec), len(seen), ec)
    return None


def candidate_states(tbl):
    """States visited in the first 1024 steps, non-A first then A
    (mirrors gen_qhbound_lex.find_lex ordering)."""
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
        pos += 1 if d == 'R' else -1
        q = nq
    return sorted(vis, key=lambda x: (x == 0, x))


def find_lex_ladder(m, rungs, mode='ext'):
    """Iterate qq (outer) x rungs (inner); return the FIRST catch as
    (qq, n, t, gate_class, closure_size) or None. Mirrors the census
    try_qhb structure (candidate state outer, rung inner)."""
    tbl = bp.parse(m)
    states = candidate_states(tbl)
    for qq in states:
        for (n, t) in rungs:
            res = try_rung(tbl, qq, n, t, mode)
            if res is not None:
                cls, csize, _ = res
                return (qq, n, t, cls, csize)
    return None
