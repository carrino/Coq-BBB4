#!/usr/bin/env python3
"""LEVER C extended RepWL sweep (UNTRUSTED measurement).

Faithful mirror of the in-Coq census RepWL tier (Checkers/RepWL.v +
Census/RepWLSearch.v), reusing tools/repwl_prover.py.  Extends the
census 4-rung ladder with:
  (i)  measure gates -- ALREADY in rp.procedure via rp.MEAS (rules
       (a)/(b) over the 5 built-ins), so the "base" config below is
       exactly the wired census tier; and
  (ii) larger (L,T) rungs.

Per rung we build the closure exactly like the Coq `close`
(front-pop worklist; count = total items pushed = 1 + sum of emitted
successors over expanded nodes = pops, bounded by 2*nodes+1), then run
rp.procedure per premise state with the full 5-measure vocabulary and
rp.lex_check.  A machine is caught at a rung iff every state is
discharged.  gate class = 'measure-lex' if any winning component is a
measure component, else 'plain-rank'.
"""
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
TOOLS = "/home/user/Coq-BBB4/tools"
sys.path.insert(0, TOOLS)
import repwl_prover as rp

# census fuel budget: the Coq `close fuel=8192` succeeds iff it
# finishes within 8192 iterations; iterations = pushes + 1 (final
# empty-todo check), where pushes = 1 + sum of emitted successors over
# expanded nodes = the "pops".  So a closure closes under the census
# budget iff pushes <= 8191.  We cap on POPS (fuel), NOT nodes: a
# low-branching closure can have up to ~8190 nodes while pushes <= 8191.
POPS_BUDGET = 8191            # rw_fuel(8192) - 1
NODE_SAFETY = 60000          # memory guard only (never binds first)


def build_closure_pops(tbl, L, T, t, cap_nodes=POPS_BUDGET):
    """Mirror rp.build_closure but cap on POPS (Coq `close` fuel).
    cap_nodes is interpreted as the POPS budget (default 8191).
    Returns (a0, seen, adj, pops) or None (halt / fail-closed /
    exceeds fuel)."""
    a0 = rp.seed(tbl, L, T, t)
    if a0 is None:
        return None
    seen = set()
    adj = {}
    todo = [a0]
    pushes = 1  # a0
    while todo:
        a = todo.pop()
        if a in seen:
            continue
        seen.add(a)
        if len(seen) > NODE_SAFETY:
            return None
        sl = rp.rw_succs(tbl, L, T, a)
        if sl is None:
            return None
        adj[a] = sl
        todo.extend(sl)
        pushes += len(sl)
        if pushes > cap_nodes:       # cap_nodes == POPS budget
            return None
    return a0, seen, adj, pushes


def try_rung(tbl, L, T, t, cap_nodes=POPS_BUDGET):
    """cap_nodes is the POPS (fuel) budget.  Returns dict(caught,
    nodes, pops, gate) or closure-fail dict."""
    r = build_closure_pops(tbl, L, T, t, cap_nodes)
    if r is None:
        return {"caught": False, "nodes": None, "pops": None,
                "gate": None, "closure": False}
    a0, seen, adj, pops = r
    states = sorted({a[0] for a in seen} | rp.warmup_states(tbl, t))
    used_meas = False
    for qq in states:
        comps = rp.procedure(tbl, seen, adj, qq, rp.MEAS)
        if comps is None or not rp.lex_check(tbl, adj, seen, qq, comps):
            return {"caught": False, "nodes": len(seen), "pops": pops,
                    "gate": None, "closure": True}
        if any(c[0] == "meas" for c in comps):
            used_meas = True
    return {"caught": True, "nodes": len(seen), "pops": pops,
            "gate": "measure-lex" if used_meas else "plain-rank",
            "closure": True}


BASE_RUNGS = [(2, 2, 0), (3, 2, 0), (4, 2, 0), (2, 3, 0)]
# extended (L,T), t=0, ordered small-first (cheap-first)
EXT_RUNGS = [(2, 4, 0),
             (3, 3, 0), (3, 4, 0),
             (4, 3, 0), (4, 4, 0),
             (5, 2, 0), (5, 3, 0), (5, 4, 0),
             (6, 2, 0), (6, 3, 0), (6, 4, 0)]


def sweep_machine(m, rungs, cap_nodes=POPS_BUDGET, per_rung_budget=None):
    """Try rungs in order; return first catch record + telemetry.
    per_rung_budget: optional wallclock seconds cap across rungs."""
    tbl = rp.parse(m)
    t0 = time.time()
    rung_notes = []
    for (L, T, t) in rungs:
        rr = try_rung(tbl, L, T, t, cap_nodes)
        rung_notes.append((L, T, t, rr["caught"], rr["nodes"], rr["pops"],
                           rr["closure"]))
        if rr["caught"]:
            return {"machine": m, "caught": True, "L": L, "T": T, "t": t,
                    "gate": rr["gate"], "nodes": rr["nodes"],
                    "pops": rr["pops"], "ms": int((time.time()-t0)*1000),
                    "notes": rung_notes}
        if per_rung_budget and (time.time()-t0) > per_rung_budget:
            return {"machine": m, "caught": False, "timeout": True,
                    "ms": int((time.time()-t0)*1000), "notes": rung_notes}
    return {"machine": m, "caught": False, "ms": int((time.time()-t0)*1000),
            "notes": rung_notes}
