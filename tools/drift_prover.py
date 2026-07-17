"""Untrusted drift prover: rule (c3) over the class-refined n-gram
abstraction (the neverqh_drift kill), mirroring the Coq checker
[ngram_check_neverqh_driftw] (theories/Checkers/Drift.v).

Reuses the FuelWide machinery from gen_fuel_certs.py (refined closure
over (cconf, fl, fr) nodes, adjacency, lex components) and replaces
the per-SCC runner kill (c2) with the DRIFT kill (c3), in BOTH
directions at once (no machine-level mirror: the two deferring
holdouts have, for a single state q, stuck SCCs drifting opposite
ways -- e.g. 1RB1LC_1LC0RB_1RD0LC_0RD1LA q=B).  A stuck cyclic SCC
dies rightward when

  - every RIGHT-moving node holds fuel on the right (window or
    class); left-movers need nothing -- the Coq descent
    V = W*R + phi only needs R >= 1 where the right window shrinks;
  - untrusted per-node potentials phi exist with, on every intra
    edge u -> v:   phi(v) + 1 <= phi(u) + W   (u moves right)
                   phi(v) + W + 1 <= phi(u)   (u moves left)
    which (Bellman-Ford, W > any simple cycle length) is exactly
    "every cycle of the SCC has strictly positive net rightward
    displacement";

and leftward by the mirror conditions.  Rightward-killed SCCs join
the state's R gate, leftward ones the L gate; the gates stay disjoint
by construction (a killed SCC's nodes never re-enter a cyclic SCC:
edges are only ever deleted), and Coq re-checks disjointness.

Everything here is UNTRUSTED search: the emitted (comps, gateR, phiR,
gateL, phiL, W) tables are re-checked edge by edge inside Coq.
dw_state_check below is the faithful mirror of Drift.v's
drift_state_ok, used for differential validation before any Coq is
generated.
"""

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import bulk_prover as bp
import gen_fuel_certs as gf

T_CANDS = gf.T_CANDS


def moves_right(tbl, fa):
    return gf.fw_moves_right(tbl, fa)


def moves_left(tbl, fa):
    tr = tbl[(fa[0][0], fa[0][1])]
    return tr is not None and tr[1] == "L"


def rfuel(fa):
    """Right fuel: nonblank in the right window, or right class >= 1
    (mirror of FuelWide fwnode_rfuel_ge1)."""
    return gf.fw_rfuel(fa)


def lfuel(fa):
    """Left fuel: nonblank in the left window, or left class >= 1
    (mirror of Drift.v fwnode_lfuel_ge1)."""
    return any(x != 0 for x in fa[0][2]) or fa[1] >= 1


def rgate_node_ok(tbl, fa):
    """Mirror of the R-gate node fact of Drift.v dgate_ok: a fueled
    right-mover, or a left-mover."""
    if moves_right(tbl, fa):
        return rfuel(fa)
    return moves_left(tbl, fa)


def lgate_node_ok(tbl, fa):
    """Mirror of the L-gate node fact: a fueled left-mover, or a
    right-mover."""
    if moves_left(tbl, fa):
        return lfuel(fa)
    return moves_right(tbl, fa)


def dpotR_ok(tbl, phi, W, fa, fb):
    """R-gate potential inequality, selected by the SOURCE's move."""
    pa = phi.get(fa, 0)
    pb = phi.get(fb, 0)
    if moves_right(tbl, fa):
        return pb + 1 <= pa + W
    return pb + W + 1 <= pa


def dpotL_ok(tbl, phi, W, fa, fb):
    """L-gate potential inequality (mirror of dpotR_ok)."""
    pa = phi.get(fa, 0)
    pb = phi.get(fb, 0)
    if moves_left(tbl, fa):
        return pb + 1 <= pa + W
    return pb + W + 1 <= pa


def drift_edge_ok(tbl, n, comps, gR, phiR, gL, phiL, W, fa, fb):
    """Mirror of Drift.v drift_edge_ok: lex-good, or gate-internal
    (one gate) with all components non-increasing and the gate's
    potential inequality."""
    if gf.lex_edge_ok_fw(tbl, n, comps, fa, fb):
        return True
    if not all(gf.comp_noninc(tbl, n, c, fa, fb) for c in comps):
        return False
    if fa in gR and fb in gR and dpotR_ok(tbl, phiR, W, fa, fb):
        return True
    return fa in gL and fb in gL and dpotL_ok(tbl, phiL, W, fa, fb)


def dw_state_check(tbl, n, adj, fseen, qq, comps, gR, phiR, gL, phiL, W):
    """Full mirror of Drift.v drift_state_ok: the gates are disjoint;
    R-gate nodes are non-qq fueled-right-movers or left-movers (L
    mirrored); every q-avoiding edge passes drift_edge_ok."""
    if gR & gL:
        return False
    for fa in gR:
        if fa[0][0] == qq or not rgate_node_ok(tbl, fa):
            return False
    for fa in gL:
        if fa[0][0] == qq or not lgate_node_ok(tbl, fa):
            return False
    for fa in fseen:
        if fa[0][0] == qq:
            continue
        for fb in adj[fa]:
            if fb[0][0] == qq:
                continue
            if not drift_edge_ok(tbl, n, comps, gR, phiR, gL, phiL, W,
                                 fa, fb):
                return False
    return True


def drift_potentials(tbl, cs, intra, W, side):
    """Feasible drift potentials for one SCC toward `side`, or None.
    Edge u -> v needs phi[u] - phi[v] >= 1 - W (u moves toward side)
    or >= W + 1 (u moves away); bp.bellman_potentials finds phi with
    We <= phi[u] - phi[v]."""
    toward = moves_right if side == "R" else moves_left
    edges = []
    for (u, v) in intra:
        We = (1 - W) if toward(tbl, u) else (W + 1)
        edges.append((u, v, We))
    return bp.bellman_potentials(list(cs), edges)


def dw_procedure(tbl, n, adj, fseen, qq, cands):
    """Rules (a)/(b) + the two-sided drift kill (c3) over the refined
    q-avoiding graph.  Returns (comps, gateR, phiR, gateL, phiL, W)
    or None.  Forked from gen_fuel_certs.fw_procedure with the (c2)
    runner kill replaced by the strictly more general (c3) kill (a
    uniform fueled right-mover SCC has feasible R-potentials
    trivially)."""
    nodes = [fa for fa in fseen if fa[0][0] != qq]
    Kc = len(nodes) + 2
    W = Kc
    alive = {}
    for fa in nodes:
        for fb in adj[fa]:
            if fb[0][0] != qq:
                alive[(fa, fb)] = True
    comps = []
    gR = set()
    phiR = {}
    gL = set()
    phiL = {}
    gate_edges = []
    rounds = 0
    while True:
        rounds += 1
        if rounds > 300:
            return None
        adjmap = {}
        for (u, v) in alive:
            adjmap.setdefault(u, []).append(v)
        comp_list = bp.sccs(nodes, lambda v: adjmap.get(v, []))
        cyclic = [c for c in comp_list
                  if len(c) > 1 or c[0] in adjmap.get(c[0], [])]
        if not cyclic:
            comps.append(("rank",
                          gf.scc_rank(nodes, list(alive) + gate_edges)))
            return comps, gR, phiR, gL, phiL, W
        comps.append(("rank", gf.scc_rank(nodes, list(alive) + gate_edges)))
        progress = False
        for c in cyclic:
            cs = set(c)
            intra = [(u, v) for (u, v) in alive if u in cs and v in cs]
            done = False
            for (patt, reg) in cands:
                ds = {e: bp.pdelta(tbl, n, patt, reg, e[0][0]) for e in intra}
                if (all(d <= 0 for d in ds.values())
                        and any(d < 0 for d in ds.values())):
                    comps.append(("meas", patt, reg, 1,
                                  {v: 0 for v in c}, cs))
                    for e in intra:
                        if ds[e] < 0:
                            del alive[e]
                    progress = True
                    done = True
                    break
            if done:
                continue
            for (patt, reg) in cands:
                Wt = [(u, v, Kc * bp.pdelta(tbl, n, patt, reg, u[0]) + 1)
                      for (u, v) in intra]
                p = bp.bellman_potentials(list(cs), Wt)
                if p is not None:
                    comps.append(("meas", patt, reg, Kc, p, cs))
                    for e in intra:
                        del alive[e]
                    progress = True
                    done = True
                    break
            if done:
                continue
            # the drift kill (c3), each direction: fuel at the
            # toward-moving nodes, feasible potentials certify
            # net-positive-toward cycles
            for side, gate, phi, node_ok in (
                    ("R", gR, phiR, rgate_node_ok),
                    ("L", gL, phiL, lgate_node_ok)):
                if not all(node_ok(tbl, u) for u in cs):
                    continue
                p = drift_potentials(tbl, cs, intra, W, side)
                if p is None:
                    continue
                gate |= cs
                phi.update(p)
                for e in intra:
                    del alive[e]
                    gate_edges.append(e)
                progress = True
                break
        if not progress:
            return None


def dw_decide(mtext, n0, per_state, n_extra=1):
    """Drift search over the window and t ladders (single orientation:
    the two-sided kill needs no mirror).  Returns (result dict, None)
    or (None, first-fail string)."""
    first_fail = None
    for n in range(n0, n0 + n_extra + 1):
        tbl = bp.parse(mtext)
        for t in T_CANDS:
            r = bp.build_closure(tbl, n, t)
            if r is None:
                continue
            seen, lset, rset, a0, _rounds = r
            tape, pos, _q = gf.sim_tape(tbl, t)
            lcnt = sum(1 for p, v in tape.items() if p < pos and v == 1)
            rcnt = sum(1 for p, v in tape.items() if p > pos and v == 1)
            fa0 = (a0, min(lcnt, 2), min(rcnt, 2))
            fseen = gf.build_fw_closure(tbl, lset, rset, fa0)
            if fseen is None:
                continue
            adj = gf.fw_adj(tbl, lset, rset, fseen)
            states = sorted({fa[0][0] for fa in fseen}
                            | gf.warmup_states(tbl, t))
            per_q = {}
            modes = {}
            ok = True
            for qq in states:
                cands = [m for m in dict.fromkeys(
                    per_state.get(qq, []) + bp.DEFAULT_MEASURES)
                    if bp.meas_ok(m[0], m[1], n)]
                res = dw_procedure(tbl, n, adj, fseen, qq, cands)
                if res is None:
                    res = dw_procedure(tbl, n, adj, fseen, qq,
                                       [m for m in gf.exhaustive_cands(n)
                                        if bp.meas_ok(m[0], m[1], n)])
                if res is None or not dw_state_check(
                        tbl, n, adj, fseen, qq, *res):
                    if first_fail is None:
                        first_fail = ("n=%d t=%d q=%s"
                                      % (n, t, chr(65 + qq)))
                    ok = False
                    break
                per_q[qq] = res
                nR, nL = len(res[1]), len(res[3])
                modes[qq] = ("drift:R%d,L%d" % (nR, nL)) if nR or nL else "lex"
            if ok:
                return {"n": n, "t": t, "nseen": len(fseen),
                        "per_q": per_q, "modes": modes,
                        "rounds": len(lset) + len(rset) + 4}, None
    return None, first_fail or "no closure at any t"
