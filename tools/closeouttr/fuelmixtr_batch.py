#!/usr/bin/env python3
"""Find weighted pattern certificates for FuelMixTr (untrusted search).

Uses fueltr_batch's instruction-target graph and ordinary lexicographic
peeling. When individual measures cannot peel an SCC, linear programming
proposes nonnegative sums, optionally with node potentials. All rounded
coefficients are checked by exact integer arithmetic, then the complete
certificate is replayed with the independent baseline pattern deltas.
The generated Coq checker checks those inequalities again in the kernel.

The find command requires NumPy/SciPy; certificate emission does not.
Command-line arguments are the same as fueltr_batch.py.
"""
import os
os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
from fractions import Fraction
from functools import partial
import math
import fueltr_batch as ft


def choose_mix(tbl, n, cs, intra, candidates, delta):
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import csr_matrix, hstack
    nodes = sorted(cs)
    ds = [[delta(p, r, a[0]) for a in nodes] for p, r in candidates]
    indices = [i for i, d in enumerate(ds) if min(d) < 0]
    if not indices:
        return None
    matrix = np.array([ds[i] for i in indices], dtype=float).T
    bounds = np.zeros(len(nodes) + 1)
    bounds[-1] = -1
    result = linprog(np.ones(len(indices)),
        A_ub=np.vstack([matrix, matrix.sum(axis=0)]), b_ub=bounds,
        bounds=(0, None), method="highs", options={"time_limit": 2.0})
    if result.success:
        fractions = [Fraction(float(x)).limit_denominator(10000) for x in result.x]
        scale = math.lcm(*(f.denominator for f in fractions))
        weights = [int(f * scale) for f in fractions]
        if max(weights) > 1000000 or min(weights) < 0:
            return None
        values = {a: sum(w * ds[i][j] for i, w in zip(indices, weights))
                  for j, a in enumerate(nodes)}
        if max(values.values()) > 0 or min(values.values()) >= 0:
            return None
        phi = dict.fromkeys(nodes, 0)
    else:
        index = {a: i for i, a in enumerate(nodes)}
        edges = list(intra)
        left = np.array([[ds[i][index[u]] for i in indices] for u, _ in edges],
                        dtype=float)
        rows, columns, values = [], [], []
        for j, (u, v) in enumerate(edges):
            rows.extend([j, j])
            columns.extend([index[v], index[u]])
            values.extend([1., -1.])
        potential = csr_matrix((values, (rows, columns)),
                               shape=(len(edges), len(nodes)))
        matrix = hstack([csr_matrix(left), potential], format="csr")
        result = linprog(np.r_[np.ones(len(indices)), np.zeros(len(nodes))],
            A_ub=matrix, b_ub=-np.ones(len(edges)), bounds=(0, None),
            method="highs", options={"time_limit": 2.0})
        if not result.success:
            return None
        weights = [max(0, round(x * 4096)) for x in result.x[:len(indices)]]
        phi = dict(zip(nodes, [max(0, round(x * 4096))
                              for x in result.x[len(indices):]]))
        values = {a: sum(w * ds[i][j] for i, w in zip(indices, weights))
                  for j, a in enumerate(nodes)}
        if any(values[u] + phi[v] - phi[u] >= 0 for u, v in edges):
            return None
    terms = [(w, *candidates[i]) for i, w in zip(indices, weights) if w]
    return terms, values, phi


base_strict, base_noninc = ft.gf.comp_strict, ft.gf.comp_noninc


def mix_change(tbl, n, comp, a, b):
    _, terms, _, scale, phi, _ = comp
    delta = sum(w * ft.bp.pdelta(tbl, n, p, r, a[0]) for w, p, r in terms)
    return scale * delta + phi.get(b, 0) - phi.get(a, 0)


def strict(tbl, n, comp, a, b):
    if comp[0] != "mix":
        return base_strict(tbl, n, comp, a, b)
    gate = comp[5]
    return a in gate and b in gate and mix_change(tbl, n, comp, a, b) <= -1


def noninc(tbl, n, comp, a, b):
    if comp[0] != "mix":
        return base_noninc(tbl, n, comp, a, b)
    gate = comp[5]
    return b not in gate or (a in gate and mix_change(tbl, n, comp, a, b) <= 0)


def emit_comp(comp):
    if comp[0] == "rank":
        return "FMRankE\n    %s" % ft.gf.emit_fphi(comp[1])
    if comp[0] == "mix":
        _, terms, _, scale, phi, gate = comp
    else:
        _, pattern, region, scale, phi, gate = comp
        terms = [(1, pattern, region)]
    emitted = ["(%s, %s, Rg%s)" %
               (ft.gf.gb.fmt_nat(w), ft.gf.gb.coq_patt(p), r) for w, p, r in terms]
    return "FMPattSumE [%s] %s\n    %s\n    %s" % (
        "; ".join(emitted), ft.gf.gb.fmt_nat(scale), ft.gf.emit_fphi(phi),
        ft.gf.emit_fkeys(gate))


def emit_cert(per_target):
    arms = []
    for q in range(4):
        for s in range(2):
            components, gate = per_target.get((q, s), ([], set()))
            body = "[" + ";\n   ".join(emit_comp(c) for c in components) + "]"
            arms.append("  | (St%s, S%d) => (%s,\n   %s)" %
                        (chr(65 + q), s, body, ft.gf.emit_fkeys(gate)))
    return "fun target : Instr => match target with\n" + "\n".join(arms) + "\n  end"


def write_records(tag, nn, indexed, overwrite=False):
    entries, preamble = [], []
    for idx, rec in indexed:
        name = "fuelmixtr_%s_%02d_%04d" % (tag, nn, idx)
        preamble.append("Definition %s : Instr -> list fmxcomp * list positive :=\n%s." %
                        (name, rec["cert"]))
        proof = "apply coversTr_nqh. "
        if rec["mirrored"]:
            proof += "apply neverqhtr_mirror. "
        proof += ("apply (ngram_check_neverqh_fuelmixtr_sound _ %d %d %d %d %s). " %
                  (rec["n"], rec["t"], rec["fuel"], rec["rounds"], name))
        proof += "vm_compute. reflexivity."
        entries.append((rec["spec"], proof))
    path = ft.write_batch(tag, nn,
        ["From BBB4.Checkers Require Import NGram FuelMixTr.",
         "From BBB4.CensusTr Require Import TNF_QHTr."], entries,
        "nonnegative pattern sums and fuel certificates (FuelMixTr)",
        overwrite=overwrite, preamble="\n\n".join(preamble))
    print(path)


ft.instruction_procedure = partial(ft.instruction_procedure, mix_finder=choose_mix)
ft.gf.comp_strict, ft.gf.comp_noninc = strict, noninc
ft.emit_cert, ft.write_records = emit_cert, write_records

if __name__ == "__main__":
    ft.main()
