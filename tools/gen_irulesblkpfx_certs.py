#!/usr/bin/env python3
"""Transcribe v6/v7 prefix block-run irules certificates into Coq
IRulesBlkPfx batches (Phase 2).

Forked from tools/gen_irulesblk_certs.py; mirrors its structure,
cname/emit_tm/zlit conventions and batch layout exactly.  Phase-2
differences (all measured, see tools/recon_20260719/PHASE2_DESIGN.md):

  * [rulepfx IDX pl pr] (verify.c:1057-1067) -- two numeric flags; rule
    IDX gets per-side prefix flags (pl=="1", pr=="1").  Rules without a
    [rulepfx] line get (false, false).
  * [rulerunm RIDX side ri sym del lb mod res] (verify.c:1023-1056) --
    that run becomes a residue-lattice var run [BVm del lb mod res].
  * run counts:  RC v -> [BC (v)];  RV d lb -> [BV (d) (lb)];
    rulerunm -> [BVm (del) (lb) (mod) (res)].
  * rules:  [mkBRuleP StX Sy [runsL] [runsR] (pl, pr)].
  * cert:  [mkBIRCertP anchor%nat (k0) (kmin) (a) (b) StX Sy
            [blks] [TL] [TR] [rules]] -- field order identical to
    Phase-1's mkBIRCert, rules are BRuleP.
  * theorem closed by [irulesblkpfx_check_neverqh_sound tm cert
    200000 300000] + [vm_compute].

Each machine emits: the TM, a [BIRCertP] literal straight from its
certificate, the [NeverQuasiHaltsSt] theorem and the [NonHalt]
corollary.  Certificates are untrusted search output; every claim is
re-checked by the verified Phase-2 block IRules engine
(theories/Checkers/IRules/EngineKS.v + RulesBlkPfx.v + MetaBlkPfx.v).

Usage: gen_irulesblkpfx_certs.py OUT.v NAME CERT [CERT ...]
"""
import sys, os

ST = {"A": "StA", "B": "StB", "C": "StC", "D": "StD"}
SYM = {0: "S0", 1: "S1"}
DIRW = {"R": "DR", "L": "DL"}
CFUEL = 200000
FUEL = 300000


def parse_cert(path):
    c = {"tplL": {}, "tplR": {}, "rules": {}, "blk": {}, "pfx": {}}
    for ln in open(path):
        p = ln.split()
        if not p:
            continue
        k = p[0]
        if k in ("anchor_step", "k0", "kmin", "meta_a", "meta_b",
                 "tpl_hsym", "nrules"):
            c[k] = int(p[1])
        elif k == "bbbcert":  c["ver"] = p[1]
        elif k == "machine":  c["machine"] = p[1]
        elif k == "type":     c["type"] = p[1]
        elif k == "tpl_state": c["tpl_state"] = p[1]
        elif k == "blk":
            c["blk"][int(p[1])] = [int(x) for x in p[2]]
        elif k == "tplrun":
            side, idx, sym, al, be = p[1], int(p[2]), int(p[3]), int(p[4]), int(p[5])
            c["tplL" if side == "L" else "tplR"][idx] = (sym, al, be)
        elif k == "rule":
            ridx = int(p[1])
            c["rules"][ridx] = {"st": p[2], "hs": int(p[3]), "L": {}, "R": {}}
        elif k == "rulepfx":
            # verify.c:1057-1067 format: rulepfx RIDX pl pr (pl,pr in
            # {0,1}; a set flag means that side is a near-head prefix).
            ridx = int(p[1])
            c["pfx"][ridx] = (p[2] == "1", p[3] == "1")
        elif k == "rulerun":
            ridx, side, idx, sym = int(p[1]), p[2], int(p[3]), int(p[4])
            r = c["rules"][ridx]
            if p[5] == "C":
                r[side][idx] = (sym, ("C", int(p[6])))
            else:
                r[side][idx] = (sym, ("V", int(p[6]), int(p[7])))
        elif k == "rulerunm":
            # v7 (verify.c:1023-1056): rulerunm IDX side ri sym del lb
            # mod res -- a var run confined to the residue lattice.
            ridx, side, idx, sym = int(p[1]), p[2], int(p[3]), int(p[4])
            dl, lb, mo, re = int(p[5]), int(p[6]), int(p[7]), int(p[8])
            c["rules"][ridx][side][idx] = (sym, ("Vm", dl, lb, mo, re))
    return c


def cname(machine):
    return machine.replace("-", "X")


def emit_tm(machine):
    groups = machine.split("_")
    out = []
    for qi, g in enumerate(groups):
        st = "ABCD"[qi]
        for si in range(2):
            t = g[3 * si:3 * si + 3]
            key = f"  | St{st}, S{si} => "
            if t == "---":
                out.append(key + "None")
            else:
                out.append(key + f"mk S{t[0]} {DIRW[t[1]]} {ST[t[2]]}")
    return "\n".join(out)


def zlit(v):
    return f"({v})"


def emit_blks(blk):
    if not blk:
        return "[]"
    entries = []
    for i in sorted(blk):
        cells = "; ".join(SYM[x] for x in blk[i])
        entries.append(f"({i}%nat, [{cells}])")
    return "[" + ";\n   ".join(entries) + "]"


def emit_tpl(d):
    runs = [d[i] for i in sorted(d)]
    if not runs:
        return "[]"
    parts = [f"({s}%nat, {zlit(al)}, {zlit(be)})" for (s, al, be) in runs]
    return "[" + "; ".join(parts) + "]"


def emit_rcnt(rc):
    if rc[0] == "C":
        return f"BC {zlit(rc[1])}"
    if rc[0] == "V":
        return f"BV {zlit(rc[1])} {zlit(rc[2])}"
    # ("Vm", del, lb, mod, res)
    return f"BVm {zlit(rc[1])} {zlit(rc[2])} {zlit(rc[3])} {zlit(rc[4])}"


def emit_rule_side(d):
    runs = [d[i] for i in sorted(d)]
    parts = [f"({s}%nat, {emit_rcnt(rc)})" for (s, rc) in runs]
    return "[" + "; ".join(parts) + "]"


def emit_pfx(pfx):
    pl, pr = pfx
    return f"({'true' if pl else 'false'}, {'true' if pr else 'false'})"


def emit_rules(rules, pfxmap):
    if not rules:
        return "[]"
    out = []
    for i in sorted(rules):
        rd = rules[i]
        pfx = pfxmap.get(i, (False, False))
        out.append(f"mkBRuleP {ST[rd['st']]} S{rd['hs']} "
                   f"{emit_rule_side(rd['L'])} {emit_rule_side(rd['R'])} "
                   f"{emit_pfx(pfx)}")
    return "[" + ";\n   ".join(out) + "]"


def cert_stats(c):
    """Count-wise summary of a parsed cert (for the selftest)."""
    nruns = 0
    npfx = 0
    nvm = 0
    for i in c["rules"]:
        rd = c["rules"][i]
        for side in ("L", "R"):
            for k in rd[side]:
                nruns += 1
                if rd[side][k][1][0] == "Vm":
                    nvm += 1
    for i in c["pfx"]:
        pl, pr = c["pfx"][i]
        if pl or pr:
            npfx += 1
    return {"rules": len(c["rules"]), "runs": nruns,
            "pfx_set": npfx, "vm_runs": nvm, "blks": len(c["blk"])}


def emit_machine(path):
    c = parse_cert(path)
    m = c["machine"]
    nm = cname(m)
    tm = emit_tm(m)
    a, b = c["meta_a"], c["meta_b"]
    npfx = sum(1 for i in c["pfx"] if c["pfx"][i][0] or c["pfx"][i][1])
    s = []
    s.append(f"(** ** {m}: anchor {c['anchor_step']}, k0 {c['k0']}, "
             f"map k -> {a}*k+{b}, {len(c['rules'])} rule(s) "
             f"({npfx} prefix), {len(c['blk'])} block(s) *)")
    s.append(f"Definition tmbp_{nm} : TM := fun q s =>")
    s.append("  match q, s with")
    s.append(tm)
    s.append("  end.")
    s.append(f"Definition certbp_{nm} : BIRCertP := mkBIRCertP")
    s.append(f"  {c['anchor_step']}%nat {zlit(c['k0'])} {zlit(c['kmin'])} "
             f"{zlit(a)} {zlit(b)} {ST[c['tpl_state']]} S{c['tpl_hsym']}")
    s.append(f"  {emit_blks(c['blk'])}")
    s.append(f"  {emit_tpl(c['tplL'])}")
    s.append(f"  {emit_tpl(c['tplR'])}")
    s.append(f"  {emit_rules(c['rules'], c['pfx'])}.")
    s.append(f"Theorem irbp_{nm}_never_quasihalts : "
             f"NeverQuasiHaltsSt tmbp_{nm}.")
    s.append("Proof.")
    s.append(f"  apply (irulesblkpfx_check_neverqh_sound tmbp_{nm} certbp_{nm} "
             f"{CFUEL} {FUEL}).")
    s.append("  vm_compute. reflexivity.")
    s.append("Qed.")
    s.append(f"Theorem irbp_{nm}_nonhalt : NonHalt tmbp_{nm}.")
    s.append(f"Proof. apply never_qh_nonhalt, irbp_{nm}_never_quasihalts. Qed.")
    return "\n".join(s), nm


HEADER = '''(** GENERATED by tools/gen_irulesblkpfx_certs.py -- DO NOT EDIT.

    Prefix block-run inductive-rules machines from the BBB harness's
    v6/v7 certificate sets (Phase 2: [rulepfx] + [rmdok], [rulerunm]).
    Per machine: the TM, the [BIRCertP] literal (block table + template
    + prefix rules) straight from its certificate, the
    [NeverQuasiHaltsSt] theorem closed by
    [irulesblkpfx_check_neverqh_sound] (MetaBlkPfx) + [vm_compute], and
    the [NonHalt] corollary.  The certificates are UNTRUSTED search
    output; every claim is re-checked by the verified Phase-2 block
    IRules engine (theories/Checkers/IRules/EngineKS.v + RulesBlkPfx.v
    + MetaBlkPfx.v). *)

From Coq Require Import ZArith List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import Cycle.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta RulesK
     EngineK RulesBlk MetaBlk EngineKS RulesBlkPfx MetaBlkPfx.
Import ListNotations.
Open Scope Z_scope.
Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).
'''


def main():
    out, name = sys.argv[1], sys.argv[2]
    certs = sys.argv[3:]
    blocks = []
    names = []
    for p in certs:
        body, nm = emit_machine(p)
        blocks.append(body)
        names.append(nm)
    with open(out, "w") as f:
        f.write(HEADER + "\n")
        f.write("\n\n".join(blocks) + "\n")
    print(f"wrote {out}: {len(names)} machines", file=sys.stderr)
    for nm in names:
        print(nm)


if __name__ == "__main__":
    main()
