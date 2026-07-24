#!/usr/bin/env python3
"""Emit ONLY the TM + BIRCertP literal (no theorem) for a list of certs,
so an ad-hoc Coq probe can Eval vm_compute the checker sub-terms.
Usage: emit_probe_certs.py CERT [CERT ...]  > body.v
"""
import sys, os, importlib.util

_spec = importlib.util.spec_from_file_location(
    "genbp", os.path.join(os.path.dirname(os.path.abspath(__file__)),
                          "gen_irulesblkpfx_certs.py"))
G = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(G)


def emit_body(path):
    c = G.parse_cert(path)
    m = c["machine"]
    nm = G.cname(m)
    tm = G.emit_tm(m)
    a, b = c["meta_a"], c["meta_b"]
    s = []
    s.append(f"(* {m}: anchor {c['anchor_step']}, k0 {c['k0']}, "
             f"kmin {c['kmin']}, map k -> {a}*k+{b}, {len(c['rules'])} rule(s), "
             f"{len(c['blk'])} block(s) *)")
    s.append(f"Definition tmbp_{nm} : TM := fun q s =>")
    s.append("  match q, s with")
    s.append(tm)
    s.append("  end.")
    s.append(f"Definition certbp_{nm} : BIRCertP := mkBIRCertP")
    s.append(f"  {c['anchor_step']}%nat {G.zlit(c['k0'])} {G.zlit(c['kmin'])} "
             f"{G.zlit(a)} {G.zlit(b)} {G.ST[c['tpl_state']]} S{c['tpl_hsym']}")
    s.append(f"  {G.emit_blks(c['blk'])}")
    s.append(f"  {G.emit_tpl(c['tplL'])}")
    s.append(f"  {G.emit_tpl(c['tplR'])}")
    s.append(f"  {G.emit_rules(c['rules'], c['pfx'])}.")
    return "\n".join(s), nm


def main():
    names = []
    for p in sys.argv[1:]:
        body, nm = emit_body(p)
        print(body)
        print()
        names.append(nm)
    sys.stderr.write("names: " + " ".join(names) + "\n")


if __name__ == "__main__":
    main()
