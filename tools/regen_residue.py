#!/usr/bin/env python3
"""Recompute the census residue after the verified-tier sweeps and
regenerate the Deferred_* tables (UNTRUSTED tooling).

residue = (wrap_residue_caught - qhbound_caught - qhbound_lex_caught)
          + (wrap_residue_survivors - repwl_residue_caught)

i.e. the committed 52,326-machine residue minus everything the new
census tiers (wrapped QHBound plain/lex, RepWL) decide at walk time.
Set relations are asserted so a stale input fails loudly instead of
silently deferring the wrong machines.

Usage: regen_residue.py HOLDOUTS OUTDIR
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def tsv_col0(path):
    with open(path) as f:
        next(f)
        return {l.split("\t")[0] for l in f if l.strip()}


def txt(path):
    return {l.strip() for l in open(path) if l.strip()}


def main():
    holdouts = sys.argv[1]
    outdir = sys.argv[2]
    wrap_qh = tsv_col0(os.path.join(HERE, "wrap_residue_caught.tsv"))
    core = txt(os.path.join(HERE, "wrap_residue_survivors.txt"))
    qhb = tsv_col0(os.path.join(HERE, "qhbound_caught.tsv"))
    qlx = tsv_col0(os.path.join(HERE, "qhbound_lex_caught.tsv"))
    rw = tsv_col0(os.path.join(HERE, "repwl_residue_caught.tsv"))

    assert len(wrap_qh) == 20568, len(wrap_qh)
    assert len(core) == 31758, len(core)
    assert not (wrap_qh & core)
    assert qhb <= wrap_qh, len(qhb - wrap_qh)
    assert qlx <= wrap_qh, len(qlx - wrap_qh)
    assert not (qhb & qlx)
    assert rw <= core, len(rw - core)

    residue = sorted((wrap_qh - qhb - qlx) | (core - rw))
    print(f"wrap-QH kept {len(wrap_qh - qhb - qlx)} of {len(wrap_qh)} "
          f"(qhb plain {len(qhb)}, lex {len(qlx)})")
    print(f"never-QH core kept {len(core - rw)} of {len(core)} "
          f"(repwl {len(rw)})")
    print(f"new residue {len(residue)}")
    res_path = os.path.join(HERE, "census_residue.txt")
    open(res_path, "w").write("\n".join(residue) + "\n")
    subprocess.run(
        [sys.executable, os.path.join(HERE, "gen_deferred.py"),
         holdouts, res_path, outdir],
        check=True)


if __name__ == "__main__":
    main()
