#!/usr/bin/env python3
"""Emit the two instances of GeometricCounterTr.

    python3 tools/closeouttr/geometric_counter_batch.py --number 92
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cbt import write_batch

ROWS = [
    ("1RB1RA_1LC0RA_1LD1LC_1RD0LB", False, ("StA", "StB", "StC", "StD"), 18, 3),
    ("1RB0LD_1RC1RB_1LC0RA_1LA1LD", True, ("StD", "StA", "StB", "StC"), 14, 2),
]


def batch(number, overwrite):
    entries = []
    for spec, mirrored, states, boot, count in ROWS:
        proof = "apply coversTr_nqh, " + ("neverqhtr_mirror.\n  " if mirrored else "")
        if not mirrored:
            proof = "apply coversTr_nqh.\n  "
        proof += """eapply geometric_counter_neverqhtr with
    (qa:=%(qa)s)(qb:=%(qb)s)(qc:=%(qc)s)(qd:=%(qd)s);try reflexivity.
  - intros [];auto 6.
  - exists %(boot)d,false,0,%(count)d. split;[lia|].
    rewrite <-lift_c0. apply csteps_lift. vm_compute. reflexivity.""" % dict(
                qa=states[0], qb=states[1], qc=states[2], qd=states[3], boot=boot, count=count)
        entries.append((spec, proof))
    write_batch("AST", number,
                ["From Coq Require Import Lia.", "From BBB4 Require Import CTape Mirror.",
                 "From BBB4.Counters Require Import GeometricCounterTr.",
                 "From BBB4.CensusTr Require Import TNF_QHTr."],
                entries, "finite binary counter overflow between periodic sweeps",
                overwrite=overwrite)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--number", type=int, default=92)
    parser.add_argument("--overwrite", action="store_true")
    args = parser.parse_args()
    batch(args.number, args.overwrite)


if __name__ == "__main__":
    main()
