#!/usr/bin/env python3
"""Emit four doubling-sweep rows and their checked conjugate boots.

DoubleSweepReturnTr proves the uniform pair sweeps, a positive return,
and all eight instruction witnesses.  The other three rows use exact
state maps and reflection through CConjugateTr, with independent boots.

    python3 tools/closeouttr/double_sweep_batch.py --number 40
"""
import argparse

from cbt import write_batch

SOURCE = "1RB0LD_1RC0RA_1LD0RB_1LB0LC"
# Spec, source-to-target state map, reflection, boot, anchor n, anchor k.
CONJUGATES = [
    ("1RB0LC_1RC0RA_1LA0LD_1LC0RB", [3, 2, 0, 1], True, 22, 1, 0),
    ("1RB0RC_1LC0LD_1RA0LB_1LB0RA", [3, 1, 2, 0], True, 13, 0, 0),
    ("1RB0RD_1LC0RA_1LA0LB_1RA0LC", [3, 0, 1, 2], False, 53, 0, 2),
]


def batch(number, overwrite=False):
    source_row = "r_AST_%02d_0000" % number
    entries = [(SOURCE, "apply coversTr_nqh, ds_neverqhtr; reflexivity.")]
    preamble = []
    for index, (spec, mapping, flip, boot, n0, k0) in enumerate(CONJUGATES, 1):
        name = "ds_target_%d" % index
        row = "r_AST_%02d_%04d" % (number, index)
        reflected = str(flip).lower()
        cases = " | ".join("St%s => St%s" % ("ABCD"[q], "ABCD"[mapping[q]])
                           for q in range(4))
        preamble.append("Local Definition %s (q : St) : St :=\n"
                        "  match q with %s end." % (name, cases))
        onto = " | ".join("exists St" + "ABCD"[mapping.index(q)] for q in range(4))
        proof = rf"""apply coversTr_nqh.
  assert (Htable : forall q s, row_to_tm {row} ({name} q) s =
    option_map (tconj {name} {reflected}) (row_to_tm {source_row} q s))
    by (intros [] []; reflexivity).
  apply (cconj_value_neverqhtr (row_to_tm {source_row})
    (row_to_tm {row}) {name} {reflected} Htable nat (fun k => 2*k+2)
    (fun n k => ds_anchor (n+{n0}) k) {k0}).
  - intros []; [{onto}]; reflexivity.
  - exists {boot}.
    assert (E : exists c, csteps (row_to_tm {row}) {boot} c0 = Some c /\
      ceqb c (cconj {name} {reflected} (ds_anchor {n0} {k0})) = true).
    {{ eexists. split; vm_compute; reflexivity. }}
    destruct E as (c&Ec&El). rewrite <-lift_c0.
    rewrite (csteps_lift _ _ _ _ Ec), (ceqb_lift _ _ El). reflexivity.
  - intros n k. apply ds_anchor_lap; reflexivity.
  - intros n k t. apply ds_anchor_fires; reflexivity."""
        entries.append((spec, proof))
    write_batch("AST", number,
                ["From BBB4 Require Import CTape.",
                 "From BBB4.Counters Require Import DoubleSweepReturnTr CConjugateTr."],
                entries, "uniform doubling sweeps with direct instruction witnesses",
                overwrite=overwrite, preamble="\n".join(preamble))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--number", type=int, default=40)
    parser.add_argument("--overwrite", action="store_true")
    args = parser.parse_args()
    batch(args.number, args.overwrite)


if __name__ == "__main__":
    main()
