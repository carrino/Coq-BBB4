#!/usr/bin/env python3
"""Reproduce AST113's two checked conjugate bootstraps."""
import argparse
from pathlib import Path
import tempfile
import cbt
from cbt import write_batch
pre='''Local Definition moving_p (q:St):St :=
 match q with StA=>StC|StB=>StD|StC=>StA|StD=>StB end.
Local Definition fuel_p (q:St):St :=
 match q with StA=>StB|StB=>StC|StC=>StA|StD=>StD end.
Local Definition fuel_pi (q:St):St :=
 match q with StA=>StC|StB=>StA|StC=>StB|StD=>StD end.'''
entries=[('0RB0LB_1LC1RD_0LD0LC_1RA1LC', '''apply(CBT_AST_50.moving_conj_cover true _ moving_p true 2 22).
 - intros[] [];reflexivity.
 - intros[];first[exists StA;reflexivity|exists StB;reflexivity|exists StC;reflexivity|exists StD;reflexivity].
 - vm_compute;reflexivity.'''),('1RB1LB_0LC1RD_1LA0RB_1LB0RD','''apply coversTr_nqh.
 apply(cconj_nqh_run(row_to_tm CBT_AST_32.r_AST_32_0000) _ fuel_p fuel_pi true 0 3 10).
 - intros[];reflexivity.
 - intros[];reflexivity.
 - intros[] [];reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - apply neverqhtr_mirror.
   apply(ngram_check_neverqh_fuelwtr_sound _ 7 0 31112 105 CBT_AST_32.fueltr_AST_32_0000).
   vm_compute;reflexivity.''')]
def emit():
 return write_batch('AST',113,['From BBB4 Require Import CTape.','From BBB4.Counters Require Import CConjCoverTr.','From BBB4.Checkers Require Import NGram FuelWideTr.','From BBB4.CensusTr Require Import TNF_QHTr.','From BBB4.CloseoutTr Require CBT_AST_50 CBT_AST_32.'],entries,'token-family and instruction-certificate conjugates with different initial boots',preamble=pre)


if __name__ == '__main__':
 parser = argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--check', action='store_true')
 args = parser.parse_args()
 target = Path(cbt.batch_path('AST',113))
 with tempfile.TemporaryDirectory() as tmp:
  cbt.CT = tmp
  text = Path(emit()).read_text()
 if args.check:
  assert target.read_text() == text, target
 else:
  target.write_text(text)
 print(('checked' if args.check else 'wrote'), target)
