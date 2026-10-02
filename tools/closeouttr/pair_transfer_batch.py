#!/usr/bin/env python3
"""Emit a conjugate pair with finite pair transfers and a doubling reset.

    python3 tools/closeouttr/pair_transfer_batch.py --number 43
"""
import argparse
from cbt import write_batch


def batch(number, overwrite=False):
    source = 'r_AST_%02d_0000' % number
    target = 'r_AST_%02d_0001' % number
    first = rf'''apply coversTr_nqh, (pt_neverqhtr (row_to_tm {source}) ltac:(reflexivity) ltac:(reflexivity)
    ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
    ltac:(reflexivity) ltac:(reflexivity) 45).
  exists 5150.
  assert (E : exists c, csteps (row_to_tm {source}) 5150 c0 = Some c /\
    ceqb c (pt_anchor 0 45) = true).
  {{ eexists. split; vm_compute; reflexivity. }}
  destruct E as (c&Ec&El). rewrite <-lift_c0.
  rewrite (csteps_lift _ _ _ _ Ec), (ceqb_lift _ _ El). reflexivity.'''
    second = rf'''apply coversTr_nqh.
  assert (Htable : forall q s, row_to_tm {target} (pt_target q) s =
    option_map (tconj pt_target true) (row_to_tm {source} q s))
    by (intros [] []; reflexivity).
  apply (cconj_value_neverqhtr (row_to_tm {source})
    (row_to_tm {target}) pt_target true Htable nat (fun k => 2*k+11)
    pt_anchor 162).
  - intros []; [exists StC | exists StA | exists StB | exists StD]; reflexivity.
  - exists 79717.
    assert (E : exists c, csteps (row_to_tm {target}) 79717 c0 = Some c /\
      ceqb c (cconj pt_target true (pt_anchor 0 162)) = true).
    {{ eexists. split; vm_compute; reflexivity. }}
    destruct E as (c&Ec&El). rewrite <-lift_c0.
    rewrite (csteps_lift _ _ _ _ Ec), (ceqb_lift _ _ El). reflexivity.
  - intros n k. apply pt_lap; reflexivity.
  - intros n k t. apply pt_fires; reflexivity.'''
    write_batch('AST', number,
                ['From BBB4 Require Import CTape.',
                 'From BBB4.Counters Require Import PairTransferTr CConjugateTr.'],
                [('1RB0LC_1LC1RD_1LA0LB_0RB0RC', first),
                 ('1RB0RC_1LC0RA_1RA1LD_0LC0LA', second)],
                'finite pair transfers with direct instruction witnesses',
                overwrite=overwrite,
                preamble='Local Definition pt_target (q:St):St:=\n'
                '  match q with StA=>StB | StB=>StC | StC=>StA | StD=>StD end.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--number', type=int, default=43)
    parser.add_argument('--overwrite', action='store_true')
    args = parser.parse_args()
    batch(args.number, args.overwrite)


if __name__ == '__main__':
    main()
