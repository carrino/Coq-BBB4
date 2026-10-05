#!/usr/bin/env python3
"""Emit/replay AST159: a productive run grammar and exact two-pass returns."""
import argparse
from pathlib import Path
import tempfile
import cbt
from period3_batch import row

SOURCE = '1RB1RA_0LC0RA_1LC1LD_1LA0LC'


def emit():
    name = 'AST_159_0000'
    preamble = f'''Definition source_{name}:TM := row_to_tm {row(SOURCE)}.
Definition family_{name}(x:{{c:cconf | bl_mark c}}):cconf := proj1_sig x.
Definition boot_{name}:{{c:cconf | bl_mark c}}.
Proof. exists(bl_anchor(bl_runs[4;7;1]));apply bl_mark_runs,bl_good_initial. Defined.'''
    proof = f'''assert(Hprogress:forall x,exists y,
    Reach1 source_{name}(family_{name} x)(family_{name} y)).
  {{ intros[c Hc]. destruct(bl_mark_return source_{name} eq_refl eq_refl eq_refl eq_refl
      eq_refl eq_refl eq_refl eq_refl c Hc)as(d&Hd&Hrun).
    exists(exist bl_mark d Hd);exact Hrun. }}
  assert(Hrec:forall q N,exists j,N<=j /\\ FiresAt(row_to_tm r_{name})q j).
  {{ intros[q s]. apply(conjugate_marked_return_fire source_{name} _ (fun q=>q) false
      _ family_{name} (q,s) 80 boot_{name}).
    - intros[] [];reflexivity.
    - rewrite <-lift_c0. apply csteps_lift. vm_compute;reflexivity.
    - exact Hprogress.
    - intros[c Hc]. apply(bl_mark_fires source_{name} eq_refl eq_refl eq_refl eq_refl
        eq_refl eq_refl eq_refl eq_refl c Hc(q,s)). }}
  apply coversTr_nqh. intros q _ N;exact(Hrec q N).'''
    return cbt.write_batch('AST', 159,
        ['From BBB4 Require Import CTape.',
         'From BBB4.Counters Require Import CConjugateTr NestCountTr LoopRunTr MarkedReturnTr BlockCoreLWordsTr BlockCoreLReturnTr BlockCoreLGlueTr.'],
        [(SOURCE, proof)], 'a productive run grammar and two exact word passes',
        preamble=preamble)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    target = Path(cbt.batch_path('AST', 159))
    with tempfile.TemporaryDirectory() as tmp:
        cbt.CT = tmp
        generated = Path(emit()).read_text()
    if args.check:
        assert target.read_text() == generated
    else:
        target.write_text(generated)
    print(('checked' if args.check else 'wrote'), target)


if __name__ == '__main__':
    main()
