#!/usr/bin/env python3
"""Emit/replay AST156: an odd-count finite-word transducer."""
import argparse
from pathlib import Path
import tempfile
import cbt
from period3_batch import row

SOURCE = '1RB0RC_0LC1LB_0LD1LC_1RD0RA'


def emit():
    name = 'AST_156_0000'
    preamble = f'''Definition source_{name}:TM := row_to_tm {row(SOURCE)}.
Definition family_{name}(x:{{c:cconf | bo_mark c}}):cconf := proj1_sig x.
Definition boot_{name}:{{c:cconf | bo_mark c}}.
Proof. exists(bo_anchor[S1]);apply bo_mark_anchor;[apply bo_nil|exists 0;reflexivity]. Defined.'''
    proof = f'''assert(Hprogress:forall x,exists y,
    Reach1 source_{name}(family_{name} x)(family_{name} y)).
  {{ intros[c Hc]. destruct(bo_return source_{name} eq_refl eq_refl eq_refl eq_refl
      eq_refl eq_refl eq_refl eq_refl c Hc)as(d&Hd&Hrun).
    exists(exist bo_mark d Hd);exact Hrun. }}
  assert(Hrec:forall q N,exists j,N<=j /\\ FiresAt(row_to_tm r_{name})q j).
  {{ intros[q s]. apply(conjugate_marked_return_fire source_{name} _ (fun q=>q) false
      _ family_{name} (q,s) 12 boot_{name}).
    - intros[] [];reflexivity.
    - apply bo_boot;reflexivity.
    - exact Hprogress.
    - intros[c Hc]. apply bo_mark_fires;try reflexivity;exact Hc. }}
  apply coversTr_nqh. intros q _ N;exact(Hrec q N).'''
    return cbt.write_batch('AST', 156,
        ['From BBB4 Require Import CTape.',
         'From BBB4.Counters Require Import CConjugateTr NestCountTr LoopRunTr MarkedReturnTr BlockCoreOReturnTr.'],
        [(SOURCE, proof)], 'odd-count word induction and eight instruction witnesses',
        preamble=preamble)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    target = Path(cbt.batch_path('AST', 156))
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
