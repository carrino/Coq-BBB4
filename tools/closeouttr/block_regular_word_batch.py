#!/usr/bin/env python3
"""Emit/replay AST158: a finite grammar closed under the word map."""
import argparse
from pathlib import Path
import tempfile
import cbt
from period3_batch import row

ROWS = [('1RB0RD_1LC1LB_1RA0LB_0RB1RA', 'left'),
        ('1RB0RD_1LC1LB_1RA0LB_1LC1RA', 'right')]


def emit():
    entries, preambles = [], []
    for i, (spec, side) in enumerate(ROWS):
        name = f'AST_158_{i:04d}'
        preambles.append(f'''Definition source_{name}:TM := row_to_tm {row(spec)}.
Definition family_{name}(x:{{c:cconf | bn_mark c}}):cconf := proj1_sig x.
Definition boot_{name}:{{c:cconf | bn_mark c}}.
Proof. exists(bn_anchor(bn_A0 0));apply bn_seed_mark. Defined.''')
        proof = f'''assert(Hprogress:forall x,exists y,
    Reach1 source_{name}(family_{name} x)(family_{name} y)).
  {{ intros[c Hc]. destruct(bn_return source_{name} eq_refl eq_refl eq_refl eq_refl
      eq_refl eq_refl ltac:({side};reflexivity) eq_refl c Hc)as(d&Hd&Hrun).
    exists(exist bn_mark d Hd);exact Hrun. }}
  destruct(bn_boot source_{name} eq_refl eq_refl eq_refl eq_refl
    eq_refl eq_refl ltac:({side};reflexivity) eq_refl)as(boot&Hboot).
  assert(Hrec:forall q N,exists j,N<=j /\\ FiresAt(row_to_tm r_{name})q j).
  {{ intros[q s]. apply(conjugate_marked_return_fire source_{name} _ (fun q=>q) false
      _ family_{name} (q,s) boot boot_{name}).
    - intros[] [];reflexivity.
    - exact Hboot.
    - exact Hprogress.
    - intros[c Hc]. apply bn_mark_fires;try reflexivity;[ {side};reflexivity | exact Hc ]. }}
  apply coversTr_nqh. intros q _ N;exact(Hrec q N).'''
        entries.append((spec, proof))
    return cbt.write_batch('AST', 158,
        ['From BBB4 Require Import CTape.',
         'From BBB4.Counters Require Import CConjugateTr NestCountTr LoopRunTr MarkedReturnTr BlockCoreNWordTr BlockCoreNReturnTr.'],
        entries, 'a closed phase grammar and eight instruction witnesses',
        preamble='\n\n'.join(preambles))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    target = Path(cbt.batch_path('AST', 158))
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
