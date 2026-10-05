#!/usr/bin/env python3
"""Emit/replay AST160: nested token passes with a decreasing block count."""
import argparse
import itertools
from pathlib import Path
import tempfile
import cbt
from period3_batch import row, table

SOURCE = '1RB0LC_1RC1RD_1LA1LC_1RD0RA'
TARGET = '1RB1RD_1LC1LB_1RA0LB_1RD0RC'
PERMUTATION = [2, 0, 1, 3]


def emit():
    source, target = table(SOURCE), table(TARGET)
    for q, symbol in itertools.product(range(4), range(2)):
        write, direction, next_state = source[2*q+symbol]
        assert target[2*PERMUTATION[q]+symbol] == (
            write, direction, PERMUTATION[next_state])
    name = 'AST_160_0000'
    arms = ' | '.join(f'St{chr(65+q)}=>St{chr(65+p)}'
                      for q,p in enumerate(PERMUTATION))
    preamble = f'''Definition source_{name}:TM := row_to_tm {row(SOURCE)}.
Definition perm_{name}(q:St):St := match q with {arms} end.
Definition family_{name}(x:list bool):cconf := kv_anchor x.'''
    cases = '\n'.join(f'  - exact(Hrec(St{chr(65+PERMUTATION.index(q))},s)N).' for q in range(4))
    proof = f'''assert(Hprogress:forall x,exists y,
    Reach1 source_{name}(family_{name} x)(family_{name} y)).
  {{ intro w. destruct(kv_return source_{name} eq_refl eq_refl eq_refl eq_refl
      eq_refl eq_refl eq_refl eq_refl w)as(u&HU).
    exists(true::u);exact HU. }}
  assert(Hrec:forall q N,exists j,N<=j /\\
    FiresAt(row_to_tm r_{name})(perm_{name}(fst q),snd q)j).
  {{ intro q. apply(conjugate_marked_return_fire source_{name} _ perm_{name} false
      _ family_{name} q 0 []).
    - intros[] [];reflexivity.
    - rewrite <-lift_c0. apply csteps_lift. vm_compute;reflexivity.
    - exact Hprogress.
    - intro w. apply(kv_anchor_fires source_{name} eq_refl eq_refl eq_refl eq_refl
        eq_refl eq_refl eq_refl eq_refl w q). }}
  apply coversTr_nqh. intros[q s] _ N;destruct q.
{cases}'''
    return cbt.write_batch('AST', 160,
        ['From BBB4 Require Import CTape.',
         'From BBB4.Counters Require Import CConjugateTr NestCountTr LoopRunTr MarkedReturnTr BlockCoreKVariantTr.'],
        [(TARGET, proof)], 'nested finite token passes and all eight instruction witnesses',
        preamble=preamble)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    target = Path(cbt.batch_path('AST', 160))
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
