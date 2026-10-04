#!/usr/bin/env python3
"""Emit/replay AST154: signed binary words and two uniform sweeps."""
import argparse
import itertools
from pathlib import Path
import tempfile
import cbt
from period3_batch import row, table

SOURCE = '1RB0LC_1RC0RD_1LA0LC_1RD0RA'
ROWS = [
    (SOURCE, [0, 1, 2, 3], 27, 1),
    ('1RB0RD_1LC0LB_1RA0LB_1RD0RC', [2, 0, 1, 3], 51, 2),
]


def emit():
    preamble, entries = [], []
    for i, (spec, permutation, boot, n) in enumerate(ROWS):
        name = f'AST_154_{i:04d}'
        source, target = table(SOURCE), table(spec)
        assert sorted(permutation) == list(range(4))
        for q, symbol in itertools.product(range(4), range(2)):
            write, direction, next_state = source[2*q+symbol]
            assert target[2*permutation[q]+symbol] == (write, direction, permutation[next_state])
        arms = ' | '.join(f'St{chr(65+q)}=>St{chr(65+p)}' for q, p in enumerate(permutation))
        preamble.append(f'''Definition source_{name}:TM := row_to_tm {row(SOURCE)}.
Definition perm_{name}(q:St):St := match q with {arms} end.
Definition family_{name}(x:{{c:cconf | bk_mark c}}):cconf := proj1_sig x.
Definition boot_{name}:{{c:cconf | bk_mark c}}.
Proof. exists(bk_anchor {n}[S1]);apply bk_marked;[lia|vm_compute;reflexivity]. Defined.''')
        cases = '\n'.join(f'  - exact(Hrec(St{chr(65+permutation.index(q))},s)N).' for q in range(4))
        proof = f'''assert(Hprogress:forall x,exists y,
    Reach1 source_{name}(family_{name} x)(family_{name} y)).
  {{ intros[c Hc]. destruct(bk_return source_{name} eq_refl eq_refl eq_refl eq_refl
      eq_refl eq_refl eq_refl eq_refl c Hc)as(d&Hd&Hrun).
    exists(exist bk_mark d Hd);exact Hrun. }}
  assert(Hrec:forall q N,exists j,N<=j /\\
    FiresAt(row_to_tm r_{name})(perm_{name}(fst q),snd q)j).
  {{ intro q. apply(conjugate_marked_return_fire source_{name} _ perm_{name} false
      _ family_{name} q {boot} boot_{name}).
    - intros[] [];reflexivity.
    - rewrite <-lift_c0. apply csteps_lift. vm_compute;reflexivity.
    - exact Hprogress.
    - intros[c Hc]. apply(bk_mark_fires source_{name} eq_refl eq_refl eq_refl eq_refl
        eq_refl eq_refl eq_refl c Hc q). }}
  apply coversTr_nqh. intros[q s] _ N;destruct q.
{cases}'''
        entries.append((spec, proof))
    return cbt.write_batch('AST', 154,
        ['From Coq Require Import Lia.',
         'From BBB4 Require Import CTape.',
         'From BBB4.Counters Require Import CConjugateTr NestCountTr LoopRunTr MarkedReturnTr BlockCoreKValueTr BlockCoreKReturnTr BlockCoreKFireTr.'],
        entries, 'positive signed binary values and two uniform sweeps',
        preamble='\n\n'.join(preamble))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    target = Path(cbt.batch_path('AST', 154))
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
