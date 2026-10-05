#!/usr/bin/env python3
"""Emit/replay AST162: two periodic orbits of the four-row block core C."""
import argparse
import itertools
from pathlib import Path
import tempfile
import cbt
from period3_batch import row, table

SOURCE = '1RB1LB_0LC1RD_1LA1LC_1RB0RB'
ROWS = [
    ('0RB1LD_1RC1RB_1LA1RA_1LA0LA', [2, 0, 1, 3], True, 2, 191),
    ('1RB0RB_0LC1RA_1LD1LC_1RB1LB', [3, 1, 2, 0], False, 1, 21),
    (SOURCE, [0, 1, 2, 3], False, 1, 21),
    ('1RB1RA_1LC1RC_0RA1LD_1LC0LC', [1, 2, 0, 3], True, 2, 190),
]


def emit():
    preamble, proofs = [], []
    for index, (spec, permutation, flip, orbit, boot) in enumerate(ROWS):
        source, target = table(SOURCE), table(spec)
        for q, symbol in itertools.product(range(4), range(2)):
            write, direction, next_state = source[2*q+symbol]
            if flip:
                direction = 'L' if direction == 'R' else 'R'
            assert target[2*permutation[q]+symbol] == (
                write, direction, permutation[next_state])
        name = f'AST_162_{index:04d}'
        suffix = '2' if orbit == 2 else ''
        arms = ' | '.join(f'St{chr(65+q)}=>St{chr(65+p)}'
                          for q, p in enumerate(permutation))
        preamble.append(f'''Definition source_{name}:TM := row_to_tm {row(SOURCE)}.
Definition perm_{name}(q:St):St := match q with {arms} end.
Definition family_{name}(n:nat):cconf := bco_anchor{suffix} n.''')
        cases = '\n'.join(f'  - exact(Hrec(St{chr(65+permutation.index(q))},s)N).'
                          for q in range(4))
        proof = f'''assert(Htable:forall q h,source_{name} q h=bco_tm q h).
  {{ intros[] [];reflexivity. }}
  assert(Hprogress:forall n,exists m,
    Reach1 source_{name}(family_{name} n)(family_{name} m)).
  {{ intro n;exists(S n);apply(bco_return{suffix} source_{name} Htable). }}
  assert(Hrec:forall q N,exists j,N<=j /\\
    FiresAt(row_to_tm r_{name})(perm_{name}(fst q),snd q)j).
  {{ intro q. apply(conjugate_marked_return_fire source_{name} _ perm_{name} {str(flip).lower()}
      _ family_{name} q {boot} 0).
    - intros[] [];reflexivity.
    - apply boot_ok;vm_compute;reflexivity.
    - exact Hprogress.
    - intro n;apply(bco_fires{suffix} source_{name} Htable n q). }}
  apply coversTr_nqh. intros[q s] _ N;destruct q.
{cases}'''
        proofs.append((spec, proof))
    return cbt.write_batch('AST', 162,
        ['From BBB4 Require Import CTape.',
         'From BBB4.Counters Require Import CConjugateTr NestCountTr LoopRunTr MarkedReturnTr BlockCoreCOrbitDefsTr BlockCoreCOrbitReturnTr.'],
        proofs, 'periodic block growth and all eight instruction witnesses',
        preamble='\n\n'.join(preamble))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    target = Path(cbt.batch_path('AST', 162))
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
