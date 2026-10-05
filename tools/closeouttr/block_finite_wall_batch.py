#!/usr/bin/env python3
"""Emit/replay AST153: a finite right wall and marked A0 returns."""
import itertools
from pathlib import Path
import cbt
from period3_batch import row, table
from balanced_carry_batch import main


def emit(records):
    preamble, entries = [], []
    for i, record in enumerate(records):
        name = f'AST_153_{i:04d}'
        permutation, flip = record['p'], record['flip']
        assert sorted(permutation) == list(range(4))
        assert record['failed'] == [[permutation[0], 0]]
        assert record['mirrored'] and record['t'] == 0
        source, target = table(record['source']), table(record['spec'])
        for q, symbol in itertools.product(range(4), range(2)):
            write, direction, next_state = source[2*q+symbol]
            if flip:
                direction = 'L' if direction == 'R' else 'R'
            assert target[2*permutation[q]+symbol] == (
                write, direction, permutation[next_state])
        instruction = f'(St{chr(65+permutation[0])},S0)'
        arms = ' | '.join(f'St{chr(65+q)}=>St{chr(65+p)}'
                          for q, p in enumerate(permutation))
        preamble.append(f'''Definition cert_{name}:Instr->list fmxcomp*list positive :=
{record['cert']}.
Definition source_{name} := row_to_tm {row(record['source'])}.
Definition perm_{name}(q:St):St := match q with {arms} end.
Definition family_{name}(x:{{c:cconf | bcg_mark c}}):cconf := proj1_sig x.
Definition boot_{name}:{{c:cconf | bcg_mark c}}.
Proof.
 exists bcg_initial;apply bcg_initial_mark.
Defined.
Definition skip_{name}(t:Instr):bool := instr_eqb t {instruction}.''')
        proof = f'''assert(Hprogress:forall x,exists y,
    Reach1 source_{name}(family_{name} x)(family_{name} y)).
  {{ intros[c Hc]. destruct(bcg_return source_{name} eq_refl eq_refl eq_refl eq_refl
      eq_refl eq_refl eq_refl eq_refl c Hc)as(d&Hd&Hrun).
    exists(exist bcg_mark d Hd);exact Hrun. }}
  assert(Hrec:forall N,exists j,N<=j /\\ FiresAt(row_to_tm r_{name}){instruction}j).
  {{ apply(conjugate_marked_return_fire source_{name} _ perm_{name} {str(flip).lower()}
      _ family_{name} (StA,S0) {record['boot']} boot_{name}).
    - intros[] [];reflexivity.
    - rewrite <-lift_c0. apply csteps_lift. vm_compute;reflexivity.
    - exact Hprogress.
    - intros[c Hc];apply fires_here;apply bcg_mark_instr;exact Hc. }}
  apply coversTr_nqh,neverqhtr_mirror.
  apply(ngram_check_neverqh_fuelmixtr_except_sound _ {record['n']} 0 {record['fuel']} {record['rounds']}
    skip_{name} cert_{name}).
  - intros[[] []] H N;try discriminate.
    destruct(Hrec N)as(j&Hj&Hf). exists j;split;[exact Hj|apply mirror_fires;exact Hf].
  - vm_compute;reflexivity.'''
        entries.append((record['spec'], proof))
    return cbt.write_batch('AST', 153,
        ['From BBB4 Require Import CTape Mirror.',
         'From BBB4.Checkers Require Import NGram FuelMixTr FuelMixPartialTr.',
         'From BBB4.Checkers.IRules Require Import AnchorVisitsTr.',
         'From BBB4.Counters Require Import CConjugateTr WTape NestCountTr LoopRunTr MarkedReturnTr BlockCoreGReturnTr.',
         'From BBB4.CensusTr Require Import TNF_QHTr.'], entries,
        'finite right walls and marked A0 returns',
        preamble='\n\n'.join(preamble))


if __name__ == '__main__':
    main(Path(__file__).with_name('block_finite_wall_ast.json'), 153, emit)
