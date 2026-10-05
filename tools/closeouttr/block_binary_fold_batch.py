#!/usr/bin/env python3
"""Emit/replay AST161: finite-stack ranks and checked boundary returns."""
import itertools
from pathlib import Path
import cbt
from period3_batch import row, table
from balanced_carry_batch import main


def emit(records):
    preamble, entries = [], []
    targets = [(0, 1), (1, 0), (1, 1), (2, 1), (3, 0), (3, 1)]
    for i, record in enumerate(records):
        name = f'AST_161_{i:04d}'
        permutation = record['p']
        assert sorted(permutation) == list(range(4))
        assert not record['flip']
        assert record['failed'] == sorted([[permutation[q], s] for q, s in targets])
        assert record['mirrored'] and record['t'] == 0
        source, target = table(record['source']), table(record['spec'])
        for q, symbol in itertools.product(range(4), range(2)):
            write, direction, next_state = source[2*q+symbol]
            assert target[2*permutation[q]+symbol] == (
                write, direction, permutation[next_state])
        skip = ' || '.join(f'instr_eqb t (St{chr(65+permutation[q])},S{s})' for q, s in targets)
        cases = '\n'.join(f'    destruct(Hrec (St{chr(65+q)},S{s}) ltac:(discriminate) ltac:(discriminate) N)as(j&Hj&Hf); exists j;split;[exact Hj|apply mirror_fires;exact Hf].' for q,s in sorted(targets, key=lambda x:(permutation[x[0]],x[1])))
        arms = ' | '.join(f'St{chr(65+q)}=>St{chr(65+p)}'
                          for q, p in enumerate(permutation))
        preamble.append(f'''Definition cert_{name}:Instr->list fmxcomp*list positive :=
{record['cert']}.
Definition source_{name}:TM := row_to_tm {row(record['source'])}.
Definition perm_{name}(q:St):St := match q with {arms} end.
Definition family_{name}(x:{{c:cconf | ms_mark c}}):cconf := proj1_sig x.
Definition boot_{name}:{{c:cconf | ms_mark c}} :=
  exist ms_mark (StB,(ms_P0,S0,[])) ms_boot_mark.
Definition skip_{name}(t:Instr):bool := {skip}.''')
        proof = f'''assert(Htable:forall q h,source_{name} q h=bm_tm q h).
  {{ intros[] [];reflexivity. }}
  assert(Hprogress:forall x,exists y,
    Reach1 source_{name}(family_{name} x)(family_{name} y)).
  {{ intros[c Hc]. destruct(ms_return source_{name} Htable c Hc)as(d&Hd&Hrun).
    exists(exist ms_mark d Hd);exact Hrun. }}
  assert(Hrec:forall q,q<>(StA,S0)->q<>(StC,S0)->
    forall N,exists j,N<=j /\\ FiresAt(row_to_tm r_{name})(perm_{name}(fst q),snd q)j).
  {{ intros q HA HC. apply(conjugate_marked_return_fire source_{name} _ perm_{name} false
      _ family_{name} q {record['boot']} boot_{name}).
    - intros[] [];reflexivity.
    - apply boot_ok;vm_compute;reflexivity.
    - exact Hprogress.
    - intros[c Hc]. apply(mg_mark_fires source_{name} Htable c q Hc HA HC). }}
  apply coversTr_nqh,neverqhtr_mirror.
  apply(ngram_check_neverqh_fuelmixtr_except_sound _ {record['n']} 0 {record['fuel']} {record['rounds']}
    skip_{name} cert_{name}).
  - intros[[] []] H N;try discriminate.
{cases}
  - vm_compute;reflexivity.'''
        entries.append((record['spec'], proof))
    return cbt.write_batch('AST', 161,
        ['From BBB4 Require Import CTape Mirror.',
         'From BBB4.Checkers Require Import NGram FuelMixTr FuelMixPartialTr.',
         'From BBB4.Checkers.IRules Require Import AnchorVisitsTr.',
         'From BBB4.Counters Require Import CConjugateTr WTape NestCountTr LoopRunTr MarkedReturnTr BlockCoreMReturnTr BlockCoreMStrongTr BlockCoreMGlueTr.',
         'From BBB4.CensusTr Require Import TNF_QHTr.'], entries,
        'binary stack ranks, guarded boundary returns, and instruction recurrence',
        preamble='\n\n'.join(preamble))


if __name__ == '__main__':
    main(Path(__file__).with_name('block_binary_fold_ast.json'), 161, emit)
