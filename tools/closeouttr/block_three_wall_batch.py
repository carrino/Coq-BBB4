#!/usr/bin/env python3
"""Emit/replay AST157: three finite walls and binary-descent marked returns."""
import itertools
from pathlib import Path
import cbt
from period3_batch import row, table
from balanced_carry_batch import main


def emit(records):
    preamble, entries = [], []
    for i, record in enumerate(records):
        name = f'AST_157_{i:04d}'
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
        # Replay the finite-list boot, retaining its explicit blank padding.
        q, h, left, right = 0, 0, [], []
        for _ in range(record['boot']):
            write, direction, q = target[2*q+h]
            if direction == 'R':
                left, h, right = [write]+left, right[0] if right else 0, right[1:]
            else:
                right, h, left = [write]+right, left[0] if left else 0, left[1:]
        norm_left, norm_right = list(left), list(right)
        while norm_left and norm_left[-1] == 0: norm_left.pop()
        while norm_right and norm_right[-1] == 0: norm_right.pop()
        syms = lambda xs: '['+';'.join('S'+str(x) for x in xs)+']'
        actual = f'(St{chr(65+q)},({syms(left)},S{h},{syms(right)}))'
        normal = f'(St{chr(65+q)},({syms(norm_left)},S{h},{syms(norm_right)}))'
        if left != norm_left:
            assert right == norm_right
            padded = f'(St{chr(65+q)},({syms(norm_left)}++rep[S0]{len(left)-len(norm_left)},S{h},{syms(right)}))'
            padlemma = 'lift_padL'
        else:
            assert left == norm_left
            padded = f'(St{chr(65+q)},({syms(left)},S{h},{syms(norm_right)}++rep[S0]{len(right)-len(norm_right)}))'
            padlemma = 'lift_padR'
        boot_proof = f"""rewrite <-lift_c0. transitivity(Some(lift{actual})).
      + apply csteps_lift;vm_compute;reflexivity.
      + f_equal. change(lift{padded}=lift{normal});apply {padlemma}."""
        preamble.append(f'''Definition cert_{name}:Instr->list fmxcomp*list positive :=
{record['cert']}.
Definition source_{name} := row_to_tm {row(record['source'])}.
Definition perm_{name}(q:St):St := match q with {arms} end.
Definition family_{name}(x:{{c:cconf | ber_mark c}}):cconf := proj1_sig x.
Definition boot_{name}:{{c:cconf | ber_mark c}}.
Proof.
 exists (bce_start {record['n0']} [{';'.join('S'+str(x)for x in record['U'])}]);apply ber_start.
Defined.
Definition skip_{name}(t:Instr):bool := instr_eqb t {instruction}.''')
        proof = f'''assert(Hprogress:forall x,exists y,
    Reach1 source_{name}(family_{name} x)(family_{name} y)).
  {{ intros[c Hc]. destruct(ber_return source_{name} eq_refl eq_refl eq_refl eq_refl
      eq_refl eq_refl eq_refl eq_refl c Hc)as(d&Hd&Hrun).
    exists(exist ber_mark d Hd);exact Hrun. }}
  assert(Hrec:forall N,exists j,N<=j /\\ FiresAt(row_to_tm r_{name}){instruction}j).
  {{ apply(conjugate_marked_return_fire source_{name} _ perm_{name} {str(flip).lower()}
      _ family_{name} (StA,S0) {record['boot']} boot_{name}).
    - intros[] [];reflexivity.
    - {boot_proof}
    - exact Hprogress.
    - intros[c Hc];apply fires_here;apply ber_mark_instr;exact Hc. }}
  apply coversTr_nqh,neverqhtr_mirror.
  apply(ngram_check_neverqh_fuelmixtr_except_sound _ {record['n']} 0 {record['fuel']} {record['rounds']}
    skip_{name} cert_{name}).
  - intros[[] []] H N;try discriminate.
    destruct(Hrec N)as(j&Hj&Hf). exists j;split;[exact Hj|apply mirror_fires;exact Hf].
  - vm_compute;reflexivity.'''
        entries.append((record['spec'], proof))
    return cbt.write_batch('AST', 157,
        ['From BBB4 Require Import CTape Mirror.',
         'From BBB4.Checkers Require Import NGram FuelMixTr FuelMixPartialTr.',
         'From BBB4.Checkers.IRules Require Import AnchorVisitsTr.',
         'From BBB4.Counters Require Import CConjugateTr WTape NestCountTr LoopRunTr MarkedReturnTr BlockCoreEStartTr BlockCoreEReturnTr.',
         'From BBB4.CensusTr Require Import TNF_QHTr.'], entries,
        'three finite right walls and binary-descent marked A0 returns',
        preamble='\n\n'.join(preamble))


if __name__ == '__main__':
    main(Path(__file__).with_name('block_three_wall_ast.json'), 157, emit)
