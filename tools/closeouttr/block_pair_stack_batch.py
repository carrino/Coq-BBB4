#!/usr/bin/env python3
"""Emit/replay AST146: paired-word normalization and marked A0 returns."""
import itertools
from pathlib import Path
import cbt
from period3_batch import row, table
from balanced_carry_batch import main


def emit(records):
    pre, entries = [], []
    for i, r in enumerate(records):
        suffix = f'AST_146_{i:04d}'
        p, flip = r['p'], r['flip']
        assert sorted(p) == list(range(4))
        assert r['failed'] == [[p[0], 0]] and r['mirrored'] and r['t'] == 0
        src, dst = table(r['source']), table(r['spec'])
        for q, s in itertools.product(range(4), range(2)):
            w, d, t = src[2*q+s]
            if flip: d = 'L' if d == 'R' else 'R'
            assert dst[2*p[q]+s] == (w, d, p[t])
        assert r['mode'] in ('zero', 'oneleft')
        anchor = 'bca_anchor_right' if r['mode'] == 'zero' else 'bca_anchor_left'
        returns = f"bca_{r['mode']}_return"
        target = f'(St{chr(65+p[0])},S0)'
        perm = ' | '.join(f'St{chr(65+q)}=>St{chr(65+x)}' for q, x in enumerate(p))
        cells = '[' + ';'.join(f'S{x}' for x in r['tail']) + ']'
        pre.append(f'''Definition cert_{suffix}:Instr->list fmxcomp*list positive :=
{r['cert']}.
Definition source_{suffix} := row_to_tm {row(r['source'])}.
Definition perm_{suffix}(q:St):St := match q with {perm} end.
Definition family_{suffix}(x:{{T:list Sym | bca_tail T}}):cconf :=
  {anchor}(proj1_sig x).
Definition boot_{suffix}:{{T:list Sym | bca_tail T}}.
Proof. exists {cells};repeat constructor. Defined.
Definition skip_{suffix}(t:Instr):bool := instr_eqb t {target}.''')
        proof = f'''assert(Hprogress:forall x,exists y,Reach1 source_{suffix}(family_{suffix} x)(family_{suffix} y)).
  {{ intros[T HT]. destruct({returns} source_{suffix} eq_refl eq_refl eq_refl eq_refl
      eq_refl eq_refl eq_refl eq_refl T HT)as(U&HU&H).
    exists(exist bca_tail U HU);exact H. }}
  assert(Hrec:forall N,exists j,N<=j /\\ FiresAt(row_to_tm r_{suffix}){target}j).
  {{ apply(conjugate_marked_return_fire source_{suffix} _ perm_{suffix} {str(flip).lower()}
      _ family_{suffix} (StA,S0) {r['boot']} boot_{suffix}).
    - intros[] [];reflexivity.
    - rewrite <-lift_c0. apply csteps_lift. vm_compute;reflexivity.
    - exact Hprogress.
    - intros[T HT];apply fires_here;reflexivity. }}
  apply coversTr_nqh,neverqhtr_mirror.
  apply(ngram_check_neverqh_fuelmixtr_except_sound _ {r['n']} 0 {r['fuel']} {r['rounds']}
    skip_{suffix} cert_{suffix}).
  - intros[[] []] H N;try discriminate.
    destruct(Hrec N)as(j&Hj&Hf). exists j;split;[exact Hj|apply mirror_fires;exact Hf].
  - vm_compute;reflexivity.'''
        entries.append((r['spec'], proof))
    return cbt.write_batch('AST', 146,
      ['From BBB4 Require Import CTape Mirror.',
       'From BBB4.Checkers Require Import NGram FuelMixTr FuelMixPartialTr.',
       'From BBB4.Checkers.IRules Require Import AnchorVisitsTr.',
       'From BBB4.Counters Require Import CConjugateTr NestCountTr LoopRunTr MarkedReturnTr BlockCoreAReturnTr.',
       'From BBB4.CensusTr Require Import TNF_QHTr.'], entries,
      'paired-word normalization and marked A0 returns', preamble='\n\n'.join(pre))


if __name__ == '__main__':
    main(Path(__file__).with_name('block_pair_stack_ast.json'), 146, emit)
