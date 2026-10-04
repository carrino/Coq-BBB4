#!/usr/bin/env python3
"""Emit/replay AST143: three-cell mirror pair by marked C1 returns."""
import itertools
from pathlib import Path
import cbt
from period3_batch import row, table
from balanced_carry_batch import main

def emit(records):
    pre, entries = [], []
    for i, r in enumerate(records):
        suffix = f'AST_143_{i:04d}'
        p, flip = r['p'], r['flip']
        assert sorted(p) == list(range(4))
        assert r['failed'] == [[p[2], 1], [p[3], 1]] and r['mirrored'] and r['t'] == 0
        src, dst = table(r['source']), table(r['spec'])
        for q, s in itertools.product(range(4), range(2)):
            w, d, t = src[2*q+s]
            if flip: d = 'L' if d == 'R' else 'R'
            assert dst[2*p[q]+s] == (w, d, p[t])
        target = f'(St{chr(65+p[2])},S1)'
        cross = f'(St{chr(65+p[3])},S1)'
        perm = ' | '.join(f'St{chr(65+q)}=>St{chr(65+x)}' for q, x in enumerate(p))
        cells = lambda xs: '['+';'.join(f'S{x}' for x in xs)+']'
        pre.append(f'''Definition cert_{suffix}:Instr->list fmxcomp*list positive :=
{r['cert']}.
Definition source_{suffix} := row_to_tm {row(r['source'])}.
Definition perm_{suffix}(q:St):St := match q with {perm} end.
Definition family_{suffix}(x:list Sym*list Sym):cconf := mn_anchor(fst x)(snd x).
Definition skip_{suffix}(t:Instr):bool := instr_eqb t {target} || instr_eqb t {cross}.''')
        proof = f'''assert(Hprogress:forall x,exists y,Reach1 source_{suffix}(family_{suffix} x)(family_{suffix} y)).
  {{ intros[L R]. destruct(mn_return source_{suffix} eq_refl eq_refl eq_refl eq_refl
      eq_refl eq_refl eq_refl eq_refl L R)as(U&V&H). exists(U,V);exact H. }}
  assert(Hrec:forall N,exists j,N<=j /\\ FiresAt(row_to_tm r_{suffix}){target}j).
  {{ apply(conjugate_marked_return_fire source_{suffix} _ perm_{suffix} {str(flip).lower()}
      _ family_{suffix} (StC,S1) {r['boot']} ({cells(r['left'])},{cells(r['right'])})).
    - intros[] [];reflexivity.
    - rewrite <-lift_c0. apply csteps_lift. vm_compute;reflexivity.
    - exact Hprogress.
    - intros[L R];apply fires_here;reflexivity. }}
  assert(Hcross:forall N,exists j,N<=j /\\ FiresAt(row_to_tm r_{suffix}){cross}j).
  {{ apply(conjugate_marked_return_fire source_{suffix} _ perm_{suffix} {str(flip).lower()}
      _ family_{suffix} (StD,S1) {r['boot']} ({cells(r['left'])},{cells(r['right'])})).
    - intros[] [];reflexivity.
    - rewrite <-lift_c0. apply csteps_lift. vm_compute;reflexivity.
    - exact Hprogress.
    - intros[L R];apply mn_D1;reflexivity. }}
  apply coversTr_nqh,neverqhtr_mirror.
  apply(ngram_check_neverqh_fuelmixtr_except_sound _ {r['n']} 0 {r['fuel']} {r['rounds']}
    skip_{suffix} cert_{suffix}).
  - intros[[] []] H N;try discriminate.
    all:first[destruct(Hrec N)as(j&Hj&Hf);exists j;split;[exact Hj|apply mirror_fires;exact Hf]
             |destruct(Hcross N)as(j&Hj&Hf);exists j;split;[exact Hj|apply mirror_fires;exact Hf]].
  - vm_compute;reflexivity.'''
        entries.append((r['spec'], proof))
    return cbt.write_batch('AST', 143,
      ['From BBB4 Require Import CTape Mirror.',
       'From BBB4.Checkers Require Import NGram FuelMixTr FuelMixPartialTr.',
       'From BBB4.Counters Require Import CConjugateTr NestCountTr LoopRunTr MarkedReturnTr MirrorNestedReturnTr.',
       'From BBB4.CensusTr Require Import TNF_QHTr.'], entries,
      'marked C1 returns and checked instruction recurrence', preamble='\n\n'.join(pre))

if __name__ == '__main__':
    main(Path(__file__).with_name('mirror_marked_ast.json'), 143, emit)
