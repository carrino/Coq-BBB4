#!/usr/bin/env python3
"""Emit/replay AST141: two balanced rows by marked-carry return to A1."""
import itertools
from pathlib import Path
import cbt
from period3_batch import row,table
from balanced_carry_batch import main

def emit(records):
    pre,entries=[],[]
    for i,r in enumerate(records):
        suffix=f'AST_141_{i:04d}'
        p,flip=r['p'],r['flip']
        assert sorted(p)==list(range(4))
        assert r['failed']==[[p[0],1]] and r['mirrored'] and r['t']==0
        src,dst=table(r['source']),table(r['spec'])
        for q,s in itertools.product(range(4),range(2)):
            w,d,t=src[2*q+s]
            if flip:d='L'if d=='R'else'R'
            assert dst[2*p[q]+s]==(w,d,p[t])
        target=f'(St{chr(65+p[0])},S1)'
        perm=' | '.join(f'St{chr(65+q)}=>St{chr(65+x)}'for q,x in enumerate(p))
        cells=lambda xs:'['+';'.join(f'S{x}'for x in xs)+']'
        pre.append(f'''Definition cert_{suffix}:Instr->list fmxcomp*list positive :=
{r['cert']}.
Definition source_{suffix} := row_to_tm {row(r['source'])}.
Definition perm_{suffix}(q:St):St := match q with {perm} end.
Definition skip_{suffix}(t:Instr):bool := instr_eqb t {target}.''')
        proof=f'''assert(Hrec:forall N,exists j,N<=j /\\ FiresAt(row_to_tm r_{suffix}){target}j).
  {{ apply(conjugate_return_recurrent source_{suffix} _ perm_{suffix} {str(flip).lower()}
      StA S1 {r['boot']} {cells(r['left'])} {cells(r['right'])}).
    - intros[] [];reflexivity.
    - rewrite <-lift_c0. apply csteps_lift. vm_compute;reflexivity.
    - apply mc_return;reflexivity. }}
  apply coversTr_nqh,neverqhtr_mirror.
  apply(ngram_check_neverqh_fuelmixtr_except_sound _ {r['n']} 0 {r['fuel']} {r['rounds']}
    skip_{suffix} cert_{suffix}).
  - intros[[] []] H N;try discriminate.
    destruct(Hrec N)as(j&Hj&Hf). exists j;split;[exact Hj|apply mirror_fires;exact Hf].
  - vm_compute;reflexivity.'''
        entries.append((r['spec'],proof))
    return cbt.write_batch('AST',141,
      ['From BBB4 Require Import CTape Mirror.',
       'From BBB4.Checkers Require Import NGram FuelMixTr FuelMixPartialTr.',
       'From BBB4.Counters Require Import CConjugateTr FiniteReturnTr MarkedCarryReturnTr.',
       'From BBB4.CensusTr Require Import TNF_QHTr.'],entries,
      'marked-carry returns and checked instruction recurrence',preamble='\n\n'.join(pre))

if __name__=='__main__':main(Path(__file__).with_name('marked_carry_ast.json'),141,emit)
