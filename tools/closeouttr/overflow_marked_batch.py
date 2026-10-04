#!/usr/bin/env python3
"""Emit/replay AST144: the nested-overflow row by marked A1 returns."""
from pathlib import Path
import cbt
from period3_batch import row
from balanced_carry_batch import main

def emit(records):
    pre, entries = [], []
    for i, r in enumerate(records):
        suffix = f'AST_144_{i:04d}'
        assert r['failed'] == [[0, 1]] and not r['mirrored'] and r['t'] == 0
        cells = lambda xs: '['+';'.join(f'S{x}' for x in xs)+']'
        pre.append(f'''Definition cert_{suffix}:Instr->list fmxcomp*list positive :=
{r['cert']}.
Definition source_{suffix} := row_to_tm {row(r['spec'])}.
Definition family_{suffix}(x:Sym*(list Sym*list Sym)):cconf :=
  on_anchor(fst x)(fst(snd x))(snd(snd x)).
Definition skip_{suffix}(t:Instr):bool := instr_eqb t (StA,S1).''')
        proof = f'''assert(Hprogress:forall x,exists y,Reach1 source_{suffix}(family_{suffix} x)(family_{suffix} y)).
  {{ intros[b[L R]]. destruct(on_return source_{suffix} eq_refl eq_refl eq_refl eq_refl
      eq_refl eq_refl eq_refl eq_refl b L R)as(b'&U&V&H). exists(b',(U,V));exact H. }}
  assert(Hrec:forall N,exists j,N<=j /\\ FiresAt(row_to_tm r_{suffix})(StA,S1)j).
  {{ apply(conjugate_marked_return_fire source_{suffix} _ (fun q=>q) false
      _ family_{suffix} (StA,S1) {r['boot']} (S{r['marker']},({cells(r['left'])},{cells(r['right'])}))).
    - intros[] [];reflexivity.
    - rewrite <-lift_c0. apply csteps_lift. vm_compute;reflexivity.
    - exact Hprogress.
    - intros[b[L R]];apply fires_here;reflexivity. }}
  apply coversTr_nqh.
  apply(ngram_check_neverqh_fuelmixtr_except_sound _ {r['n']} 0 {r['fuel']} {r['rounds']}
    skip_{suffix} cert_{suffix}).
  - intros[[] []] H N;try discriminate;apply Hrec.
  - vm_compute;reflexivity.'''
        entries.append((r['spec'], proof))
    return cbt.write_batch('AST', 144,
      ['From BBB4 Require Import CTape.',
       'From BBB4.Checkers Require Import NGram FuelMixTr FuelMixPartialTr.',
       'From BBB4.Counters Require Import CConjugateTr NestCountTr LoopRunTr MarkedReturnTr OverflowNestedReturnTr.'], entries,
      'marked A1 returns and checked instruction recurrence', preamble='\n\n'.join(pre))

if __name__ == '__main__':
    main(Path(__file__).with_name('overflow_marked_ast.json'), 144, emit)
