#!/usr/bin/env python3
"""Regenerate the conditional (2,3) registry from checked certificate metadata."""
from pathlib import Path
import json,re,sys
rows=json.loads(Path(sys.argv[1]).read_text())
base=[d['machine']for d in rows]
left=Path('small/certificates/remaining23.txt').read_text().splitlines()
items={d['machine']:dict(d,index=d.get('proof_index'))for d in rows}
def codes(m):
 s=m.replace('_','');return [12 if s[j]=='-'else 4*int(s[j])+(2 if s[j+1]=='R'else 0)+ord(s[j+2])-65 for j in range(0,len(s),3)]
cs=lambda m:'['+';'.join(map(str,codes(m)))+']'
header='''From Coq Require Import Arith Lia List.
From SmallBB Require Import Statement StatementTr Size Bounds Codes23 StateCheckers.
Import ListNotations.
'''
s=header+'Definition remaining23:list TM:= ['+';'.join('machine_of_codes 2 3 '+cs(m)for m in left)+'].\n'
s+='''Lemma remaining23_state_checked:forallb(fun tm=>ng_state_check 59 tm 2 128 4096 32)remaining23=true.
Proof. native_compute. reflexivity. Qed.
Lemma remaining23_nth:forall i tm,nth_error remaining23 i=Some tm->NonHalt tm /\\ QHBound 59 tm.
Proof.
 intros i tm H. pose proof(nth_error_In remaining23 i H)as Hin.
 pose proof remaining23_state_checked as HC;rewrite forallb_forall in HC.
 apply(ng_state_check_sound 59 tm 2 128 4096 32);exact(HC tm Hin).
Qed.
''';Path('small/theories/Remaining23.v').write_text(s)
header='''(** The instruction census reduces to the explicitly listed remaining machines. *)
From Coq Require Import Arith Lia List.
From SmallBB Require Import Statement StatementTr CTape Size Bounds Mirror CycleCensus
 Codes23 KnownCensus Census23State Weighted23 Weighted23Deep IR23 Remaining23.
'''
header+='\n'.join('Require SmallBB.Counters23.'+p.stem+'.'for p in sorted(Path('small/theories/Counters23').glob('*.v')))+'\nImport ListNotations.\n'
s=header+'''Lemma known23_recurrence:forall tm,NeverQuasiHaltsTr tm->NonHalt tm /\\ QHBoundTr 67 tm.
Proof.
 intros tm H;split;[apply never_qh_tr_nonhalt;exact H|].
 intros tg s[Hv Hquiet];destruct(H tg ltac:(exists s;exact Hv)(S s))as(k&Hk&Hf).
 exfalso;apply(Hquiet k);[lia|exact Hf].
Qed.
Lemma known23_unmirror:forall tm,NonHalt(mirror_tm tm) /\\ QHBoundTr 67(mirror_tm tm)->NonHalt tm /\\ QHBoundTr 67 tm.
Proof.
 intros tm[HN HB];split;[apply mirror_nonhalt;exact HN|].
 intros tg s[Hv Hquiet];apply(HB tg s);split;[apply mirror_fires;exact Hv|].
 intros k Hk Hf;apply(Hquiet k Hk);apply mirror_fires;exact Hf.
Qed.
'''
for i,m in enumerate(base):
 name=f'known23_{i:03d}';d=items[m];kind=d['kind'];j=d['index']if'index'in d else None
 s+=f'(* {m} *)\nDefinition {name}:TM:=machine_of_codes 2 3 '+cs(m)+'.\n'
 s+=f'Lemma {name}_bound(residue:Forall(QHBoundTr 67)remaining23):NonHalt {name} /\\ Bounds 59 67 {name}.\nProof.\n'
 s+=f' assert(H:NonHalt {name} /\\ QHBoundTr 67 {name}).\n {{\n'
 if d.get('mirror'):s+=' apply known23_unmirror.\n'
 cur=f'(mirror_tm {name})'if d.get('mirror')else name
 if kind in ['weighted','deep']:
  prefix=f'w23_{j:03d}'if kind=='weighted'else f'wd23_{j:03d}';tm=f'(mirror_tm {prefix}_tm)'if d['mirror']else prefix+'_tm'
  s+=f' change(NonHalt {tm} /\\ QHBoundTr 67 {tm}).\n'
  args=f'{j} {tm} '+(f'{d["n"]} {d["t"]} 'if kind=='deep'else'')+prefix+'_cert eq_refl'
  th='weighted23_nth'if kind=='weighted'else'weighted23_deep_nth'
  s+=f' destruct({th} {args})as[HN[_ HB]];split;assumption.\n'
 elif kind=='ir':
  s+=f' pose proof(ir23_nth {j} _ _ eq_refl)as[HN[_ HB]];split;[exact HN|exact HB].\n'
 elif kind in ['qh','nqh']:
  tm=d['module']+'.tm_'+d['ident'];s+=f' assert(E:{cur}={tm})by(apply same_table_sound;reflexivity). rewrite E.\n'
  if kind=='nqh':s+=' apply known23_recurrence. exact '+d['module']+'.nqhtr_'+d['ident']+'.\n'
  else:s+=' exact '+d['module']+'.qhtr_'+d['ident']+'.\n'
 else:
  s+=f' split;[exact(proj1(remaining23_nth {j} {name} eq_refl))|].\n rewrite Forall_forall in residue;apply residue. exact(nth_error_In remaining23 {j} (eq_refl(Some {name}))).\n'
 s+=f' }} destruct H as[HN HB];split;[exact HN|];split;[apply bbb23_state_upper,codes23_admissible|exact HB].\nQed.\n'
s+='Definition known23:list TM:= ['+';'.join(f'known23_{i:03d}'for i in range(len(base)))+'].\n'
s+='Lemma known23_sound:Forall(QHBoundTr 67)remaining23->Forall(fun tm=>NonHalt tm /\\ Bounds 59 67 tm)known23.\nProof. intro H;unfold known23.\n'+''.join(f' constructor;[exact(known23_{i:03d}_bound H)|].\n'for i in range(len(base)))+' constructor. Qed.\n'
Path('small/theories/Known23.v').write_text(s)
