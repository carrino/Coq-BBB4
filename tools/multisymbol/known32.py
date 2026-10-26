#!/usr/bin/env python3
"""Regenerate selected legacy bridges: INPUT.json OUTPUT.json, from repository root."""
from pathlib import Path
import json,re,sys
data=json.loads(Path(sys.argv[1]).read_text())
maps=[d for d in data if 'files'in d];checks=[d for d in data if 'block'in d]
byname={d['name']:d for d in checks}
header='''(** Selected binary recurrence certificates from the existing closeout. *)
From Coq Require Import Arith List ZArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta RulesK
 EngineK RulesBlk MetaBlk EngineKS RulesBlkPfx MetaBlkPfx MetaBlkPfxTr.
Import ListNotations.
'''
legacy=header;oldnames={}
for i,(name,d)in enumerate(sorted(byname.items())):
 ident=f'legacy32_{i:03d}';oldnames[name]=ident;raw=name.replace('_','');arms=[]
 for q in range(4):
  for a in range(2):
   tr=raw[6*q+3*a:6*q+3*a+3];rhs='None'if tr=='---'else f'Some(mkTrans S{tr[0]} D{tr[1]} St{tr[2]})';arms.append(f'|St{chr(65+q)},S{a}=>{rhs}')
 proof=d['block'].split('Proof.',1)[1].replace('apply coversTr_nqh,','apply').replace('vm_cast_no_check (eq_refl true).','native_compute. reflexivity.')
 legacy+=f'(* Reuses {d["file"]}: {name}. *)\nDefinition {ident}:TM:=fun q s=>match q,s with '+''.join(arms)+' end.\n'+f'Lemma {ident}_recur:NeverQuasiHaltsTr {ident}.\nProof.'+proof+'\n'
Path('small/legacy').mkdir(exist_ok=True);Path('small/legacy/Counter32.v').write_text(legacy)
allmaps={d['machine']:dict(d,oldtm=Path(d['files'][0]).stem+'.tm_'+Path(d['files'][0]).stem[5:],oldthm=Path(d['files'][0]).stem+'.nqhtr_'+Path(d['files'][0]).stem[5:])for d in maps}
for d in checks:
 ident=oldnames[d['name']];allmaps.setdefault(d['machine'],dict(d,oldtm='Counter32.'+ident,oldthm='Counter32.'+ident+'_recur'))
imports='\n'.join('Require BBB4.Machines.CountersTr.'+Path(f).stem+'.'for f in sorted({d['files'][0]for d in maps}))
out='''(** Bounds transported from existing binary counter proofs. *)
From Coq Require Import Arith Lia List.
From SmallBB Require Import Statement StatementTr CTape Mirror Size Bounds CycleCensus Legacy32.
Require SmallLegacy.Counter32.
'''+imports+'''
Import ListNotations.
'''
for i,(m,d)in enumerate(sorted(allmaps.items())):
 ident=f'known32_{i:03d}';d['index']=i;d['ident']=ident
 s=m.replace('_','');codes=[18 if s[j]=='-'else 6*int(s[j])+(3 if s[j+1]=='R'else 0)+ord(s[j+2])-65 for j in range(0,len(s),3)]
 out+=f'(* {m} *)\nDefinition {ident}:TM:=machine_of_codes 3 2 ['+';'.join(map(str,codes))+'].\n'
 out+=f'Lemma {ident}_bound:NonHalt {ident} /\\ Bounds 55 55 {ident}.\nProof.\n'
 if d['mirror']:
  out+=' assert(H:NonHalt(mirror_tm '+ident+') /\\ Bounds 55 55(mirror_tm '+ident+')).\n {\n'
 out+=' apply recurrence_bounds. eapply (legacy_neverqh '+('true'if d['perm'][1]==2 else 'false')+' _ '+d['oldtm']+').\n'
 out+=' - split.\n   + intros [] [] tr H; cbv ['+ident+' machine_of_codes nat_trans st_index sym_index nth mirror_tm mirror_dir] in H;\n     try discriminate; injection H as <-; unfold output_ok; simpl; lia.\n   + intros [] [] H; simpl in H; try(exfalso;lia); reflexivity.\n'
 out+=' - intros [] [] Hs; try(exfalso;apply Hs;reflexivity); reflexivity.\n - exact '+d['oldthm']+'.\n'
 if d['mirror']:out+=' } destruct H as[Hnh Hb];split;[apply mirror_nonhalt|apply mirror_bounds];assumption.\n'
 out+='Qed.\n'
out+='Definition known32:list TM:= ['+';'.join(d['ident']for d in allmaps.values())+'].\n'
# Same sorted order for indices and Forall list.
items=[d for m,d in sorted(allmaps.items())];out=out[:out.index('Definition known32:list')]+'Definition known32:list TM:= ['+';'.join(d['ident']for d in items)+'].\n'
out+='Lemma known32_sound:Forall(fun tm=>NonHalt tm /\\ Bounds 55 55 tm)known32.\nProof. unfold known32; repeat constructor; try assumption.\n'
# Avoid repeat constructor splitting conjunction goals: use explicit list induction constructors.
out=out[:out.index('Lemma known32_sound:')]+ 'Lemma known32_sound:Forall(fun tm=>NonHalt tm /\\ Bounds 55 55 tm)known32.\nProof. unfold known32.\n'+''.join(' constructor; [exact '+d['ident']+'_bound|].\n'for d in items)+' constructor. Qed.\n'
Path('small/theories/Known32.v').write_text(out);Path(sys.argv[2]).write_text(json.dumps(items,indent=2)+'\n')
