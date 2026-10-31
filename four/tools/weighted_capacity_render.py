"""Render supplied capacity invariants and independent rejection regressions.

All arithmetic and recurrence obligations are checked in Coq.
"""
from weighted_render_v4 import HEADER as BASE_HEADER, render as previous
from weighted_render import coqlist,naturals

HEADER = BASE_HEADER + 'From BBB24 Require Import WeightedCapacity.\n'


def render(row):
 text=previous(row)
 capacities=''
 branches=[]
 for target,C in sorted(row['capacities'].items(),key=lambda x:int(x[0])):
  if not 0<=int(target)<8 or type(C['K']) is not int or C['K']<1:raise ValueError('Bad capacity target/scale')
  if len(C['bias'])!=len(row['graph']['nodes']):raise ValueError('Capacity bias length differs')
  weights=C['weights']
  if len(weights)!=12 or any(type(v) is not int or v<0 for v in weights) or any(weights[i] for i in (0,4,8)):raise ValueError('Bad capacity weights')
  terms=[]
  for part,ctor in enumerate(('MAll','MLeft','MRight')):
   for sym in (1,2,3):
    w=weights[4*part+sym]
    if w:terms.append(f'({w}%nat,{ctor} C{sym})')
  name='capacity_'+str(target)
  capacities+=f'Definition {name}:WCapacity:=mkWCapacity {C["K"]}%nat {coqlist(terms)} (wc_table 0%nat nodes {naturals(C["bias"])}).\n'
  branches.append(f'|(St{chr(65+int(target)//4)},S{int(target)%4})=>Some {name}')
 capacities+='Definition capacity(t:Instr):option WCapacity:=match t with '+''.join(branches)+('' if len(branches)==8 else '|_=>None')+' end.\n'
 text=text.replace('Lemma checked:',capacities+'Lemma checked:',1).replace('wc_graph_check ','wca_graph_check ').replace('nodes certificate=true','nodes certificate capacity=true').replace('wc_graph_check_sound _ _ _ _ _ _ _ checked','wca_graph_check_sound _ _ _ _ _ _ _ _ checked')
 text=text.replace(BASE_HEADER,HEADER,1)
 g=row['graph'];actual='(mirror_tm family)' if g['mirror'] else 'family'
 text+=f'Example old_certificate_rejected:wc_graph_check 4096%N 4096%N {actual} {g["n"]}%nat {g["t"]}%nat nodes certificate=false.\nProof. vm_compute. reflexivity. Qed.\n'
 text+='Definition zero_capacity(t:Instr):option WCapacity:=match capacity t with None=>None|Some C=>Some(mkWCapacity 0 (wca_terms C)(wca_bias C))end.\n'
 text+=f'Example zero_scale_rejected:wca_graph_check 4096%N 4096%N {actual} {g["n"]}%nat {g["t"]}%nat nodes certificate zero_capacity=false.\nProof. vm_compute. reflexivity. Qed.\n'
 text+='Definition empty_capacity(t:Instr):option WCapacity:=match capacity t with None=>None|Some C=>Some(mkWCapacity(wca_scale C)[](wca_bias C))end.\n'
 text+=f'Example wrong_weights_rejected:wca_graph_check 4096%N 4096%N {actual} {g["n"]}%nat {g["t"]}%nat nodes certificate empty_capacity=false.\nProof. vm_compute. reflexivity. Qed.\n'
 return text

