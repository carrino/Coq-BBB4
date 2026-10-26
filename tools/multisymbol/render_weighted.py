import json,sys
from pathlib import Path
rows=list(map(json.loads,open(sys.argv[1])))
coqlist=lambda xs:'['+';'.join(map(str,xs))+']'
cl=lambda xs:coqlist('S'+str(x)for x in xs)
node=lambda c:'(St'+chr(65+c[0])+',('+cl(c[1])+',S'+str(c[2])+','+cl(c[3])+'))'
nats=lambda xs:coqlist(str(x)+'%nat'for x in xs)
zs=lambda xs:coqlist('('+str(x)+')%Z'for x in xs)
out='''From Coq Require Import List ZArith.
From SmallBB Require Import Statement StatementTr CTape Size Bounds Mirror CycleCensus WeightedNGram WeightedCensus.
From SmallBB.Checkers Require Import NGram.
Import ListNotations.
'''
entries=[]
for i,row in enumerate(rows):
 g=row['graph'];pre=f'w23_{i:03d}';out+=f'Definition {pre}_nodes:list cconf:='+coqlist(node(c)for c in g['nodes'])+'.\n'
 cert=[]
 for t,c in row['certs'].items():
  comps=[]
  for comp in c['components']:
   kind=comp['kind']
   if kind=='rank':comps.append('WRank(wc_table 0%nat '+pre+'_nodes '+nats(comp['rank'])+')');continue
   xs=comp['values'];gate='(wc_gate '+pre+'_nodes '+nats(comp['active'])+')'
   if kind=='linear':
    cs=[]
    for part,ctor in enumerate(['MAll','MLeft','MRight']):
     for s in [1,2]:
      if xs[3*part+s]:cs.append('('+str(xs[3*part+s])+'%nat,'+ctor+' C'+str(s)+')')
    comps.append('WLinear '+coqlist(cs)+' (wc_table 0%nat '+pre+'_nodes '+nats(xs[9:])+') '+gate)
   else:
    scores=['(wc_score '+' '.join('('+str(x)+')%Z'for x in xs[j:j+3])+')'for j in [0,3,6,9]]
    comps.append('WBinary '+' '.join(scores)+' (wc_table 0%Z '+pre+'_nodes '+zs(xs[12:])+') '+gate)
  name=pre+'_t'+str(t);out+=f'Definition {name}:WCert:=mkWC {c["k"]}%nat '+coqlist(cl(w)for w in c['guards'])+' '+coqlist(node(x)for x in c['inside'])+' '+coqlist(comps)+'.\n'
  t=int(t);cert.append('|(St'+chr(65+t//3)+',S'+str(t%3)+')=>Some '+name)
 out+=f'Definition {pre}_cert(t:Instr):option WCert:=match t with '+''.join(cert)+'|_=>None end.\n'
 s=g['machine'].replace('_','');codes=[12 if s[j]=='-'else 4*int(s[j])+(2 if s[j+1]=='R'else 0)+ord(s[j+2])-65 for j in range(0,len(s),3)]
 out+=f'Definition {pre}_tm:TM:=machine_of_codes 2 3 '+nats(codes)+'.\n'
 actual=f'(mirror_tm {pre}_tm)'if g['mirror']else pre+'_tm'
 entries.append(f'({actual},{g["n"]}%nat,{g["t"]}%nat,{pre}_cert)')
out+='Definition weighted23_entries:list(TM*nat*nat*(Instr->option WCert)):='+coqlist(entries)+'.\n'
out+="Lemma weighted23_checked: forallb(fun p=>let '(tm,n,t,c):=p in wc_check 59 67 tm n t 4096 32 c)weighted23_entries=true.\nProof. native_compute. reflexivity. Qed.\n"
Path(sys.argv[2]).write_text(out)
