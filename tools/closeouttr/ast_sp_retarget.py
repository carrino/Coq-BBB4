#!/usr/bin/env python3
"""Retarget landed block-rule certificates to a new checked bootstrap.

Untrusted search only: state-renamed rules and the new start are checked
by MetaBlkPfxTr. Input mappings are [target, source, permutation, mirror,
source_batch], where the permutation maps target states to source states.

  ast_sp_retarget.py find MATCHES.json OUTPUT.json --steps 300000
  ast_sp_retarget.py batch OUTPUT.json --tag AST --batch 70
"""
from pathlib import Path
import json,re,sys
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
import bulk_prover as bp
from cbt import write_batch
def args(s):
 out=[];start=None;depth=0
 for i,c in enumerate(s):
  if not c.isspace() and start is None:start=i
  if c in '([':depth+=1
  if c in ')]':depth-=1
  if c.isspace() and depth==0 and start is not None:out.append(s[start:i]);start=None
 if start is not None:out.append(s[start:])
 return out

def extract(spec,batch):
 s=(ROOT/'theories/CloseoutTr'/f'{batch}.v').read_text().split(f'(* spec {spec} *)')[1].split('Qed.')[0]
 at=s.index('(mkBIRCertP');depth=0
 for j in range(at,len(s)):
  if s[j]=='(':depth+=1
  elif s[j]==')':
   depth-=1
   if depth==0:break
 return s[at+1:j],s

def intval(s):return int(re.sub(r'%nat|[()]','',s))
def trials(target,source,p,m,batch):
 expr,proof=extract(source,batch)
 a=args(expr)[1:]; assert len(a)==11,len(a)
 kmin=intval(a[2]); q=p.index(ord(a[5][-1])-65); h=int(a[6][-1]);blocks={0:[0],1:[1]}
 for id,word in re.findall(r'\((\d+)%nat,\s*\[([^]]*)\]\)',a[7]):blocks[int(id)]=[int(x) for x in re.findall(r'S([01])',word)]
 tpl=[]
 for side in a[8:10]:
  tpl.append([tuple(map(int,x)) for x in re.findall(r'\((\d+)%nat,\s*\((-?\d+)\),\s*\((-?\d+)\)\)',side)])
 def side(ts,k):return sum((blocks[i]*max(0,aa*k+b) for i,aa,b in ts),[])
 return dict(target=target,source=source,p=p,m=m,batch=batch,args=a,q=q,h=h,kmin=kmin,blocks=blocks,tpl=tpl)

def probe(candidates,N=300000):
 target=candidates[0]['target'];tbl=bp.parse(target);tape=set();pos=q=0
 for t in range(N):
  h=int(pos in tape)
  for c in candidates:
   if q!=c['q'] or h!=c['h']:continue
   left=[int(pos-j in tape) for j in range(1,pos-min(tape,default=pos)+1)]
   right=[int(pos+j in tape) for j in range(1,max(tape,default=pos)-pos+1)]
   if c['m']:left,right=right,left
   for ar in (left,right):
    while ar and ar[-1]==0:ar.pop()
   estimates=[]
   for ts,ar in zip(c['tpl'],[left,right]):
    coef=sum(len(c['blocks'][i])*aa for i,aa,b in ts);const=sum(len(c['blocks'][i])*b for i,aa,b in ts)
    if coef: estimates=[(len(ar)-const)//coef];break
   for estimate in estimates:
    for k in range(max(c['kmin'],estimate-3),estimate+5):
     ok=True
     for ts,ar in zip(c['tpl'],[left,right]):
      want=sum((c['blocks'][i]*max(0,aa*k+b) for i,aa,b in ts),[])
      while want and want[-1]==0:want.pop()
      if ar!=want:ok=False;break
     if ok:
      c.update(t=t,k=k);print('FOUND',target,c['source'],t,k,flush=True);return c
  w,d,q=tbl[q,h]
  if w:tape.add(pos)
  else:tape.discard(pos)
  pos+=1 if d=='R' else -1
 print('NOHIT',target,flush=True)

def emit(records, tag, nn, overwrite=False):
    entries = []
    for rec in records:
        data = list(rec['args'])
        data[0] = str(rec['t']) + '%nat'
        data[1] = '(%d)' % rec['k']
        expr = '(mkBIRCertP ' + ' '.join(data) + ')%Z'
        expr = re.sub(r'St([ABCD])', lambda m:
            'St' + chr(65 + rec['p'].index(ord(m[1]) - 65)), expr)
        proof = 'apply coversTr_nqh. '
        if rec['m']:
            proof += 'apply neverqhtr_mirror. '
        proof += ('apply (irulesblkpfx_check_neverqhtr_sound _ %s '
                  '200000 300000). vm_compute. reflexivity.' % expr)
        entries.append((rec['target'], proof))
    print(write_batch(tag, nn, [
        'From BBB4.CensusTr Require Import TNF_QHTr.',
        'From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta RulesK',
        '     EngineK RulesBlk MetaBlk EngineKS RulesBlkPfx MetaBlkPfx MetaBlkPfxTr.'
    ], entries, 'state-renamed block-rule certificates with independently checked boot configurations',
        overwrite=overwrite))


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='mode', required=True)
    find = sub.add_parser('find')
    find.add_argument('matches')
    find.add_argument('output')
    find.add_argument('--steps', type=int, default=300000)
    batch = sub.add_parser('batch')
    batch.add_argument('input')
    batch.add_argument('--tag', default='AST')
    batch.add_argument('--batch', type=int, required=True)
    batch.add_argument('--overwrite', action='store_true')
    ns = parser.parse_args()
    if ns.mode == 'batch':
        emit(json.loads(Path(ns.input).read_text()), ns.tag, ns.batch, ns.overwrite)
        return
    by = {}
    for row in json.loads(Path(ns.matches).read_text()):
        if row[-1].startswith('CBT_SP_'):
            c = trials(*row)
            by.setdefault(row[0], []).append(c)
    found = []
    for candidates in by.values():
        result = probe(candidates, ns.steps)
        if result:
            found.append(result)
        Path(ns.output).write_text(json.dumps(found, indent=2) + '\n')


if __name__ == '__main__':
    main()
