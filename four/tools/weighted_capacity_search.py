"""Untrusted nonnegative tape-count capacity search for binary recurrence ranks.

The existing SCC/lexicographic producer is reused. LP proposals are converted
to exact integers and all capacity inequalities are rechecked before output.
The Coq checker remains authoritative, including the left-boundary invariant.
"""
import argparse,json,time,hashlib
from pathlib import Path
from collections import Counter
from fractions import Fraction
from math import lcm
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
import weighted_search_v2 as search

def capacity(graph,target):
 nodes=graph['nodes']; edges=[(i,j) for i,adj in enumerate(graph['edges']) for j in adj if 4*nodes[i][0]+nodes[i][2]!=target and 4*nodes[j][0]+nodes[j][2]!=target]
 if not edges:return {'K':1,'weights':[0]*12,'bias':[0]*len(nodes)}
 rows,_=search.inequalities(graph,edges,'linear');directions=[graph['trans'][4*nodes[i][0]+nodes[i][2]][1] for i,j in edges]
 rr=[];cc=[];vv=[]
 for index,row in enumerate(rows):
  for column,value in row.items():
   if value:rr.append(index);cc.append(column);vv.append(value)
 size=12+len(nodes);matrix=coo_matrix((vv,(rr,cc)),shape=(len(edges),size)).tocsr()
 bounds=[(0,0) if i in (0,4,8) else (0,None) for i in range(size)]
 result=linprog(np.array([1.]*12+[1./len(nodes)]*len(nodes)),A_ub=matrix,b_ub=np.array(directions),bounds=bounds,method='highs')
 if not result.success:return None
 for limit in [1000,100000,10000000]:
  fractions=[Fraction(float(x)).limit_denominator(limit) for x in result.x];K=lcm(*(x.denominator for x in fractions));values=[int(x*K) for x in fractions]
  if min(values,default=0)<0 or max([K,*values]).bit_length()>4096 or any(values[i] for i in (0,4,8)):continue
  if all(sum(values[k]*v for k,v in row.items())<=K*d for row,d in zip(rows,directions)):
   return {'K':K,'weights':values[:12],'bias':values[12:]}
 return None

def solve(graph,wall_width,counts):
 certs={};caps={}
 for target in range(8):
  if target in graph['ranked']:continue
  width=next((k for k in range(1,wall_width+1) if search.shared.wall(graph,target,k)),None)
  cap=None
  if width is None:
   counts['capacity_tests']+=1;cap=capacity(graph,target);counts['capacity_feasible' if cap else 'capacity_infeasible']+=1
  comps=search.solve(graph,target,width is not None or cap is not None,counts)
  if comps is None:counts['failed_target_'+str(target)]+=1;return None
  cert=search.shared.wallcert(graph,target,width) if width else {'k':0,'guards':[],'inside':[]}
  certs[str(target)]={**cert,'components':comps}
  if cap is not None and any(c['kind']=='w' for c in comps):caps[str(target)]=cap
 return {'graph':graph,'certs':certs,'capacities':caps}

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--graphs',type=Path,required=True)
 parser.add_argument('--output',type=Path,required=True)
 parser.add_argument('--report',type=Path,required=True)
 parser.add_argument('--timeout',type=float,default=3)
 parser.add_argument('--wall-width',type=int,default=16)
 parser.add_argument('--node-limit',type=int,default=2048)
 args=parser.parse_args()
 if not 0<args.timeout<float('inf') or args.wall_width<0 or args.node_limit<1:parser.error('Invalid budgets')
 counts=Counter();done=set();beg=time.monotonic();search.install_budget()
 source_hash=hashlib.sha256(args.graphs.read_bytes()).hexdigest()
 with args.graphs.open() as src,args.output.open('w') as dst:
  for line in src:
   event=json.loads(line);graph=event.get('graph')
   if graph is None or event['machine'] in done:continue
   if graph['machine']!=event['machine']:raise ValueError('Graph/event machine mismatch')
   counts['graphs']+=1
   if len(graph['nodes'])>args.node_limit:counts['node_limit']+=1;continue
   try:
    with search.budget(args.timeout):result=solve(graph,args.wall_width,counts)
    if result is not None:
     done.add(event['machine']);counts['candidate']+=1
     counts['with_capacity' if result['capacities'] else 'without_capacity']+=1
     dst.write(json.dumps(result,separators=(',',':'))+'\n');dst.flush()
   except search.BudgetExpired:counts['timeout']+=1
 if hashlib.sha256(args.graphs.read_bytes()).hexdigest()!=source_hash:raise ValueError('Graph input changed')
 report={'scope':'Untrusted capacity candidates; every certificate still requires Coq replay.',
         'source_sha256':source_hash,'counts':dict(counts),'seconds':round(time.monotonic()-beg,3),
         'parameters':{'timeout':args.timeout,'wall_width':args.wall_width,'node_limit':args.node_limit},
         'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
 args.report.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)

if __name__=='__main__':main()
