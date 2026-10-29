"""Bounded partial-table marker/history discovery; no proof credit.

Every total state residual already passes the uniform B criterion. This pilot
therefore tests sixteen partial-table families with capacity inequalities,
using closed history graphs as candidate evidence for reachable nonhalting.
"""
import argparse
from collections import Counter
import hashlib,json
from pathlib import Path
import subprocess,time

from generate_pipeline_examples import codes
from marker_state_profile_v2 import ore_goal
from search_burn4_entry_marker import capacity,WEIGHTS

ROOT=Path(__file__).resolve().parents[1]
BUILD=ROOT/'build/burn10-marker-history'
INPUT=ROOT/'research/burn10-marker-history-input.json'
REPORT=ROOT/'research/burn10-marker-history-search.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def exact(p,d):
 text=json.dumps(d,indent=2,sort_keys=True)+'\n'
 if p.exists():assert p.read_text()==text
 else:p.write_text(text)
def initial(machine,mask):
 table=codes(machine);tape={};head=0;q=0
 for _ in range(4096):
  cell=table[q*4+tape.get(head,0)]
  if cell==16:return False
  tape[head]=cell//4;head+=1 if cell//2%2 else -1;q=cell%2
 return q==0 or any(p>=head and (mask>>s)&1 for p,s in tape.items())
def markers(graph):
 result=[]
 for mask in range(2,16,2):
  mark=lambda s:bool((mask>>s)&1)
  visible=lambda a:any(mark(s)for s in [a[2],*a[3]])
  if initial(graph['machine'],mask)and all(graph['nodes'][j][0]==0 or visible(graph['nodes'][j])or(graph['nodes'][i][0]==1 and not mark(graph['nodes'][i][2]))for i,es in enumerate(graph['edges'])for j in es):result.append(mask)
 return result

def plain_rank(graph,goal):
 left={i for i,a in enumerate(graph['nodes'])if a[0]!=goal};ranks={i:0 for i,a in enumerate(graph['nodes'])if a[0]==goal}
 while left:
  add={i:1+max((ranks[j]for j in graph['edges'][i]),default=0)for i in left if all(j in ranks for j in graph['edges'][i])}
  if not add:return False
  ranks.update(add);left.difference_update(add)
 return True

def select():
 strata=Counter();rows=[]
 for machine in(ROOT/'build/burn8-burndown/state-remaining.txt').read_text().splitlines():
  t=codes(machine);total=16 not in t;other=any(ore_goal(t,1,m)for m in(0,1));w=next((x for x in WEIGHTS if capacity(t,x)),None)
  strata[(total,other,w is not None)]+=1
  if not total and not other and w is not None:rows.append(dict(machine=machine,weights=list(w)))
 assert len(rows)==55
 rows.sort(key=lambda r:sha_bytes('burn10-marker-history:'+r['machine']))
 return [[list(k),v]for k,v in sorted(strata.items())],rows[:16]
def sha_bytes(s):return hashlib.sha256(s.encode()).hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');args=p.parse_args()
 strata,rows=select();binary=ROOT/'build/burn9-state-capacity/export'
 source=[Path(__file__),ROOT/'tools/generate_pipeline_examples.py',ROOT/'tools/marker_state_profile_v2.py',ROOT/'tools/search_burn4_entry_marker.py',ROOT/'tools/burn9_state_capacity_export.ml',binary,ROOT/'research/burn8-burndown-summary.json',ROOT/'build/burn8-burndown/state-remaining.txt']
 pins={str(x.relative_to(ROOT)):sha(x)for x in source}
 manifest=dict(scope='Native candidate discovery only; zero proof credit.',selection='Sixteen smallest SHA256(burn10-marker-history:machine) from55 partial capacity-eligible state families',rows=rows,full_residual_strata=strata,seconds_per_graph=8,workers=1,source_sha256=pins)
 if args.check:
  assert json.loads(INPUT.read_text())==manifest
  r=json.loads(REPORT.read_text());assert r['input_sha256']==sha(INPUT)and r['ledger_sha256']==sha(BUILD/'results.jsonl')
  assert[r['machine']for r in r['results']]==[x['machine']for x in rows]
  for x in r['results']:
   if 'graph_path'in x:
    assert sha(ROOT/x['graph_path'])==x['graph_sha256'];g=json.loads((ROOT/x['graph_path']).read_text());assert x['marker_masks']==markers(g)and x['B_plain_rank']==plain_rank(g,1)
  print('Exact input, graph conditions and ledger passed.');return
 if REPORT.exists():raise ValueError('Completed report exists; use --check')
 BUILD.mkdir(parents=True,exist_ok=True);exact(INPUT,manifest);results=[]
 with(BUILD/'results.jsonl').open('w')as ledger:
  for i,row in enumerate(rows):
   inp=BUILD/f'input-{i:02d}.txt';inp.write_text(row['machine']+'\n');out=BUILD/f'graph-{i:02d}.json';err=BUILD/f'worker-{i:02d}.log';start=time.monotonic()
   with out.open('w')as stdout,err.open('w')as stderr:
    try:run=subprocess.run([str(binary),str(inp)],stdout=stdout,stderr=stderr,timeout=8);status='closed'if run.returncode==0 else 'graph_rejected'
    except subprocess.TimeoutExpired:status='timeout'
   record=dict(index=i,machine=row['machine'],status=status,seconds=round(time.monotonic()-start,6))
   if status=='closed':
    graph=json.loads(out.read_text());assert graph['machine']==row['machine'];masks=markers(graph);b=plain_rank(graph,1)
    record.update(marker_masks=masks,B_plain_rank=b,nodes=len(graph['nodes']),graph_path=str(out.relative_to(ROOT)),graph_sha256=sha(out))
    if masks:record['status']='marker_candidate'
   results.append(record);ledger.write(json.dumps(record,separators=(',',':'))+'\n');ledger.flush();print(json.dumps(record),flush=True)
 assert pins=={str(x.relative_to(ROOT)):sha(x)for x in source}
 exact(REPORT,dict(scope='Native candidates only; no kernel proof credit.',input_sha256=sha(INPUT),ledger_sha256=sha(BUILD/'results.jsonl'),results=results,statuses=dict(Counter(x['status']for x in results)),seconds=sum(x['seconds']for x in results),checked_state_families=0))
if __name__=='__main__':main()
