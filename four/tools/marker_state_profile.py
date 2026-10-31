"""Measure a proposed rightmost-marker recurrence class; no proof claims.

The classifier is a search proposal pending a generic Coq theorem. It only
considers total tables and retains the exact frozen state-residual inventory.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
from generate_pipeline_examples import codes

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ore_goal(table,goal,mirror):
 other=1-goal
 def rank(s,fuel=4):
  v=table[4*other+s]
  if not fuel or v==16 or v%2==goal or ((v//2%2)^mirror)==0:return 0
  return 1+rank(v//4,fuel-1)
 for s in range(4):
  v=table[4*other+s]
  if v==16:return False
  if v%2==goal:continue
  if s==0 or (((v//2%2)^mirror)==1 and rank(v//4)>=rank(s)):return False
 return True

def marker_check(table,mask):
 if 16 in table:return False
 marked=lambda s:bool(mask>>s&1)
 if not all(table[4+s]%2==0 for s in range(1,4) if marked(s)):return False
 for cell,v in enumerate(table):
  if cell==0 or marked(cell%4):
   if not ((v//2%2==1 and v%2==0) or (v//2%2==0 and marked(v//4))):return False
 if table[4]%4!=3:return False  # Blank in B moves right, remaining in B.
 def rank(s,fuel=4):
  v=table[4+s]
  if not fuel or v%2==0 or v//2%2==0:return 0
  return 1+rank(v//4,fuel-1)
 for s in range(4):
  v=table[4+s]
  if v%2==0:continue
  if v//2%2==1:
   if rank(v//4)>=rank(s):return False
  elif table[4+v//4]%2!=0:return False
 return any(ore_goal(table,1,mirror) for mirror in (0,1))

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--input',type=Path,default=ROOT/'build/state-pipeline/history-full/not-accepted.txt')
 p.add_argument('--output',type=Path,default=ROOT/'research/state-marker-profile.json');a=p.parse_args()
 machines=a.input.read_text().splitlines()
 if len(set(machines))!=len(machines):raise ValueError('Repeated family')
 rows=[];partial=0;hist=Counter()
 for machine in machines:
  table=codes(machine)
  if 16 in table:partial+=1;continue
  masks=[mask for mask in range(2,16,2) if marker_check(table,mask)]
  if masks:
   mask=min(masks,key=lambda m:(m.bit_count(),m));rows.append(dict(machine=machine,marker_mask=mask));hist[str(mask)]+=1
 report=dict(status='untrusted_marker_class_measurement',input_families=len(machines),partial_excluded=partial,
  total_candidates=len(rows),marker_mask_histogram=dict(hist),rows=rows,input_sha256=sha(a.input),
  source_sha256={str(x.resolve().relative_to(REPO)):sha(x) for x in [Path(__file__),ROOT/'tools/generate_pipeline_examples.py']},
  kernel_checked=0,census_linked=0,scope='STATE ONLY proposed marker invariant; generic proof still required.')
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='rows'}))
if __name__=='__main__':main()
