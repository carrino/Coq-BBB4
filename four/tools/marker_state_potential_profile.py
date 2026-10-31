"""Measure a proposed weighted-left-capacity marker rule (untrusted).

For B-self steps, weight(write)-weight(read) <= direction (+1 R,-1 L),
with blank weight0 and all weights nonnegative. This preserves a padded
left-capacity margin; the rightmost marker prevents right-boundary escape.
A separate generic proof is still required.
"""
import argparse
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path
from marker_state_profile_v2 import ROOT,REPO,sha,ore_goal,marker_check
from generate_pipeline_examples import codes

WEIGHTS=[(0,)+x for x in itertools.product(range(4),repeat=3)]
def invariant_conditions(table,mask):
 if 16 in table:return False
 marked=lambda s:bool(mask>>s&1)
 if not all(table[4+s]%2==0 for s in range(1,4) if marked(s)):return False
 for cell,v in enumerate(table):
  if cell==0 or marked(cell%4):
   if not ((v//2%2==1 and v%2==0) or (v//2%2==0 and marked(v//4))):return False
 return table[4]%4==3 and any(ore_goal(table,1,mirror) for mirror in (0,1))
def capacity_weights(table):
 for weights in WEIGHTS:
  if all(v%2==0 or weights[v//4]-weights[s] <= (1 if v//2%2 else -1) for s,v in enumerate(table[4:])):
   return list(weights)
 return None

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--input',type=Path,default=ROOT/'build/state-pipeline/history-full/not-accepted.txt')
 p.add_argument('--output',type=Path,default=ROOT/'research/state-marker-potential-profile.json');a=p.parse_args()
 machines=a.input.read_text().splitlines()
 if len(machines)!=len(set(machines)):raise ValueError('Repeated family')
 rows=[];hist=Counter();new=0
 for machine in machines:
  table=codes(machine)
  masks=[m for m in range(2,16,2) if invariant_conditions(table,m)]
  if not masks:continue
  weights=capacity_weights(table)
  if weights is None:continue
  mask=min(masks,key=lambda m:(m.bit_count(),m));old=any(marker_check(table,m) for m in masks)
  rows.append(dict(machine=machine,marker_mask=mask,weights=weights,covered_by_v2=old));hist[str(mask)]+=1;new+=not old
 report=dict(status='untrusted_weighted_marker_measurement',input_families=len(machines),candidates=len(rows),new_beyond_v2=new,
  mask_histogram=dict(hist),rows=rows,input_sha256=sha(a.input),
  source_sha256={str(x.resolve().relative_to(REPO)):sha(x) for x in [Path(__file__),ROOT/'tools/marker_state_profile_v2.py',ROOT/'tools/generate_pipeline_examples.py']},
  kernel_checked=0,census_linked=0,scope='STATE ONLY proposed invariant and finite-tape padding argument; proof still required.')
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='rows'}))
if __name__=='__main__':main()
