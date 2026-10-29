"""Measure an untrusted marker/exit-trail recurrence proposal.

Every B-self right move writes a symbol whose B transition exits to A.
An initial left sweep hits a blank; after any right move a reversal left
returns onto such an exit symbol. The rightmost marker bounds a pure right
sweep. A generic proof is still required.
"""
import argparse
import json
from pathlib import Path
from marker_state_potential_profile import ROOT,REPO,sha,invariant_conditions,capacity_weights
from marker_state_profile_v2 import marker_check
from generate_pipeline_examples import codes

def trail_check(table,mask):
 return invariant_conditions(table,mask) and all(v%2==0 or v//2%2==0 or table[4+v//4]%2==0 for v in table[4:])
def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--input',type=Path,default=ROOT/'build/state-pipeline/history-full/not-accepted.txt')
 p.add_argument('--output',type=Path,default=ROOT/'research/state-marker-trail-profile.json');a=p.parse_args()
 machines=a.input.read_text().splitlines();rows=[];new=0
 if len(set(machines))!=len(machines):raise ValueError('Repeated input')
 for machine in machines:
  table=codes(machine);masks=[m for m in range(2,16,2) if trail_check(table,m)]
  if not masks:continue
  mask=min(masks,key=lambda m:(m.bit_count(),m));old=any(marker_check(table,m) for m in masks) or capacity_weights(table) is not None
  rows.append(dict(machine=machine,marker_mask=mask,covered_by_prior=old));new+=not old
 report=dict(status='untrusted_marker_exit_trail_measurement',input_families=len(machines),candidates=len(rows),new_beyond_v2_and_potential=new,
  rows=rows,input_sha256=sha(a.input),source_sha256={str(x.resolve().relative_to(REPO)):sha(x) for x in
   [Path(__file__),ROOT/'tools/marker_state_potential_profile.py',ROOT/'tools/marker_state_profile_v2.py',ROOT/'tools/generate_pipeline_examples.py']},
  kernel_checked=0,census_linked=0,scope='STATE ONLY proposed marker invariant and exit-trail argument; proof still required.')
 a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='rows'}))
if __name__=='__main__':main()
