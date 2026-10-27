"""Select proposals differing at one recurring transition (never proof evidence).

Dropping a comparison only widens an untrusted search filter. Every target
still requires its own exact blank-start ir_check and later kernel replay.
"""
import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
from affine_template_orbits import transform_table
from generate_pipeline_examples import codes

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pack(table):return sum(v<<(5*i) for i,v in enumerate(table))
def bits(mask):return sum(31<<(5*i) for i in range(8) if mask>>i&1)

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--source-index',type=Path,action='append',required=True)
 p.add_argument('--targets',type=Path,required=True)
 p.add_argument('--output',type=Path,required=True)
 p.add_argument('--profile',type=Path,required=True)
 p.add_argument('--cap',type=int,default=8)
 a=p.parse_args()
 if a.cap<1:raise ValueError('Positive cap required')
 seeds=[];seen=set();bank=defaultdict(dict)
 for path in a.source_index:
  for seed in json.loads(path.read_text())['seeds']:
   token=seed['certificate'];original=seed['mask']
   if token in seen or original.bit_count()<6:continue
   seen.add(token)
   table,_=transform_table(codes(seed['source']),255,seed['permutation'],seed['mirror'],seed['state_swap'])
   n=pack(table);index=len(seeds);seeds.append(seed)
   for i in range(8):
    if not original>>i&1:continue
    mask=original^(1<<i);signature=n&bits(mask)
    bucket=bank[mask].setdefault(signature,[])
    if len(bucket)<a.cap:bucket.append(index)
 prepared=[(bits(mask),mask.bit_count(),buckets) for mask,buckets in sorted(bank.items(),key=lambda x:-x[0].bit_count())]
 machines=a.targets.read_text().splitlines();rows=[]
 if len(set(machines))!=len(machines):raise ValueError('Repeated target ID')
 for machine in machines:
  table=codes(machine);n=pack(table);choices=set()
  for bitmask,_,buckets in prepared:choices.update(buckets.get(n&bitmask,[]))
  if choices:
   chosen=sorted(choices,key=lambda i:(-seeds[i]['mask'].bit_count(),seeds[i]['has_blocks'],seeds[i]['certificate']))[:a.cap]
   rows.append(dict(machine=machine,templates=chosen,uncapped_templates=len(choices)))
 a.output.parent.mkdir(parents=True,exist_ok=True)
 a.output.write_text(json.dumps(dict(seeds=seeds,targets=rows),separators=(',',':'))+'\n')
 report=dict(status='untrusted_one_transition_relaxed_proposals',target_families=len(machines),
  compatible_targets=len(rows),source_templates=len(seeds),mask_groups=len(bank),cap=a.cap,
  target_template_pairs=sum(len(r['templates']) for r in rows),
  input_sha256={str(x.resolve().relative_to(REPO)):sha(x) for x in a.source_index+[a.targets]},
  source_sha256=sha(Path(__file__)),index_sha256=sha(a.output))
 a.profile.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
if __name__=='__main__':main()
