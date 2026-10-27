"""Index every full-mask source at targets differing in one table cell.

All symbol/reflection/state-swap variants are only suffix proposals. Acceptance
still requires a complete blank-start target ir_check and later kernel replay.
"""
import argparse
from collections import defaultdict
import csv
import hashlib
import itertools
import json
from pathlib import Path
from affine_template_bank import proposal
from affine_template_orbits import transform_table
from generate_pipeline_examples import codes

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pack(t):return sum(v<<(5*i) for i,v in enumerate(t))

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--ledger',type=Path,action='append',required=True)
 p.add_argument('--targets',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
 p.add_argument('--profile',type=Path,required=True);p.add_argument('--cap',type=int,default=8)
 a=p.parse_args()
 if a.cap<1:raise ValueError('Positive cap required')
 machines=a.targets.read_text().splitlines();tables=[codes(m) for m in machines];packed=list(map(pack,tables))
 if len(set(machines))!=len(machines):raise ValueError('Repeated target')
 masks=[((1<<40)-1)^(31<<(5*i)) for i in range(8)]
 lookups=[defaultdict(list) for _ in range(8)]
 for i,n in enumerate(packed):
  for hole,mask in enumerate(masks):lookups[hole][n&mask].append(i)
 constants={i:tables[0][i] for i in range(8) if all(t[i]==tables[0][i] for t in tables)}
 variants=[((0,)+q,m,s) for q in itertools.permutations((1,2,3)) for m in (0,1) for s in (0,1)]
 sources=[];source_ids=set()
 for path in a.ledger:
  for row in csv.DictReader(path.open(),delimiter='\t'):
   if row['status']!='replay_true' or row['machine'] in source_ids:continue
   source_ids.add(row['machine']);cert=REPO/row['certificate'];metadata,mask,blocks,_=proposal(cert)
   if metadata['machine']!=row['machine']:raise ValueError('Source identity differs')
   if mask==255:sources.append((bool(blocks),row['machine'],row['certificate'],cert))
 sources.sort()
 seeds=[];choices=[[] for _ in machines];uncapped=[0 for _ in machines];source_hits=0;transforms=0
 for blocks,machine,path,cert in sources:
  base=codes(machine);source_used=False;digest=None
  for perm,mirror,swap in variants:
   table,_=transform_table(base,255,perm,mirror,swap);n=pack(table)
   mismatching_constants=[i for i,value in constants.items() if table[i]!=value]
   if len(mismatching_constants)>1:continue
   holes=mismatching_constants if mismatching_constants else range(8)
   matches=set()
   for hole in holes:
    matches.update(i for i in lookups[hole].get(n&masks[hole],[]) if packed[i]!=n)
   if not matches:continue
   transforms+=1;source_used=True
   for i in matches:uncapped[i]+=1
   kept=[i for i in matches if len(choices[i])<a.cap]
   if not kept:continue
   if digest is None:digest=sha(cert)
   token=path+'|'+''.join(map(str,perm))+f'|{mirror}|{swap}';index=len(seeds)
   seeds.append(dict(source=machine,certificate=token,original_certificate_sha256=digest,
     mask=255,has_blocks=blocks,permutation=list(perm),mirror=mirror,state_swap=swap))
   for i in kept:choices[i].append(index)
  source_hits+=int(source_used)
 rows=[dict(machine=m,templates=choices[i],uncapped_templates=uncapped[i]) for i,m in enumerate(machines) if choices[i]]
 a.output.parent.mkdir(parents=True,exist_ok=True)
 a.output.write_text(json.dumps(dict(seeds=seeds,targets=rows),separators=(',',':'))+'\n')
 report=dict(status='untrusted_full_mask_neighbor_proposals',source_full_mask_families=len(sources),
  source_families_with_target_matches=source_hits,matching_transformed_tables=transforms,indexed_proposals=len(seeds),
  target_families=len(machines),compatible_targets=len(rows),target_template_pairs=sum(map(len,choices)),
  uncapped_target_template_pairs=sum(uncapped),cap=a.cap,constant_target_cells=constants,
  input_sha256={str(x.resolve().relative_to(REPO)):sha(x) for x in a.ledger+[a.targets]},
  source_sha256={str(x.resolve().relative_to(REPO)):sha(x) for x in [Path(__file__),ROOT/'tools/affine_template_bank.py',ROOT/'tools/affine_template_orbits.py']},
  index_sha256=sha(a.output))
 a.profile.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
if __name__=='__main__':main()
