"""Query frozen affine proposal indexes on a new target list.

This only selects untrusted templates; the target's actual blank-start replay
and all proof obligations still require the unchanged checker.
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

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source-index',type=Path,action='append',required=True)
    p.add_argument('--targets',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--profile',type=Path,required=True)
    p.add_argument('--cap',type=int,default=24)
    a=p.parse_args()
    if a.cap<1:raise ValueError('Positive cap required')
    seeds=[];seen=set();bank=defaultdict(lambda:defaultdict(list))
    for path in a.source_index:
        for seed in json.loads(path.read_text())['seeds']:
            token=seed['certificate']
            if token in seen:continue
            seen.add(token)
            table,_=transform_table(codes(seed['source']),255,seed['permutation'],seed['mirror'],seed['state_swap'])
            mask=seed['mask'];slots=[i for i in range(8) if mask>>i&1]
            signature=tuple(table[i] for i in slots)
            if 16 in signature:raise ValueError('Undefined recurring source transition')
            bank[mask][signature].append(len(seeds));seeds.append(seed)
    rows=[];machines=a.targets.read_text().splitlines()
    if len(machines)!=len(set(machines)):raise ValueError('Repeated target ID')
    prepared=[(tuple(i for i in range(8) if mask>>i&1),buckets) for mask,buckets in sorted(bank.items())]
    for machine in machines:
        table=codes(machine);choices=set()
        for slots,buckets in prepared:choices.update(buckets.get(tuple(table[i] for i in slots),[]))
        if choices:
            selected=sorted(choices,key=lambda i:(seeds[i]['has_blocks'],seeds[i]['state_swap'],seeds[i]['certificate']))[:a.cap]
            rows.append(dict(machine=machine,templates=selected,uncapped_templates=len(choices)))
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(dict(seeds=seeds,targets=rows),separators=(',',':'))+'\n')
    report=dict(status='untrusted_reindexed_affine_proposals',source_templates=len(seeds),
        target_families=len(machines),compatible_targets=len(rows),cap=a.cap,
        target_template_pairs=sum(len(r['templates']) for r in rows),
        input_sha256={str(x.resolve().relative_to(REPO)):sha(x) for x in a.source_index+[a.targets]},
        source_sha256=sha(Path(__file__)),index_sha256=sha(a.output))
    a.profile.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))

if __name__=='__main__':main()
