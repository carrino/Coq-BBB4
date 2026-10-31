"""Audit search accounting without treating search output as a proof.

The result IDs must match the input exactly. Original-family counts are kept
separate from expanded child nodes, and concrete/partial families are separate.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

from generate_pipeline_examples import codes
from check_late_cycles import cert_text

ROOT=Path(__file__).resolve().parents[1]


def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def tree_budget(cert,fuel):
    cert_text(cert)
    if cert[0]=='C':
        if cert[2]+cert[3]>fuel: raise ValueError('Cycle exceeds the recorded walk budget')
        return 1,1,0
    if cert[1]>fuel: raise ValueError('Branch anchor exceeds the recorded walk budget')
    children=[tree_budget(c,fuel) for c in cert[2]]
    return 1+max(c[0] for c in children),1+sum(c[1] for c in children),1+sum(c[2] for c in children)


def summarize(input_path,result_path,fuel,nodes,statistics):
    machines=input_path.read_text().splitlines()
    rows=[json.loads(line) for line in result_path.read_text().splitlines()]
    if len(machines)!=len(set(machines)) or [r['machine'] for r in rows]!=machines:
        raise ValueError('Search output must contain every input exactly once, in input order')
    accepted=[]
    for row in rows:
        free=codes(row['machine']).count(16)
        if row['free_cells']!=free or not 1<=row['nodes']<=nodes or not 0<=row['steps']<=fuel*row['nodes']:
            raise ValueError(f'Invalid search accounting: {row["machine"]}')
        if row['status']=='candidate_closed':
            depth,count,branches=tree_budget(row['certificate'],fuel)
            if depth>free+1 or count!=row['nodes'] or branches!=row['branch_nodes']:
                raise ValueError('Closed-tree nodes do not match the original family accounting')
            accepted.append(row)
        elif row['status']!='pending' or row['certificate'] is not None:
            raise ValueError('Unknown search status or a certificate on an open family')
    concrete=sum(r['free_cells']==0 for r in rows)
    partial=len(rows)-concrete
    check={'families':len(rows),'candidate_closed':len(accepted),'concrete':concrete,'partial':partial,
           'partial_candidate_closed':sum(r['free_cells']>0 for r in accepted),
           'steps':sum(r['steps'] for r in rows)}
    if any(statistics[k]!=v for k,v in check.items()):
        raise ValueError('Search statistics differ from the complete row inventory')
    return dict(status='Untrusted cycle/census search; proof counts require the separate checked report.',
        parameters={'fuel':fuel,'nodes_per_original_family':nodes,'candidate_bound':fuel+1,
                    'algorithm':'Brent checkpoints, normalized ray hashes, exact tape confirmation; no fixed period window'},
        input_sha256=sha(input_path),results_sha256=sha(result_path),search_source_sha256=sha(ROOT/'tools/late_cycles.cpp'),
        original_families=len(rows),concrete_families=concrete,partial_families=partial,
        candidate_closed_original_families=len(accepted),
        candidate_concrete_families=sum(r['free_cells']==0 for r in accepted),
        candidate_partial_families=sum(r['free_cells']>0 for r in accepted),
        certificate_roots=dict(Counter(r['certificate'][0] for r in accepted)),
        pending_original_families=len(rows)-len(accepted),
        original_families_reaching_undefined=sum(r['branch_nodes']>0 for r in rows),
        expanded_defined_children=sum(r['nodes']-1 for r in rows),
        anchor_histogram=dict(sorted(Counter(r['max_anchor'] for r in accepted).items())),
        largest_candidate_period=max((r['max_period'] for r in accepted),default=0),
        simulated_steps=check['steps'],seconds=statistics['seconds'],
        accounting='Expanded children are search work, not additional original families. Each branching proof also covers the None/halting choice.')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path)
    parser.add_argument('results',type=Path)
    parser.add_argument('--statistics',type=Path,required=True)
    parser.add_argument('--fuel',type=int,required=True)
    parser.add_argument('--nodes',type=int,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result=summarize(args.input,args.results,args.fuel,args.nodes,json.loads(args.statistics.read_text()))
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['original_families','candidate_closed_original_families',
                                         'candidate_concrete_families','candidate_partial_families']}))


if __name__=='__main__': main()
