"""Index full-instruction affine templates only at exact transformed tables.

Full masks were omitted by the first bank. State-swapped suffix proposals can
nevertheless apply to a different blank A-start orbit; target ir_check decides.
"""
import argparse
from collections import Counter,defaultdict
import csv
import hashlib
import itertools
import json
from pathlib import Path

from affine_template_bank import proposal
from affine_template_orbits import transform_table,transform_template
from generate_affine import shared
from generate_pipeline_examples import codes

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parent


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ledger',type=Path,default=ROOT/'build/affine-wave/replay4096/replay.tsv')
    parser.add_argument('--targets',type=Path,default=ROOT/'build/weighted-v2/full-cohort.txt')
    parser.add_argument('--output',type=Path,default=ROOT/'build/affine-template-fullmask')
    parser.add_argument('--profile',type=Path,default=ROOT/'research/affine-template-fullmask-profile.json')
    args=parser.parse_args()
    machines=args.targets.read_text().splitlines();lookup={tuple(codes(m)):m for m in machines}
    if len(lookup)!=len(machines):raise ValueError('Repeated target table')
    variants=[((0,)+p,m,s) for p in itertools.permutations((1,2,3)) for m in (0,1) for s in (0,1)]
    rows=[r for r in csv.DictReader(args.ledger.open(),delimiter='\t') if r['status']=='replay_true']
    bank=defaultdict(dict);seeds=[];source_full=0;source_hits=0;transform_hist=Counter()
    for row in rows:
        path=REPO/row['certificate'];metadata,mask,blocks,_=proposal(path)
        if mask!=255:continue
        source_full+=1
        table=codes(row['machine']);hits=[]
        for perm,mirror,swap in variants:
            transformed,_=transform_table(table,255,perm,mirror,swap)
            target=lookup.get(tuple(transformed))
            if target:hits.append((target,perm,mirror,swap))
        if not hits:continue
        source_hits+=1;c=shared.parse_cert(path)
        for target,perm,mirror,swap in hits:
            body=transform_template(c,perm,mirror,swap)
            identity=hashlib.sha256(json.dumps(body,sort_keys=True,separators=(',',':')).encode()).hexdigest()
            if identity in bank[target]:continue
            token=row['certificate']+'|'+''.join(map(str,perm))+f'|{mirror}|{swap}'
            index=len(seeds);seeds.append(dict(source=row['machine'],certificate=token,
                original_certificate_sha256=sha(path),template_sha256=identity,mask=255,
                has_blocks=bool(blocks),permutation=list(perm),mirror=mirror,state_swap=swap))
            bank[target][identity]=index;transform_hist['state_swap' if swap else 'same_initial_state']+=1
    targets=[dict(machine=m,templates=list(bank[m].values()),uncapped_templates=len(bank[m])) for m in machines if m in bank]
    args.output.mkdir(parents=True,exist_ok=True)
    index=args.output/'index.json';index.write_text(json.dumps(dict(seeds=seeds,targets=targets),separators=(',',':'))+'\n')
    report=dict(status='untrusted_full_mask_template_proposals',source_full_mask_families=source_full,
        source_families_with_target_matches=source_hits,target_families=len(machines),
        compatible_targets=len(targets),template_proposals=len(seeds),transform_histogram=dict(transform_hist),
        input_sha256=dict(ledger=sha(args.ledger),targets=sha(args.targets),index=sha(index)),
        source_sha256={str(p.relative_to(REPO)):sha(p) for p in
            [Path(__file__).resolve(),ROOT/'tools/affine_template_bank.py',ROOT/'tools/affine_template_orbits.py',
             ROOT/'tools/generate_affine.py',ROOT/'tools/generate_pipeline_examples.py',REPO/'tools/gen_irulesblkpfx_certs.py']},
        proof_status='No proof count. Exact transformed tables select proposals; target prefix and all affine recurrence claims must be checked from the actual A-start.')
    args.profile.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('input_sha256','source_sha256','proof_status')}))


if __name__=='__main__':main()
