"""Profile reusable affine proposals; every target still requires ir_check.

Recurring instruction flags from search certificates are UNTRUSTED filters.
Neither matching a table mask nor a template is a proof of recurrence/bounds.
"""
import argparse
from collections import Counter,defaultdict
import csv
import hashlib
import json
from pathlib import Path

from generate_pipeline_examples import codes

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parent


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def proposal(path):
    lines=path.read_text().splitlines()
    metadata={};template=[];mask=0;blocks=0
    for line in lines:
        parts=line.split()
        if not parts:continue
        key=parts[0]
        if key=='claim_trans' and len(parts)>=3 and parts[2]=='I':
            slot=4*('AB'.index(parts[1][0]))+int(parts[1][1]);mask|=1<<slot
        if key=='blk':blocks+=1
        if key in ('machine','anchor_step','k0'):metadata[key]=parts[1]
        elif key.startswith('claim_') or key in ('decided_at_step','bbbcert','end'):pass
        else:template.append(line)
    identity=hashlib.sha256(('\n'.join(template)+'\n').encode()).hexdigest()
    return metadata,mask,blocks,identity


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ledger',type=Path,default=ROOT/'build/affine-wave/replay4096/replay.tsv')
    parser.add_argument('--targets',type=Path,default=ROOT/'build/affine-wave/replay4096/not-accepted.txt')
    parser.add_argument('--output',type=Path,default=ROOT/'build/affine-template-bank')
    parser.add_argument('--profile',type=Path,default=ROOT/'research/affine-template-profile.json')
    parser.add_argument('--cap',type=int,default=8)
    args=parser.parse_args()
    if args.cap<1:raise ValueError('Positive proposal cap required')
    ledger=list(csv.DictReader(args.ledger.open(),delimiter='\t'))
    rows=[r for r in ledger if r['status']=='replay_true']
    if len(rows)!=len({r['machine'] for r in rows}):raise ValueError('Repeated source machine')
    bank=defaultdict(lambda:defaultdict(dict));mask_counts=Counter();block_counts=Counter();template_ids=set();seeds=[]
    for row in rows:
        path=REPO/row['certificate'];metadata,mask,blocks,identity=proposal(path)
        if metadata['machine']!=row['machine']:raise ValueError('Certificate identity mismatch')
        mask_counts[mask.bit_count()]+=1;block_counts[blocks>0]+=1;template_ids.add(identity)
        if mask==255 or mask==0:continue
        table=codes(row['machine']);slots=tuple(i for i in range(8) if mask>>i&1)
        signature=tuple(table[i] for i in slots)
        if any(v==16 for v in signature):continue
        bucket=bank[mask][signature]
        if identity not in bucket:
            index=len(seeds);seeds.append(dict(source=row['machine'],certificate=row['certificate'],
                certificate_sha256=sha(path),template_sha256=identity,mask=mask,has_blocks=bool(blocks)))
            bucket[identity]=index
    machines=args.targets.read_text().splitlines()
    if len(machines)!=len(set(machines)):raise ValueError('Repeated target')
    prepared=[(mask,tuple(i for i in range(8) if mask>>i&1),buckets) for mask,buckets in sorted(bank.items())]
    matches=[];raw_proposals=0;mask_hits=Counter()
    for machine in machines:
        table=codes(machine);choices=[]
        for mask,slots,buckets in prepared:
            bucket=buckets.get(tuple(table[i] for i in slots))
            if bucket:
                choices.extend(bucket.values());mask_hits[mask.bit_count()]+=1
        if not choices:continue
        raw_proposals+=len(choices)
        # Prefer ordinary RLE proposals, then stable source identity.
        chosen=sorted(set(choices),key=lambda i:(seeds[i]['has_blocks'],seeds[i]['source'],seeds[i]['template_sha256']))[:args.cap]
        matches.append(dict(machine=machine,templates=chosen,uncapped_templates=len(set(choices))))
    args.output.mkdir(parents=True,exist_ok=True)
    index=args.output/'index.json';index.write_text(json.dumps(dict(seeds=seeds,targets=matches),separators=(',',':'))+'\n')
    profile=dict(status='untrusted_affine_template_proposals',source_replay_true=len(rows),
        recurring_mask_size_histogram=dict(sorted(mask_counts.items())),block_templates=dict(block_counts),
        unique_templates=len(template_ids),indexed_proposals=len(seeds),distinct_masks=len(bank),
        target_families=len(machines),table_compatible_targets=len(matches),uncapped_proposals=raw_proposals,
        capped_proposals=sum(len(r['templates']) for r in matches),cap_per_target=args.cap,
        compatible_mask_size_histogram=dict(sorted(mask_hits.items())),
        input_sha256=dict(ledger=sha(args.ledger),targets=sha(args.targets),index=sha(index)),
        source_sha256={str(p.relative_to(ROOT)):sha(p) for p in [Path(__file__).resolve(),ROOT/'tools/generate_pipeline_examples.py']},
        proof_status='No target success or family discharge is claimed. Source recurring flags only select proposals; target ir_check remains necessary.')
    args.profile.write_text(json.dumps(profile,indent=2)+'\n')
    print(json.dumps({k:v for k,v in profile.items() if k not in ('source_sha256','input_sha256','proof_status')}))


if __name__=='__main__':main()
