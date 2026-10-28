"""Expand recurring affine proposals by symbol/state relabeling and reflection.

State swaps are allowed only as suffix-template proposals. Every target is
still replayed from the actual blank A-start by the unchanged affine checker.
"""
import argparse
from collections import Counter,defaultdict
import hashlib
import itertools
import json
from pathlib import Path

from generate_pipeline_examples import codes
from generate_affine import shared

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parent
BASE=ROOT/'build/affine-template-bank'


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def transform_table(table,mask,perm,mirror,swap):
    transformed=[16]*8;new_mask=0
    for cell,value in enumerate(table):
        target=4*((cell//4)^swap)+perm[cell%4]
        if mask>>cell&1:new_mask|=1<<target
        if value<16:transformed[target]=4*perm[value//4]+2*((value//2%2)^mirror)+((value%2)^swap)
    return transformed,new_mask


def transform_template(c,perm,mirror,swap):
    def state(q):return 'AB'['AB'.index(q)^swap]
    def block(i):return perm[i] if i<4 else i
    def template(side):return {i:(block(x),a,b) for i,(x,a,b) in side.items()}
    def runs(side):return {i:(block(x),count) for i,(x,count) in side.items()}
    left,right=template(c['tplL']),template(c['tplR'])
    if mirror:left,right=right,left
    rules={};prefixes={}
    for i,r in c['rules'].items():
        l,rr=runs(r['L']),runs(r['R']);prefix=c['pfx'].get(i,(False,False))
        if mirror:l,rr=rr,l;prefix=prefix[::-1]
        rules[i]=dict(st=state(r['st']),hs=perm[r['hs']],L=l,R=rr);prefixes[i]=prefix
    return dict(tplL=left,tplR=right,rules=rules,pfx=prefixes,
        blk={i:[perm[s] for s in word] for i,word in c['blk'].items()},
        kmin=c['kmin'],meta_a=c['meta_a'],meta_b=c['meta_b'],
        tpl_state=state(c['tpl_state']),tpl_hsym=perm[c['tpl_hsym']])


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base-index',type=Path,default=BASE/'index.json')
    parser.add_argument('--targets',type=Path,default=ROOT/'build/weighted-v2/full-cohort.txt')
    parser.add_argument('--output',type=Path,default=ROOT/'build/affine-template-orbits')
    parser.add_argument('--profile',type=Path,default=ROOT/'research/affine-template-orbit-profile.json')
    parser.add_argument('--cap',type=int,default=24)
    args=parser.parse_args()
    original=json.loads(args.base_index.read_text());source_rows=original['seeds']
    variants=[((0,)+p,m,s) for p in itertools.permutations((1,2,3)) for m in (0,1) for s in (0,1)]
    bank=defaultdict(lambda:defaultdict(dict));seeds=[];cache={};attempts=0
    for original_seed in source_rows:
        path=REPO/original_seed['certificate']
        if sha(path)!=original_seed['certificate_sha256']:raise ValueError('Source certificate changed')
        c=cache.get(str(path))
        if c is None:c=shared.parse_cert(path);cache[str(path)]=c
        table=codes(original_seed['source'])
        for perm,mirror,swap in variants:
            transformed,mask=transform_table(table,original_seed['mask'],perm,mirror,swap)
            signature=tuple(transformed[i] for i in range(8) if mask>>i&1)
            body=transform_template(c,perm,mirror,swap)
            identity=hashlib.sha256(json.dumps(body,sort_keys=True,separators=(',',':')).encode()).hexdigest()
            attempts+=1;bucket=bank[mask][signature]
            if identity in bucket:continue
            token=original_seed['certificate']+'|'+''.join(map(str,perm))+f'|{mirror}|{swap}'
            index=len(seeds);seeds.append(dict(source=original_seed['source'],certificate=token,
                original_certificate_sha256=original_seed['certificate_sha256'],template_sha256=identity,
                mask=mask,has_blocks=original_seed['has_blocks'],permutation=list(perm),mirror=mirror,state_swap=swap))
            bucket[identity]=index
    machines=args.targets.read_text().splitlines()
    if len(machines)!=len(set(machines)):raise ValueError('Repeated target')
    prepared=[(mask,tuple(i for i in range(8) if mask>>i&1),buckets) for mask,buckets in sorted(bank.items())]
    matches=[];raw=0;histogram=Counter()
    for machine in machines:
        table=codes(machine);choices=[]
        for mask,slots,buckets in prepared:
            bucket=buckets.get(tuple(table[i] for i in slots))
            if bucket:choices.extend(bucket.values());histogram[mask.bit_count()]+=1
        if not choices:continue
        choices=set(choices);raw+=len(choices)
        chosen=sorted(choices,key=lambda i:(seeds[i]['has_blocks'],
            seeds[i]['state_swap'],seeds[i]['mirror'],seeds[i]['permutation'],
            seeds[i]['source'],seeds[i]['template_sha256']))[:args.cap]
        matches.append(dict(machine=machine,templates=chosen,uncapped_templates=len(choices)))
    args.output.mkdir(parents=True,exist_ok=True)
    index=args.output/'index.json';index.write_text(json.dumps(dict(seeds=seeds,targets=matches),separators=(',',':'))+'\n')
    report=dict(status='untrusted_orbit_template_proposals',source_templates=len(source_rows),
        transformations_per_source=len(variants),transformed_template_attempts=attempts,
        indexed_proposals=len(seeds),distinct_masks=len(bank),target_families=len(machines),
        table_compatible_targets=len(matches),uncapped_proposals=raw,
        capped_proposals=sum(len(r['templates']) for r in matches),cap_per_target=args.cap,
        compatible_mask_size_histogram=dict(sorted(histogram.items())),
        input_sha256=dict(base_index=sha(args.base_index),targets=sha(args.targets),index=sha(index)),
        source_sha256={str(p.relative_to(REPO)):sha(p) for p in
            [Path(__file__).resolve(),ROOT/'tools/generate_affine.py',ROOT/'tools/generate_pipeline_examples.py',
             REPO/'tools/gen_irulesblkpfx_certs.py']},
        proof_status='No proof claim. State swaps apply to proposed suffix templates; actual target A-start and all recurrence claims are checked independently.')
    args.profile.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('source_sha256','input_sha256','proof_status')}))


if __name__=='__main__':main()
