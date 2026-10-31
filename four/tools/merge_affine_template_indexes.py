"""Merge frozen suffix-proposal indexes without promoting any proof status."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,action='append')
    parser.add_argument('--output',type=Path,default=ROOT/'build/affine-template-shift/index.json')
    parser.add_argument('--profile',type=Path,default=ROOT/'research/affine-template-shift-index.json')
    args=parser.parse_args()
    inputs=args.input or [ROOT/'build/affine-template-orbits/index.json',ROOT/'build/affine-template-fullmask/index.json']
    seeds=[];identities={};targets={}
    for path in inputs:
        data=json.loads(path.read_text())
        for row in data['targets']:
            choices=targets.setdefault(row['machine'],set())
            for old in row['templates']:
                seed=data['seeds'][old];token=seed['certificate']
                if token not in identities:identities[token]=len(seeds);seeds.append(seed)
                choices.add(identities[token])
    rows=[dict(machine=m,templates=sorted(choices),uncapped_templates=len(choices)) for m,choices in targets.items()]
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(dict(seeds=seeds,targets=rows),separators=(',',':'))+'\n')
    report=dict(status='untrusted_template_index',targets=len(rows),used_templates=len(seeds),
        target_template_pairs=sum(len(r['templates']) for r in rows),
        inputs_sha256={str(p.relative_to(ROOT)):sha(p) for p in inputs},
        index_sha256=sha(args.output),builder_sha256=sha(Path(__file__)))
    args.profile.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))

if __name__=='__main__':main()
