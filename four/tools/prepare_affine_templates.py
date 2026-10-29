"""Regenerate/recompile already audited affine bundles for an aggregate audit.

This never rewrites the frozen audit reports or runs another recursive audit.
It checks the bundle, source and every generated Coq-source digest first.
The final campaign coqchk must include the emitted module names.
"""
import argparse
import json
from pathlib import Path
import re

import check_affine_wave as checker

ROOT=Path(__file__).resolve().parents[1]


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report',type=Path,action='append',required=True)
    parser.add_argument('--timeout',type=int,default=600)
    args=parser.parse_args()
    sources=checker.source_hashes()
    for report_path in args.report:
        report=json.loads(report_path.read_text())
        match=re.fullmatch(r'BBB24AffineWave\.([A-Z][A-Za-z0-9_]*)\.All',report['module'])
        if not match:raise ValueError('Unexpected audited module namespace')
        name=match.group(1)
        if sources!=report['source_sha256']:raise ValueError('Audited mathematical/generator sources changed')
        bundle=report_path.with_name(report_path.stem+'-input.json')
        if checker.sha(bundle)!=report['input_sha256']:raise ValueError('Audited input bundle changed')
        destination=checker.BUILD/name;destination.mkdir(parents=True,exist_ok=True)
        data,paths=checker.load_bundle(bundle,destination/'certs')
        if len(paths)!=report['checked_families'] or len(paths)!=report['census_linked_families']:
            raise ValueError('Audited family inventory differs')
        parts=[];generated=[]
        for start in range(0,len(paths),checker.SHARD_SIZE):
            part=f'Part{start//checker.SHARD_SIZE:04}';path=destination/f'{part}.v'
            path.write_text(checker.shard(paths[start:start+checker.SHARD_SIZE],data['bound'],data['cfuel'],data['fuel']))
            parts.append(part);generated.append(path)
        aggregate=destination/'All.v';aggregate.write_text(checker.aggregate(name,parts,data['bound'],len(paths)))
        generated.append(aggregate)
        if {p.name:checker.sha(p) for p in generated}!=report['shard_sha256']:
            raise ValueError('Regenerated Coq source differs from the audited bundle')
        for path in generated:checker.compile_file(path,sources,args.timeout,resume=True)
        print(json.dumps({'module':report['module'],'families':len(paths),
            'status':'Previously audited sources regenerated/compiled; include module in final aggregate audit'}),flush=True)


if __name__=='__main__':main()
