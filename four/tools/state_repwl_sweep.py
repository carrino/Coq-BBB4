"""Resumable STATE-only repeated-word closure search. No instruction claims.

The input is a fixed state work queue with an input-manifest hash. Accepted
rows remain search candidates until check_state_repwl_batch.py replays them.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess

from check_shadow_links import dependency_hashes
from pipeline_sweep import digest, encoded, read_rows, read_results

ROOT=Path(__file__).resolve().parents[1]
BUILD=ROOT/'build/state-repwl'
FIELDS=('machine','stage','mode','bound','size','anchor','fuel','extra','history')


def source_hashes():
    files={str(p.relative_to(ROOT)):digest(p) for p in (
        Path(__file__).resolve(), ROOT/'tools/ExtractStateRepWL.v',
        ROOT/'tools/state_repwl_probe.ml',ROOT/'tools/pipeline_sweep.py',
        ROOT/'tools/check_shadow_links.py')}
    return {**files,**dependency_hashes([ROOT/'theories/StateRepWL.v'],['-Q',str(ROOT/'theories'),'BBB24'])}


def build_probe(probe):
    BUILD.mkdir(parents=True,exist_ok=True)
    commands=[
        ['coqc','-native-compiler','no','-Q','theories','BBB24','tools/ExtractStateRepWL.v'],
        ['ocamlopt','-w','-a','-I','build/state-repwl','-c','build/state-repwl/checkers.mli'],
        ['ocamlopt','-w','-a','-I','build/state-repwl','-c','build/state-repwl/checkers.ml'],
        ['ocamlopt','-w','-a','-I','build/state-repwl','-c','-o','build/state-repwl/state_repwl_probe.cmx','tools/state_repwl_probe.ml'],
        ['ocamlopt','-w','-a','-I','build/state-repwl','unix.cmxa','build/state-repwl/checkers.cmx','build/state-repwl/state_repwl_probe.cmx','-o',str(probe.resolve())]]
    for command in commands:subprocess.run(command,cwd=ROOT,check=True)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,default=ROOT/'build/state-pipeline/deep-full/not-accepted.txt')
    parser.add_argument('--input-manifest',type=Path,default=ROOT/'research/state-closure-deep-full.json')
    parser.add_argument('--output-dir',type=Path,default=BUILD/'survey-pilot')
    parser.add_argument('--report',type=Path,default=ROOT/'research/state-repwl-pilot.json')
    parser.add_argument('--stages',type=Path,default=ROOT/'research/state-repwl-stages.json')
    parser.add_argument('--probe',type=Path,default=BUILD/'probe')
    parser.add_argument('--bound',type=int,default=4096)
    parser.add_argument('--timeout',type=float,default=0.5)
    parser.add_argument('--sample',type=int,default=512,help='Lowest machine SHA256 hashes;0 means all input rows')
    parser.add_argument('--build',action='store_true')
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    if args.bound<0 or args.sample<0 or not 0<args.timeout<float('inf'):
        parser.error('Invalid bound, sample size, or timeout')
    stages=json.loads(args.stages.read_text())
    if not stages:parser.error('At least one stage is required')
    for stage in stages:
        if set(stage)!={'mode','size','anchor','fuel','extra','history'} or stage['mode'] != 'rw':
            parser.error('Invalid checker stage')
        if not all(type(stage[k]) is int for k in ('size','anchor','fuel','extra','history')):
            parser.error('Checker parameters must be integers')
        if stage['size']<1 or stage['fuel']<1 or stage['extra']<2 or not 0<=stage['anchor']<=args.bound or stage['history']!=0:
            parser.error('Invalid checker parameters')
    inventory=read_rows(args.input)
    prior=json.loads(args.input_manifest.read_text())
    expected_hash=prior.get('remaining_sha256',prior.get('not_accepted_sha256'))
    expected_rows=prior.get('remaining_rows',prior.get('not_accepted_rows'))
    if digest(args.input)!=expected_hash or len(inventory)!=expected_rows:
        raise ValueError('State queue differs from its input manifest')
    if args.build:build_probe(args.probe)
    rows=sorted(inventory,key=lambda m:hashlib.sha256(m.encode()).digest())
    if args.sample:rows=rows[:args.sample]
    args.output_dir.mkdir(parents=True,exist_ok=True)
    manifest={'scope':'state only','input_sha256':digest(args.input),'input_rows':len(inventory),
        'input_manifest_sha256':digest(args.input_manifest),'selected_rows':len(rows),
        'selected_sha256':hashlib.sha256(encoded(rows).encode()).hexdigest(),
        'selection':'lowest SHA256(machine UTF-8) values' if args.sample else 'all rows ordered by SHA256(machine UTF-8)',
        'state_bound':args.bound,'instruction_bound':None,'stages':stages,
        'timeout_seconds_per_stage_row':args.timeout,'probe_sha256':digest(args.probe),
        'extraction_sha256':digest(BUILD/'checkers.ml'),'source_sha256':source_hashes()}
    manifest_path=args.output_dir/'manifest.json'
    if manifest_path.exists():
        if json.loads(manifest_path.read_text())!=manifest:
            raise ValueError('Input, sources, parameters or binary changed; use a new output directory')
    elif args.check:raise ValueError('Missing saved manifest')
    else:
        manifest_path.write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
        (args.output_dir/'selected.txt').write_text(encoded(rows))
    if (args.output_dir/'selected.txt').read_text()!=encoded(rows):raise ValueError('Selected input differs')
    remaining=rows;accepted=[];reports=[]
    for index,stage in enumerate(stages):
        path=args.output_dir/f'stage-{index:02d}.tsv'
        found=read_results(path,set(remaining),repair=not args.check)
        todo=[m for m in remaining if m not in found]
        if todo and args.check:raise ValueError(f'Stage{index}: missing{len(todo)} outcomes')
        if todo:
            input_path=args.output_dir/f'stage-{index:02d}-todo.txt';input_path.write_text(encoded(todo))
            command=[str(args.probe.resolve()),stage['mode'],str(args.bound),str(stage['size']),
                str(stage['anchor']),str(stage['fuel']),str(stage['extra']),str(stage['history']),
                str(args.timeout),str(input_path.resolve())]
            with path.open('a') as stream:subprocess.run(command,stdout=stream,check=True)
            found=read_results(path,set(remaining))
        if len(found)!=len(remaining):raise ValueError('Incomplete stage log')
        counts=Counter(status for status,_ in found.values())
        report={'stage':index,**stage,'rows':len(remaining),'statuses':dict(sorted(counts.items())),
                'sum_row_seconds':round(sum(t for _,t in found.values()),6),
                'results_sha256':digest(path) if path.exists() else None}
        reports.append(report);print(json.dumps(report,sort_keys=True),flush=True)
        accepted.extend({'machine':m,'stage':index,**stage,'bound':args.bound}
                        for m in remaining if found[m][0]=='candidate')
        remaining=[m for m in remaining if found[m][0]!='candidate']
    candidates='\t'.join(FIELDS)+'\n'+''.join('\t'.join(str(row[k]) for k in FIELDS)+'\n' for row in accepted)
    report={'scope':'Untrusted state-only search; no kernel replay or instruction-bound claims.',
        'manifest':manifest,'results':reports,'candidate_rows':len(accepted),
        'not_accepted_rows':len(remaining),'state_kernel_checked_rows':0,'instruction_kernel_checked_rows':0,
        'candidate_tsv_sha256':hashlib.sha256(candidates.encode()).hexdigest(),
        'not_accepted_sha256':hashlib.sha256(encoded(remaining).encode()).hexdigest()}
    outputs={args.output_dir/'candidates.tsv':candidates,args.output_dir/'not-accepted.txt':encoded(remaining),
             args.report:json.dumps(report,indent=2,sort_keys=True)+'\n'}
    for path,contents in outputs.items():
        if args.check:
            if not path.exists() or path.read_text()!=contents:raise ValueError(f'Output differs:{path}')
        else:
            path.parent.mkdir(parents=True,exist_ok=True);path.write_text(contents)
    print(f'{len(accepted)} state-only candidates;{len(remaining)} not accepted. Coq replay required.',flush=True)


if __name__=='__main__':main()
