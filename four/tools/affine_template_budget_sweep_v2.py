"""Replay proposals with a CPU budget per symbolic tail, preserving exact target acceptance on a fixed, explicitly filtered cohort.

This produces search candidates, never proof counts. A successful target must
subsequently pass check_affine_wave.py and actual census-membership checks.
"""
import argparse
from collections import Counter
import csv
import hashlib
import json
from pathlib import Path
import subprocess

from affine_bundle_from_replay import inventory

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parent
BASE=ROOT/'build/affine-template-budget-v2'
EXTRACTED=ROOT/'build/affine-wave/extracted'
DEFAULT_EXCLUSIONS=[ROOT/'research'/name for name in [
    'late-cycles-full65536.json','late-cycles-extra262144.json',
    'alphabet23-families.json','alphabet-mask-families.json',
    'wave2-families.tsv','weighted-pilot-machines.json','affine-template427.tsv','affine-template181.tsv','affine-template245.tsv','affine-template12.tsv','affine-template-short-input.json']]
DEFAULT_EXCLUSIONS += [ROOT/'build/affine-template-short/source-prefix4.tsv',ROOT/'research/affine-template-relaxed511-input.json',ROOT/'research/affine-template-neighbors-input.json']


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--index',type=Path,default=ROOT/'build/affine-template-allfull-neighbor/index.json')
    parser.add_argument('--stage',default='full')
    parser.add_argument('--sample',type=int,default=0)
    parser.add_argument('--exclude',type=Path,action='append')
    parser.add_argument('--bound',type=int,default=4096)
    parser.add_argument('--cfuel',type=int,default=4096)
    parser.add_argument('--fuel',type=int,default=8192)
    parser.add_argument('--timeout',type=float,default=0.5)
    parser.add_argument('--tail-cpu',type=float,default=0.03)
    parser.add_argument('--retry-ledger',type=Path,action='append',default=[])
    parser.add_argument('--build',action='store_true')
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    if not args.stage.replace('_','').isalnum() or args.sample<0 or min(args.bound,args.cfuel,args.fuel)<=0 or args.timeout<=0:
        raise ValueError('Invalid stage/budget')
    BASE.mkdir(parents=True,exist_ok=True)
    if args.build:
        subprocess.run(['ocamlfind','ocamlopt','-package','zarith,unix','-I',str(EXTRACTED),
            '-c','-o',str(BASE/'affine_template_budget_probe_v2.cmx'),str(ROOT/'tools/affine_template_budget_probe_v2.ml')],check=True)
        subprocess.run(['ocamlfind','ocamlopt','-package','zarith,unix','-linkpkg','-I',str(EXTRACTED),
            str(EXTRACTED/'checker.cmx'),str(EXTRACTED/'affine_cert_io.cmx'),
            str(BASE/'affine_template_budget_probe_v2.cmx'),'-o',str(BASE/'probe')],check=True)
    data=json.loads(args.index.read_text());excluded=set()
    exclusions=args.exclude if args.exclude is not None else DEFAULT_EXCLUSIONS
    for path in exclusions:excluded.update(inventory(path))
    candidates=data['targets']
    retry=set()
    for path in args.retry_ledger:
        retry.update(row['machine'] for row in csv.DictReader(path.open(),delimiter='\t') if row['status']=='timeout')
    if args.retry_ledger:candidates=[row for row in candidates if row['machine'] in retry]
    if len(candidates)!=len({r['machine'] for r in candidates}):raise ValueError('Repeated target in index')
    selected=sorted([r for r in candidates if r['machine'] not in excluded],
                    key=lambda r:hashlib.sha256(r['machine'].encode()).digest())
    eligible=len(selected)
    if args.sample:selected=selected[:args.sample]
    output=BASE/args.stage;output.mkdir(parents=True,exist_ok=True)
    certdir=output/'certs';certdir.mkdir(exist_ok=True)
    input_path=output/'input.tsv'
    text=''.join(r['machine']+'\t'+'\t'.join(data['seeds'][i]['certificate'] for i in r['templates'])+'\n' for r in selected)
    if args.check:
        if input_path.read_text()!=text:raise ValueError('Selected target/template input changed')
    else:input_path.write_text(text)
    source_paths=[ROOT/'tools/affine_template_budget_sweep_v2.py',ROOT/'tools/affine_template_budget_probe_v2.ml',
        ROOT/'tools/affine_fullmask_neighbors.py',ROOT/'tools/affine_cert_io.ml',EXTRACTED/'checker.ml',
        EXTRACTED/'affine_cert_io.cmx',BASE/'probe']
    manifest=dict(index_sha256=sha(args.index),input_sha256=sha(input_path),
        excluded_inventory_sha256={str(p.relative_to(REPO)):sha(p) for p in exclusions},
        sources_sha256={str(p.relative_to(REPO)):sha(p) for p in source_paths},
        bound=args.bound,cfuel=args.cfuel,fuel=args.fuel,timeout=args.timeout,tail_cpu=args.tail_cpu,retry_ledger_sha256={str(p.resolve().relative_to(REPO)):sha(p) for p in args.retry_ledger},
        compatible_targets=len(candidates),eligible_targets=eligible,selected_targets=len(selected))
    manifest_path=output/'manifest.json'
    if manifest_path.exists():
        if json.loads(manifest_path.read_text())!=manifest:raise ValueError('Frozen search manifest differs')
    elif args.check:raise ValueError('Missing search manifest')
    else:manifest_path.write_text(json.dumps(manifest,indent=2)+'\n')
    ledger=output/'replay.tsv'
    if not args.check:
        if ledger.exists():raise ValueError('Use --check for an existing complete stage')
        with ledger.open('w') as out,(output/'search.log').open('w') as err:
            subprocess.run([str(BASE/'probe'),str(args.bound),str(args.cfuel),str(args.fuel),
                str(args.timeout),str(args.tail_cpu),str(input_path),str(certdir)],cwd=REPO,stdout=out,stderr=err,check=True)
    rows=list(csv.DictReader(ledger.open(),delimiter='\t'))
    if [r['machine'] for r in rows]!=[r['machine'] for r in selected]:raise ValueError('Incomplete or reordered target ledger')
    allowed={'replay_true','replay_false','no_template_match','timeout','unsupported','stack_overflow','invalid_certificate'}
    for row in rows:
        if row['status'] not in allowed:raise ValueError('Unknown native replay status')
        if row['status']=='replay_true':
            cert=Path(row['certificate'])
            if cert.resolve()!=(certdir/(row['machine']+'.cert')).resolve():raise ValueError('Certificate path mismatch')
            if cert.read_text().splitlines().count('machine '+row['machine'])!=1:raise ValueError('Certificate identity mismatch')
    accepted=[r['machine'] for r in rows if r['status']=='replay_true']
    report=dict(status='untrusted_native_replay',manifest=manifest,
        statuses=dict(Counter(r['status'] for r in rows)),accepted_targets=len(accepted),
        row_seconds=sum(float(r['seconds']) for r in rows),
        template_instances=sum(int(r['instances']) for r in rows),ir_check_calls=sum(int(r['checks']) for r in rows),
        tail_timeouts=sum(int(r['tail_timeouts']) for r in rows),replay_sha256=sha(ledger),kernel_checked_rows=0,census_linked_rows=0,
        accounting='Targets are original input families. Recurring source flags and boot hashes are proposal filters; unchanged target ir_check supplies only native replay evidence until Coq and census replay.')
    (output/'accepted.txt').write_text('\n'.join(accepted)+'\n')
    report_path=ROOT/f'research/affine-template-budget-v2-{args.stage}.json'
    serialized=json.dumps(report,indent=2)+'\n'
    if args.check:
        if report_path.read_text()!=serialized:raise ValueError('Search report differs from complete ledger')
    else:report_path.write_text(serialized)
    print(json.dumps({k:report[k] for k in ['statuses','accepted_targets','row_seconds','template_instances','ir_check_calls']}))


if __name__=='__main__':main()
