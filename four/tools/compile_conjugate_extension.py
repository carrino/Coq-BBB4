"""Prepare a conjugacy board for one shared campaign kernel audit.

This command deliberately publishes a COMPILED/QUEUED manifest, never a checked
family count. The campaign must recursively audit the named aggregate and bind
its exact source/object/dependency snapshot before promoting these rows.
Default reproduction needs only tracked compact input and built source boards.
"""
import argparse
import csv
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess

import check_conjugate_batch as base
from kernel_audit_cache import digest,snapshot

ROOT=Path(__file__).resolve().parents[1]


def load_sources(path):
    config=json.loads(path.read_text());machines=[];inputs={str(path.resolve().relative_to(ROOT)):digest(path)}
    loadpaths=[(ROOT/'theories','BBB24')]
    for source in config['sources']:
        for field in ('module','board','nonhalt','small_sound','sound'):
            base.identifier(source[field])
        if source.get('was_pending'):base.identifier(source['was_pending'])
        if type(source['bound'])is not int or not 0<=source['bound']<=config['source_bound']:
            raise ValueError('Invalid source bound')
        new=[]
        for entry in source['machine_inputs']:
            inputs[entry['path']]=digest(ROOT/entry['path'])
            if entry['format']=='checked_affine_tsv':
                with (ROOT/entry['path']).open() as f:rows=list(csv.DictReader(f,delimiter='\t'))
                if any(r['status']!='coq_checked' or int(r['proof_index'])!=i for i,r in enumerate(rows)):
                    raise ValueError('Affine inventory is not in checked proof order')
                new += [r['machine'] for r in rows]
            else:new += base.machine_rows(entry)
        for m in new:base.codes(m)
        source['count']=len(new);machines+=new
        for field in ('proof_source','audited_report'):inputs[source[field]]=digest(ROOT/source[field])
        if not (ROOT/source['proof_source']).with_suffix('.vo').is_file():raise ValueError('Source board not built')
        for entry in source['load_paths']:
            base.identifier(entry['namespace']);pair=(ROOT/entry['path'],entry['namespace'])
            if pair not in loadpaths:loadpaths.append(pair)
    return config,machines,inputs,loadpaths


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--name',default='r001')
    parser.add_argument('--config',type=Path,default=ROOT/'research/conjugate-sources-r001.json')
    parser.add_argument('--input',type=Path,default=ROOT/'research/conjugate-input-r001.json')
    parser.add_argument('--select',action='store_true')
    parser.add_argument('--exclude-input',action='append',type=Path,default=[])
    parser.add_argument('--timeout',type=int,default=36000)
    args=parser.parse_args()
    if not re.fullmatch(r'[a-z][a-z0-9_]*',args.name):raise ValueError('Invalid batch name')
    namespace='BBB24Conjugate'+args.name.capitalize();build=ROOT/'build/conjugate'/args.name;build.mkdir(parents=True,exist_ok=True)
    config,machines,inputs,loadpaths=load_sources(args.config)
    if args.select:
        data=base.select(config,machines,build,4096);excluded=set();exclusion_hashes={}
        for path in args.exclude_input:
            old=json.loads(path.read_text());column=old['columns'].index('machine')
            excluded.update(r[column] for r in old['rows']);exclusion_hashes[str(path.resolve().relative_to(ROOT))]=digest(path)
        data['selection']['excluded_previously_selected_cores']=sum(r[0] in excluded for r in data['rows'])
        data['exclusion_inputs_sha256']=exclusion_hashes
        data['rows']=[r for r in data['rows'] if r[0] not in excluded]
        args.input.write_text(base.compact(data))
    else:data=json.loads(args.input.read_text())
    base.validate(data,machines,config)
    inputs[str(args.input.resolve().relative_to(ROOT))]=digest(args.input)
    for path in [Path(__file__),ROOT/'tools/check_conjugate_batch.py',ROOT/'tools/kernel_audit_cache.py',ROOT/'tools/conjugate_probe.cpp']:
        inputs[str(path.resolve().relative_to(ROOT))]=digest(path)
    paths=base.generate(config,machines,data['rows'],build,namespace)
    loadpaths.append((build,namespace));loadargs=[x for p,n in loadpaths for x in ('-Q',str(p),n)]
    with (build/'compile.log').open('w') as log:
        for path in paths:
            print('Compiling '+path.name,flush=True)
            subprocess.run(['coqc','-native-compiler','no',*loadargs,str(path)],stdout=log,stderr=subprocess.STDOUT,check=True,timeout=args.timeout)
    if any(digest(ROOT/p)!=h for p,h in inputs.items()):raise ValueError('Pinned input changed during compilation')
    pinned=snapshot([paths[-1]],loadpaths)
    snapshot_path=build/'compiled-snapshot.json';snapshot_path.write_text(json.dumps(pinned,indent=2)+'\n')
    ledger=io.StringIO();writer=csv.writer(ledger,delimiter='\t',lineterminator='\n')
    writer.writerow(data['columns']+['state_bound','instruction_bound','status'])
    writer.writerows(r+[config['output_bound'],config['output_bound'],'compiled_queued_campaign_audit'] for r in data['rows'])
    descriptor=dict(module=namespace+'.ConjugateAll',board='board',nonhalt='nonhalt',small_sound='small_sound',sound='sound',was_pending='was_pending',bound=config['output_bound'],
                    proof_source=str(paths[-1].relative_to(ROOT)),load_paths=[dict(path=str(p.relative_to(ROOT)),namespace=n) for p,n in loadpaths if n!='BBB24'],
                    machine_inputs=[dict(path=str(args.input.resolve().relative_to(ROOT)),format='json_columns')],compiled_report=f'research/conjugate-{args.name}-compiled.json')
    report=dict(status='compiled_queued_campaign_recursive_audit',checked_canonical_cores=0,compiled_canonical_cores=len(data['rows']),
                compiled_baseline_search_survivors=sum(r[-1] for r in data['rows']),source_board_entries=len(machines),source_distinct_ids=len(set(machines)),
                descriptor=descriptor,selection=data['selection'],inputs=inputs,
                compiled_snapshot=str(snapshot_path.relative_to(ROOT)),compiled_snapshot_sha256=digest(snapshot_path),
                proof_artifacts_sha256={p.name:digest(p) for v in paths for p in (v,v.with_suffix('.vo'))},
                ledger_sha256=hashlib.sha256(ledger.getvalue().encode()).hexdigest(),
                promotion_requirement='A successful recursive campaign audit must include this exact module and source/object/transitive-dependency snapshot; compilation alone is not counted as an audited closeout.')
    (ROOT/f'research/conjugate-{args.name}-compiled.tsv').write_text(ledger.getvalue())
    (ROOT/f'research/conjugate-{args.name}-compiled.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ('status','compiled_canonical_cores','compiled_baseline_search_survivors')}))


if __name__=='__main__':main()
