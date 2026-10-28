"""Audit frozen compiled source-tail boards without regenerating proof objects.

The original compilation snapshots and every pinned input must still match.
One audit covers the union of imported closures; separate promoted reports
share its exact-object receipt. Existing compiled reports remain historical.
"""
import argparse
import copy
import json
from pathlib import Path

from kernel_audit_cache import audit,digest,fresh_paths,snapshot

ROOT=Path(__file__).resolve().parents[1]


def within(path):
    result=path.resolve();result.relative_to(ROOT);return result


def validate(path):
    report=json.loads(path.read_text())
    if report['status']!='compiled_queued_campaign_audit' or report['checked_canonical_cores']!=0:
        raise ValueError('Expected an immutable compiled-only report')
    for relative,sha in report['inputs_sha256'].items():
        if digest(within(ROOT/relative))!=sha:raise ValueError('Pinned compilation input changed')
    descriptor=report['descriptor'];source=within(ROOT/descriptor['proof_source'])
    for name,sha in report['proof_source_sha256'].items():
        if digest(within(source.parent/name))!=sha:raise ValueError('Generated proof source changed')
    snap_path=within(ROOT/report['compiled_snapshot'])
    if digest(snap_path)!=report['compiled_snapshot_sha256']:raise ValueError('Compilation snapshot changed')
    paths=[(ROOT/'theories','BBB24')]+[(within(ROOT/e['path']),e['namespace'])for e in descriptor['load_paths']]
    if snapshot([source],paths)!=json.loads(snap_path.read_text()):
        raise ValueError('Compiled object or transitive dependency changed')
    ledger=path.with_name(path.name.removesuffix('-compiled.json')+'.tsv')
    if digest(ledger)!=report['ledger_sha256']:raise ValueError('Frozen target ledger changed')
    return report,source,paths


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiled-report',type=Path,action='append',required=True)
    parser.add_argument('--cache',type=Path,action='append',default=[])
    parser.add_argument('--build',type=Path,required=True)
    args=parser.parse_args()
    build=within(args.build);build.mkdir(parents=True,exist_ok=True)
    items=[];loadpaths=[];seen=set();pins={}
    for path in args.compiled_report:
        path=within(path);report,source,paths=validate(path)
        items.append((path,report,source));pins[str(path.relative_to(ROOT))]=digest(path)
        for pair in paths:
            if pair not in seen:seen.add(pair);loadpaths.append(pair)
    receipt_path,log=fresh_paths(build)
    receipt=audit([r['descriptor']['module']for _,r,_ in items],[s for _,_,s in items],
        loadpaths,receipt_path,log,cache=args.cache)
    for path,old,source in items:
        if digest(path)!=pins[str(path.relative_to(ROOT))]:raise ValueError('Compiled report changed during audit')
        validate(path)
        output=path.with_name(path.name.removesuffix('-compiled.json')+'-summary.json')
        report=copy.deepcopy(old);report['status']='kernel_audited'
        report['checked_canonical_cores']=report['compiled_canonical_cores']
        report['descriptor']['audited_report']=str(output.relative_to(ROOT))
        report.update(validation='Previously compiled immutable objects plus '+receipt['kind']+' coqchk',
            audit_receipt=str(receipt_path.relative_to(ROOT)),audit_receipt_sha256=digest(receipt_path),
            compiled_report=str(path.relative_to(ROOT)),compiled_report_sha256=digest(path),
            audit_driver_sha256=digest(Path(__file__)),
            note='The imported source proofs and new target proofs are covered by this exact-object audit closure. No compilation or source rankings were rerun.')
        if output.exists():
            prior=json.loads(output.read_text())
            for key in ('compiled_canonical_cores','checked_canonical_cores','descriptor','inputs_sha256','proof_source_sha256','ledger_sha256','compiled_report_sha256'):
                if prior[key]!=report[key]:raise ValueError('Portable promoted report changed')
            (build/(output.stem+'-latest.json')).write_text(json.dumps(report,indent=2)+'\n')
        else:output.write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps(dict(report=str(output.relative_to(ROOT)),families=report['checked_canonical_cores'],audit=receipt['kind'])),flush=True)


if __name__=='__main__':main()
