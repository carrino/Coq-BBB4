"""Reproduce the exact-checker equivalence regression and paired wall benchmark.

The three machines are already selected suffix targets. This report measures
checker cost and contributes no additional census family count.
"""
import argparse
import json
from pathlib import Path
import resource
import subprocess
import time

import check_weighted_stream_reuse_v9 as producer
from kernel_audit_cache import audit,digest,fresh_paths
from weighted_transform_v2 import transform

ROOT=Path(__file__).resolve().parents[1]


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--refresh',action='store_true')
    parser.add_argument('--cache',type=Path,action='append',default=[])
    parser.add_argument('--adopt-timings',type=Path,
                        help='Record already completed paired compiles; exact sources and all proof objects are still kernel-audited')
    args=parser.parse_args()
    build=ROOT/'build/fast-wall';build.mkdir(parents=True,exist_ok=True)
    report_path=ROOT/'research/fast-wall-check.json'
    registry=ROOT/'research/weighted-stream-reuse/pools001_006.json'
    source_input=ROOT/'research/weighted-stream-reuse/pools001_006-input.json'
    pool,_,pins=producer.sources(registry)
    for p in (source_input,Path(__file__),Path(producer.__file__),ROOT/'theories/FastWallRegression.v'):
        pins[str(p.resolve().relative_to(ROOT))]=digest(p)
    producer.native.coq.transform=transform
    rows=json.loads(source_input.read_text())['rows'];sources={};samples=[]
    for index in [219,410,631]:
        row=next(r for r in rows if r[1]==index);samples.append(row)
        old,_=producer.original_template(pool[index],[row],'Example',True)
        fast,_=producer.template(pool[index],[row],'Example',True)
        sources[f'Old{index}.v']=producer.native.coq.COMMON+old
        sources[f'Fast{index}.v']=producer.COMMON+fast
    for name,body in sources.items():
        path=build/name
        if args.adopt_timings and (not path.exists() or path.read_text()!=body):
            raise ValueError('Measured source differs: '+name)
        path.write_text(body)
    sources['BenchmarkAll.v']='From BBB24 Require Import FastWallRegression.\nFrom BBB24FastWallBench Require Import '+ ' '.join(Path(n).stem for n in sources)+'.\n'
    (build/'BenchmarkAll.v').write_text(sources['BenchmarkAll.v'])
    flags=['-native-compiler','no','-Q',str(ROOT/'theories'),'BBB24','-Q',str(build),'BBB24FastWallBench']
    timing=[]
    if args.adopt_timings:
        timing=json.loads(args.adopt_timings.read_text())
        expected={(i,k)for i in [219,410,631]for k in ['Old','Fast']}
        if {(r['source'],r['kind'])for r in timing}!=expected or any(r['status']!=0 for r in timing):
            raise ValueError('Incomplete historical measurement')
    with(build/'benchmark-compile.log').open('w')as log:
        paths=[ROOT/'theories/FastWall.v',ROOT/'theories/FastWallRegression.v']+[build/n for n in sources]
        for path in paths:
            if args.adopt_timings and path.name!='BenchmarkAll.v':
                if not path.with_suffix('.vo').exists():raise ValueError('Missing compiled measurement')
                continue
            before=resource.getrusage(resource.RUSAGE_CHILDREN);start=time.monotonic()
            subprocess.run(['coqc',*flags,str(path)],stdout=log,stderr=subprocess.STDOUT,check=True)
            after=resource.getrusage(resource.RUSAGE_CHILDREN)
            if path.stem.startswith(('Old','Fast'))and path.parent==build:
                kind='Old'if path.stem.startswith('Old')else'Fast'
                timing.append(dict(source=int(path.stem[len(kind):]),kind=kind,status=0,
                    cpu_seconds=after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,
                    wall_seconds=time.monotonic()-start))
            print('Compiled '+path.name,flush=True)
    receipt_path,log=fresh_paths(build,'benchmark-audit')
    receipt=audit(['BBB24FastWallBench.BenchmarkAll'],[build/'BenchmarkAll.v'],
        [(ROOT/'theories','BBB24'),(build,'BBB24FastWallBench')],receipt_path,log,cache=args.cache)
    if any(digest(ROOT/p)!=h for p,h in pins.items()):raise ValueError('Pinned input changed')
    result=dict(status='Kernel-audited equivalent checker and paired regression; no new census families counted.',
        samples=samples,inputs_sha256=pins,proof_source_sha256={n:digest(build/n)for n in sources},
        validation='coqc plus '+receipt['kind']+' coqchk',timing=timing,
        audit_receipt=str(receipt_path.relative_to(ROOT)),audit_receipt_sha256=digest(receipt_path),
        module='BBB24.FastWall',equality_theorems=['fast_wall_check_eq','fast_wt_ready_eq',
            'fast_wt_hybrid_check_eq','fast_wc_graph_check_eq','fast_weighted_suffix_check_eq'],
        assumptions='Equality theorems are closed under the global context.')
    if args.refresh:report_path.write_text(json.dumps(result,indent=2)+'\n')
    else:
        old=json.loads(report_path.read_text())
        for k in ('samples','inputs_sha256','proof_source_sha256','module','equality_theorems'):
            if result[k]!=old[k]:raise ValueError('Replay changed '+k)
    totals={k:sum(r['cpu_seconds']for r in timing if r['kind']==k)for k in ['Old','Fast']}
    print(json.dumps(dict(validation=result['validation'],compile_cpu_seconds=totals)),flush=True)


if __name__=='__main__':main()
