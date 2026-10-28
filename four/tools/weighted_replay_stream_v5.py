"""Replay future snapshot batches with the proved-equal FastWall producer.

Use separate worker indices to share the queue. Scheduling priority is inherited
from the caller. Published reports are validated read-only and never refreshed;
fresh-checkout reconstruction is handled by replay_recorded_weighted_v5.py.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--campaign-dir',type=Path,required=True)
    parser.add_argument('--snapshots-dir',type=Path,required=True)
    parser.add_argument('--proof-root',type=Path,required=True)
    parser.add_argument('--worker',type=int,required=True)
    parser.add_argument('--workers',type=int,default=2)
    parser.add_argument('--start-batch',type=int,required=True)
    parser.add_argument('--chunk-size',type=int,default=2048)
    parser.add_argument('--batch-size',type=int,default=32)
    parser.add_argument('--timeout',type=int,default=1800)
    parser.add_argument('--after-report',type=Path)
    args=parser.parse_args()
    if not (0<=args.worker<args.workers and args.start_batch>=0 and args.start_batch%args.workers==args.worker and args.chunk_size>0 and args.batch_size>0 and args.timeout>0):
        parser.error('Invalid worker/range parameters')
    manifest=json.loads((args.campaign_dir/'manifest.json').read_text())
    count=(manifest['input_rows']+args.chunk_size-1)//args.chunk_size
    args.proof_root.mkdir(parents=True,exist_ok=True)
    if args.after_report:
        while not args.after_report.exists():time.sleep(15)
    for index in range(args.start_batch,count,args.workers):
        pool=args.snapshots_dir/f'batch{index:03d}';registry=pool/'registry.json'
        while not registry.exists():time.sleep(15)
        data=json.loads(registry.read_text())
        expected=[index*args.chunk_size,min((index+1)*args.chunk_size,manifest['input_rows'])]
        if data['source']['input_range']!=expected or data['source']['input_sha256']!=manifest['input_sha256']:
            raise ValueError('Snapshot belongs to another input range/cohort')
        if not data['rows']:
            print(json.dumps({'batch':index,'status':'empty_candidate_pool'}),flush=True);continue
        output=args.proof_root/f'batch{index:03d}-v5';report=pool/'check.json'
        command=[sys.executable,str(Path(__file__).with_name('record_weighted_audit_v5.py')),
                 '--registry',str(registry),'--output-dir',str(output),'--report',str(report),
                 '--inventory',str(pool/'machines.json'),'--namespace',f'BBB24WeightedFullB{index:03d}',
                 '--batch-size',str(args.batch_size),'--timeout',str(args.timeout)]
        if report.exists():command.append('--check')
        print(json.dumps({'batch':index,'status':'validating_recorded' if report.exists() else 'replaying','candidate_rows':data['rows']}),flush=True)
        with (args.proof_root/f'batch{index:03d}-v5-progress.log').open('a') as log:
            subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=True)
        checked=json.loads(report.read_text())
        if checked['manifest']['registry_sha256']!=__import__('hashlib').sha256(registry.read_bytes()).hexdigest():
            raise ValueError('Published proof belongs to another registry')
        # These scratch files are never part of a recorded proof. V5 normally
        # suppresses them, but clean up any prior interrupted compiler output.
        pinned=checked['artifacts_sha256']
        for path in output.glob('*.glob'):
            if path.name in pinned:raise ValueError('A glob file unexpectedly became a pinned artifact')
            path.unlink()
        print(json.dumps({'batch':index,'status':'audited','census_linked':checked['census_linked'],
                          'counts':checked['counts'],'report':str(report)},sort_keys=True),flush=True)


if __name__=='__main__':main()
