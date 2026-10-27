"""Export immutable completed weighted-search ranges as they become available.

This orchestration does not change the search, snapshot format, or proof logic.
The existing snapshot exporter validates each consecutive ledger-prefix range.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--campaign-dir',type=Path,required=True)
    parser.add_argument('--snapshots-dir',type=Path,required=True)
    parser.add_argument('--index',type=Path,required=True)
    parser.add_argument('--chunk-size',type=int,default=2048)
    args=parser.parse_args()
    if args.chunk_size<1:parser.error('Positive chunk size required')
    manifest_path=args.campaign_dir/'manifest.json'
    manifest=json.loads(manifest_path.read_text());manifest_hash=sha(manifest_path)
    total=manifest['input_rows'];offset=0;completed=0;batch=0;snapshots=[]
    args.index.parent.mkdir(parents=True,exist_ok=True)
    while batch*args.chunk_size<total:
        if sha(manifest_path)!=manifest_hash:raise ValueError('Frozen campaign manifest changed')
        ledger=args.campaign_dir/'results.jsonl'
        if ledger.exists():
            if ledger.stat().st_size<offset:raise ValueError('Committed ledger was truncated')
            with ledger.open('rb') as stream:
                stream.seek(offset)
                while line:=stream.readline():
                    if not line.endswith(b'\n'):break
                    completed+=1;offset=stream.tell()
        if completed>total:raise ValueError('Ledger exceeds frozen input inventory')
        end=min((batch+1)*args.chunk_size,total)
        if completed<end:time.sleep(15);continue
        directory=args.snapshots_dir/f'batch{batch:03d}';registry=directory/'registry.json'
        command=[sys.executable,str(Path(__file__).with_name('weighted_snapshot_v2.py')),
                 '--campaign-dir',str(args.campaign_dir),'--start',str(batch*args.chunk_size),
                 '--count',str(end-batch*args.chunk_size),'--bundle-dir',str(directory),'--registry',str(registry)]
        if batch:command+=['--previous-registry',str(args.snapshots_dir/f'batch{batch-1:03d}'/'registry.json')]
        subprocess.run(command,check=True)
        data=json.loads(registry.read_text())
        snapshots.append({'batch':batch,'input_range':[batch*args.chunk_size,end],
                          'registry':str(registry.resolve()),'registry_sha256':sha(registry),
                          'candidate_rows':data['rows'],'kinds':data['kinds']})
        index={'status':'Immutable untrusted candidate pools; each needs independent Coq replay.',
               'campaign_manifest_sha256':manifest_hash,'input_rows':total,'exported_input_rows':end,
               'snapshot_rows':sum(row['candidate_rows'] for row in snapshots),'snapshots':snapshots}
        temporary=args.index.with_suffix('.tmp');temporary.write_text(json.dumps(index,indent=2,sort_keys=True)+'\n');temporary.replace(args.index)
        print(json.dumps(snapshots[-1],sort_keys=True),flush=True);batch+=1


if __name__=='__main__':main()
