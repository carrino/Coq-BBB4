"""Freeze a completed range of an active weighted search for independent replay.

The append-only ledger may keep growing. Only complete newline-terminated
records through the requested endpoint are read; their exact prefix is hashed.
Each snapshot owns a disjoint input-row range and an immutable bundle registry.
"""
import argparse
import hashlib
import json
from pathlib import Path

from weighted_campaign_v2 import ROOT, emit_bundles, sha


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--campaign-dir',type=Path,required=True)
    parser.add_argument('--start',type=int,required=True)
    parser.add_argument('--count',type=int,required=True)
    parser.add_argument('--bundle-dir',type=Path,required=True)
    parser.add_argument('--registry',type=Path,required=True)
    parser.add_argument('--previous-registry',type=Path,
                        help='Required after the first batch; enforces consecutive, disjoint ranges')
    args=parser.parse_args()
    manifest_path=args.campaign_dir/'manifest.json'
    manifest=json.loads(manifest_path.read_text())
    end=args.start+args.count
    if args.start<0 or args.count<1 or end>manifest['input_rows']:parser.error('Invalid input-row range')
    previous=None
    if args.start:
        if args.previous_registry is None:parser.error('Noninitial snapshots require --previous-registry')
        previous=json.loads(args.previous_registry.read_text())
        old=previous['source']
        if old['input_range'][1]!=args.start or old['campaign_manifest_sha256']!=sha(manifest_path):
            raise ValueError('Previous snapshot is not the immediate preceding range')
        for bundle in previous['bundles']:
            if sha(ROOT/bundle['path'])!=bundle['sha256']:raise ValueError('Previous snapshot bundle differs')
    elif args.previous_registry is not None:parser.error('Initial snapshot cannot have a previous registry')
    for relative,digest in manifest['source_sha256'].items():
        if sha(ROOT/relative)!=digest:raise ValueError('Pinned source differs: '+relative)
    prefix=hashlib.sha256();rows=[];names=set()
    with (args.campaign_dir/'results.jsonl').open('rb') as stream:
        for index in range(end):
            line=stream.readline()
            if not line.endswith(b'\n'):raise ValueError('Requested range is not fully committed yet')
            prefix.update(line);row=json.loads(line)
            if previous is not None and index+1==args.start and prefix.hexdigest()!=previous['source']['ledger_prefix_sha256']:
                raise ValueError('Previously exported ledger prefix changed')
            if row['machine'] in names:raise ValueError('Duplicate source ledger machine')
            names.add(row['machine'])
            if row['candidate'] is not None and row['candidate']['machine']!=row['machine']:
                raise ValueError('Candidate machine differs from ledger machine')
            if index>=args.start:rows.append(row)
    source={'campaign_manifest_sha256':sha(manifest_path),'input_sha256':manifest['input_sha256'],
            'input_rows':manifest['input_rows'],'input_range':[args.start,end],
            'ledger_prefix_rows':end,'ledger_prefix_sha256':prefix.hexdigest(),
            'snapshot_tool_sha256':sha(Path(__file__))}
    if previous is not None:
        source['previous_registry']={'path':str(args.previous_registry.resolve().relative_to(ROOT)),
                                     'sha256':sha(args.previous_registry)}
    if args.registry.exists():
        previous=json.loads(args.registry.read_text())
        if previous['source']!=source:raise ValueError('Immutable snapshot already exists for different inputs')
        for bundle in previous['bundles']:
            if sha(ROOT/bundle['path'])!=bundle['sha256']:raise ValueError('Snapshot bundle differs')
        print(f"Validated immutable snapshot: {previous['rows']} candidates.");return
    if args.bundle_dir.exists() and any(args.bundle_dir.iterdir()):raise ValueError('Snapshot bundle directory is not empty')
    registry=emit_bundles(rows,args.bundle_dir,args.registry,source)
    print(json.dumps({'input_range':[args.start,end],'candidate_rows':registry['rows'],
                      'kinds':registry['kinds'],'registry_sha256':sha(args.registry)},sort_keys=True))


if __name__=='__main__':main()
