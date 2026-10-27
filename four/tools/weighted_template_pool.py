"""Freeze an ordered union of immutable weighted pools without copying bundles.

This selects untrusted source certificates, not machine proofs. Every reuse
consumer must replay the full certificate checks for its selected targets.
"""
import argparse
from collections import Counter
import json
from pathlib import Path

from kernel_audit_cache import digest
from weighted_codec_v2 import bundle_decode

ROOT=Path(__file__).resolve().parents[1]


def merge(paths):
    bundles=[];registries=[];seen=set();kinds=Counter();total=0
    for path in paths:
        path=path.resolve();relative=str(path.relative_to(ROOT))
        registry=json.loads(path.read_text());count=0;local=Counter()
        for entry in registry['bundles']:
            bundle=(ROOT/entry['path']).resolve();bundle.relative_to(ROOT)
            if entry['path'] in seen:raise ValueError('Repeated bundle')
            seen.add(entry['path'])
            if digest(bundle)!=entry['sha256']:raise ValueError('Bundle hash changed')
            rows=bundle_decode(bundle.read_text())
            if len(rows)!=entry['rows'] or bundle.stat().st_size!=entry['bytes']:
                raise ValueError('Bundle size changed')
            count+=len(rows);local.update(r.get('kind','weighted') for r in rows)
            bundles.append(entry)
        if count!=registry['rows'] or dict(local)!=registry['kinds']:
            raise ValueError('Registry counts changed')
        registries.append(dict(path=relative,sha256=digest(path)))
        total+=count;kinds.update(local)
    return dict(format='BBB24 compact weighted certificates v2',bundles=bundles,
                rows=total,kinds=dict(kinds),source=dict(registries=registries,
                union_tool_sha256=digest(Path(__file__))),
                status='Ordered immutable candidate-pool union; no proof or census claim.')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--registry',type=Path,action='append',required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();data=merge(args.registry)
    text=json.dumps(data,indent=2,sort_keys=True)+'\n'
    if args.output.exists() and args.output.read_text()!=text:
        raise ValueError('Refusing to change an existing pool; choose a new output')
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(text)
    print(json.dumps({k:data[k] for k in ('rows','kinds')}))


if __name__=='__main__':main()
