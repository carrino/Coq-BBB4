"""Validate the portable full-search candidate partition without claiming proofs.

The census input and immutable snapshot bundles suffice on a clean checkout.
The complement means no candidate was retained in this search, not that a
machine was mathematically rejected by a complete decision procedure.
"""
import argparse
import base64
from collections import Counter
import hashlib
import json
from pathlib import Path
import zlib

from weighted_codec_v2 import bundle_decode

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def machine(value):
    if type(value) is not int or not 0 <= value < 17**8:
        raise ValueError('Invalid packed census machine')
    slots = []
    for _ in range(8):
        value, digit = divmod(value, 17)
        if digit == 16:
            slots.append('---')
        else:
            slots.append(str(digit // 4) + 'LR'[(digit // 2) % 2] + 'AB'[digit % 2])
    return ''.join(slots[:4]) + '_' + ''.join(slots[4:])


def summarize(cohort, metadata, directory):
    wrapped = json.loads(cohort.read_text())
    if wrapped['encoding'] != 'zlib-base64':
        raise ValueError('Unknown cohort encoding')
    raw = zlib.decompress(base64.b64decode(wrapped['data'], validate=True))
    if hashlib.sha256(raw).hexdigest() != wrapped['uncompressed_sha256']:
        raise ValueError('Cohort payload hash differs')
    machines = [machine(value) for value in json.loads(raw)['rows']]
    text = ''.join(value + '\n' for value in machines).encode()
    meta = json.loads(metadata.read_text())
    if (len(machines) != meta['rows'] or len(set(machines)) != len(machines)
            or hashlib.sha256(text).hexdigest() != meta['machine_text_sha256']):
        raise ValueError('Cohort inventory differs')
    sources = {str(cohort.relative_to(ROOT)): sha(cohort),
               str(metadata.relative_to(ROOT)): sha(metadata),
               'tools/summarize_weighted_full.py': sha(Path(__file__)),
               'tools/weighted_codec_v2.py': sha(ROOT / 'tools/weighted_codec_v2.py')}
    offset, previous, manifest = 0, None, None
    candidates, kinds, pools = set(), Counter(), []
    for registry in sorted(directory.glob('batch*/registry.json')):
        data = json.loads(registry.read_text())
        source = data['source']
        begin, end = source['input_range']
        if not (begin == offset < end <= len(machines)):
            raise ValueError('Snapshot ranges are not a consecutive partition')
        if (source['input_sha256'] != meta['machine_text_sha256']
                or source['input_rows'] != len(machines) or source['ledger_prefix_rows'] != end):
            raise ValueError('Snapshot belongs to a different census input')
        if previous != source.get('previous_registry'):
            raise ValueError('Snapshot hash chain differs')
        if manifest is None:
            manifest = source['campaign_manifest_sha256']
        if source['campaign_manifest_sha256'] != manifest:
            raise ValueError('Snapshot campaign manifests differ')
        rows = []
        for bundle in data['bundles']:
            path = ROOT / bundle['path']
            if sha(path) != bundle['sha256'] or path.stat().st_size != bundle['bytes']:
                raise ValueError('Snapshot bundle bytes differ')
            decoded = bundle_decode(path.read_text())
            if len(decoded) != bundle['rows']:
                raise ValueError('Snapshot bundle row count differs')
            rows.extend(decoded)
        names = [row['machine'] for row in rows]
        counts = Counter(row['kind'] for row in rows)
        if (len(rows) != data['rows'] or dict(counts) != data['kinds']
                or len(set(names)) != len(names) or candidates.intersection(names)):
            raise ValueError('Snapshot candidate counts or uniqueness differ')
        # Export preserves the order of the full input, with misses omitted.
        selected = set(names)
        if [name for name in machines[begin:end] if name in selected] != names:
            raise ValueError('Snapshot candidate order or membership differs')
        candidates.update(names)
        kinds.update(counts)
        previous = {'path': str(registry.relative_to(ROOT)), 'sha256': sha(registry)}
        pools.append({**previous, 'input_range': [begin, end], 'candidate_rows': len(rows)})
        offset = end
    if offset != len(machines):
        raise ValueError('Snapshots do not cover the complete cohort')
    accepted = [name for name in machines if name in candidates]
    remainder = [name for name in machines if name not in candidates]
    digest = lambda rows: hashlib.sha256(''.join(row+'\n' for row in rows).encode()).hexdigest()
    report = {
        'status': 'Complete untrusted candidate search; only separate audited boards establish proofs.',
        'input_rows': len(machines), 'candidate_rows': len(accepted),
        'candidate_kinds': dict(kinds), 'without_retained_candidate': len(remainder),
        'candidate_inventory_sha256': digest(accepted),
        'complement_inventory_sha256': digest(remainder),
        'campaign_manifest_sha256': manifest,
        'final_ledger_sha256': source['ledger_prefix_sha256'],
        'sources_sha256': sources, 'snapshots': pools}
    return report, accepted, remainder


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cohort', type=Path, default=ROOT/'research/weighted-full-cohort-input.json')
    parser.add_argument('--metadata', type=Path, default=ROOT/'research/weighted-full-cohort.json')
    parser.add_argument('--snapshots', type=Path, default=ROOT/'research/weighted-full-snapshots')
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    report, accepted, remainder = summarize(args.cohort.resolve(), args.metadata.resolve(), args.snapshots.resolve())
    if args.check:
        if json.loads(args.report.read_text()) != report:
            raise ValueError('Recorded full-search summary differs')
    else:
        if args.report.exists():
            raise ValueError('Refusing to overwrite a recorded summary; use --check')
        args.report.write_text(json.dumps(report, indent=2, sort_keys=True)+'\n')
    if args.output_dir:
        args.output_dir.mkdir(parents=True, exist_ok=True)
        for filename, rows in [('candidates.txt', accepted), ('without-candidate.txt', remainder)]:
            (args.output_dir/filename).write_text(''.join(row+'\n' for row in rows))
    print(json.dumps({key: report[key] for key in ('input_rows', 'candidate_rows', 'candidate_kinds', 'without_retained_candidate')}))


if __name__ == '__main__':
    main()
