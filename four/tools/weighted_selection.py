"""Reference-only scheduling selections; deferred rows are never proof claims.

Original candidate bundles stay immutable. A selected registry retains exact
bundle indices plus a complete audited/queued deferral ledger. Every retained
row still passes the original Coq checker independently.
"""
import base64
import csv
import hashlib
import json
import zlib
from collections import Counter
from pathlib import Path

from generate_pipeline_examples import codes
from weighted_codec_v2 import bundle_decode

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def pinned(item):
    path = ROOT/item['path']
    if sha(path) != item['sha256']:
        raise ValueError('Changed selection dependency: '+item['path'])
    return path


def assignment(path):
    data = json.loads(path.read_text())
    statuses, hashes = {}, {str(path.resolve().relative_to(ROOT)): sha(path)}
    for source in data['sources']:
        if source['status'] not in ('audited', 'queued'):
            raise ValueError('Unknown scheduling assignment status')
        if source.get('scope') != 'both' or (source['status'] == 'audited' and source.get('report') is None):
            raise ValueError('Only explicit BOTH assignments may defer direct proofs')
        for key in ('report', 'inventory'):
            item = source.get(key)
            if item is None:
                continue
            pinned(item)
            hashes[item['path']] = item['sha256']
        item = source['inventory']
        text = pinned(item).read_text()
        if item['format'] == 'tsv':
            rows = [row['machine'] for row in csv.DictReader(text.splitlines(), delimiter='\t')]
        else:
            inventory = json.loads(text)
            if inventory.get('encoding') == 'zlib-base64':
                raw = zlib.decompress(base64.b64decode(inventory['data'], validate=True))
                if hashlib.sha256(raw).hexdigest() != inventory['uncompressed_sha256']:
                    raise ValueError('Compressed assignment inventory hash differs')
                inventory = json.loads(raw)
            if item['format'] == 'json_columns':
                rows = [row[0] for row in inventory['rows']]
            elif item['format'] == 'json_rows':
                rows = [row['machine'] for row in inventory['rows']]
            else:
                raise ValueError('Unknown assignment inventory format')
        if not rows or len(rows) != source['rows'] or len(set(rows)) != len(rows):
            raise ValueError('Assignment inventory count/uniqueness differs')
        for machine in rows:
            codes(machine)
            if source['status'] == 'audited' or machine not in statuses:
                statuses[machine] = source['status']
    return statuses, hashes


def build(original_path, assignment_path):
    source = json.loads(original_path.read_text())
    statuses, hashes = assignment(assignment_path)
    full, kept, deferred, bundles = [], [], [], []
    for item in source['bundles']:
        path = pinned(item)
        rows = bundle_decode(path.read_text())
        if len(rows) != item['rows']:
            raise ValueError('Original bundle row count differs')
        indices = []
        for index, row in enumerate(rows):
            machine = row['machine']; codes(machine); full.append(machine)
            if machine in statuses:
                deferred.append({'machine': machine, 'status': statuses[machine]})
            else:
                indices.append(index); kept.append(row)
        if indices:
            bundles.append({**item, 'rows': len(indices),
                            'source_rows': len(rows), 'keep': indices})
        hashes[item['path']] = item['sha256']
    if len(full) != source['rows'] or len(set(full)) != len(full):
        raise ValueError('Original candidate inventory is inconsistent')
    original = {'path': str(original_path.resolve().relative_to(ROOT)), 'sha256': sha(original_path)}
    assigned = {'path': str(assignment_path.resolve().relative_to(ROOT)), 'sha256': sha(assignment_path)}
    hashes[original['path']] = original['sha256']
    data = {'format': 'BBB24 selected weighted certificates v1',
            'status': 'Retained rows require independent kernel replay. Deferrals are scheduling only.',
            'source': source['source'], 'rows': len(kept),
            'kinds': dict(Counter(row['kind'] for row in kept)), 'bundles': bundles,
            'selection': {'original_registry': original, 'assignment': assigned,
                          'original_rows': len(full), 'retained_rows': len(kept),
                          'deferred_rows': len(deferred), 'deferred': deferred}}
    return data, hashes


def freeze(original_path, assignment_path, output):
    data, _ = build(original_path, assignment_path)
    text = json.dumps(data, indent=2, sort_keys=True)+'\n'
    output.parent.mkdir(parents=True, exist_ok=True)
    if output.exists():
        if output.read_text() != text:
            raise ValueError('Frozen selection changed')
    else:
        temp = output.with_suffix('.json.tmp'); temp.write_text(text); temp.replace(output)
    return data


def load(path):
    data = json.loads(path.read_text())
    selected = data['selection']
    expected, hashes = build(pinned(selected['original_registry']), pinned(selected['assignment']))
    if data != expected:
        raise ValueError('Selection does not exactly partition the original candidates')
    by_hash = {entry['sha256']: entry for entry in data['bundles']}
    if len(by_hash) != len(data['bundles']):
        raise ValueError('Ambiguous selected bundle identity')

    def decode(text):
        digest = hashlib.sha256(text.encode()).hexdigest()
        if digest not in by_hash:
            raise ValueError('Unexpected selected bundle')
        item = by_hash[digest]; rows = bundle_decode(text)
        if len(rows) != item['source_rows']:
            raise ValueError('Selected source bundle row count differs')
        return [rows[index] for index in item['keep']]

    return data, hashes, decode
