"""Package extracted replay candidates, excluding explicitly supplied inventories.

The self-contained bundle is untrusted input to check_affine_wave.py. Exclusions
are selection bookkeeping; this tool never treats them as proof evidence.
"""
import argparse
import base64
import csv
import hashlib
import json
import zlib
from pathlib import Path

from generate_pipeline_examples import codes


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    data = json.loads(path.read_text())
    if isinstance(data, dict) and data.get('encoding') == 'zlib-base64':
        raw = zlib.decompress(base64.b64decode(data['data'], validate=True))
        if hashlib.sha256(raw).hexdigest() != data['uncompressed_sha256']:
            raise ValueError('Compressed inventory hash mismatch')
        data = json.loads(raw)
    return data


def inventory(path):
    if path.suffix == '.tsv':
        with path.open(newline='') as source:
            rows = list(csv.DictReader(source, delimiter='\t'))
        result = [r['machine'] for r in rows]
    else:
        data = read_json(path)
        if 'certificates' in data:
            result = list(data['certificates'])
        else:
            result = [r['machine'] if isinstance(r, dict) else r[0] for r in data['rows']]
    if len(set(result)) != len(result):
        raise ValueError('Duplicate machine in selection inventory')
    for machine in result:
        codes(machine)
    return set(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--replay', type=Path, action='append', required=True)
    parser.add_argument('--exclude', type=Path, action='append', default=[])
    parser.add_argument('--cohort', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--bound', type=int, default=4096)
    parser.add_argument('--cfuel', type=int, default=4096)
    parser.add_argument('--fuel', type=int, default=8192)
    parser.add_argument('--limit', type=int)
    args = parser.parse_args()
    if not 1 <= min(args.bound, args.cfuel, args.fuel) <= max(args.bound, args.cfuel, args.fuel) <= 10000000:
        raise ValueError('Invalid checker budget')
    if args.limit is not None and args.limit <= 0:
        raise ValueError('Invalid selection limit')
    cohort = args.cohort.read_text().splitlines()
    if not cohort or len(set(cohort)) != len(cohort):
        raise ValueError('Cohort must be nonempty and unique')
    for machine in cohort:
        codes(machine)
    cohort = set(cohort)
    excluded = set()
    for path in args.exclude:
        excluded.update(inventory(path))
    selected = {}
    for path in args.replay:
        with path.open(newline='') as source:
            reader = csv.DictReader(source, delimiter='\t')
            if not {'machine', 'certificate', 'status'} <= set(reader.fieldnames or []):
                raise ValueError('Missing replay identity/status columns')
            for row in reader:
                machine = row['machine']
                if row['status'] != 'replay_true' or machine in excluded:
                    continue
                codes(machine)
                if machine not in cohort:
                    raise ValueError('Replay success outside declared cohort')
                cert = Path(row['certificate'])
                if cert.stem != machine:
                    raise ValueError('Certificate filename identity mismatch')
                text = cert.read_text()
                if text.splitlines().count('machine '+machine) != 1:
                    raise ValueError('Certificate header identity mismatch')
                selected.setdefault(machine, text)
    machines = sorted(selected, key=lambda m: hashlib.sha256(m.encode()).digest())
    if args.limit is not None:
        machines = machines[:args.limit]
    if not machines:
        raise ValueError('Empty proof candidate selection')
    provenance = {'description': 'Hash-ordered extracted replay successes, excluding the declared inventories. '
                     'First supplied successful certificate wins when a machine has multiple trials. '
                     'Every selected certificate still requires Coq proof and census-membership checks.',
                  'cohort_sha256': sha(args.cohort),
                  'replay_inputs_sha256': {str(p): sha(p) for p in args.replay},
                  'excluded_inventory_sha256': {str(p): sha(p) for p in args.exclude},
                  'builder_source_sha256': sha(Path(__file__)),
                  'eligible_unique_machines': len(selected), 'selection_limit': args.limit}
    data = {'bound': args.bound, 'cfuel': args.cfuel, 'fuel': args.fuel,
            'provenance': provenance, 'certificates': {m: selected[m] for m in machines}}
    raw = json.dumps(data, sort_keys=True, separators=(',', ':')).encode()
    wrapper = {'encoding': 'zlib-base64', 'uncompressed_sha256': hashlib.sha256(raw).hexdigest(),
               'data': base64.b64encode(zlib.compress(raw, 9)).decode()}
    args.output.write_text(json.dumps(wrapper, sort_keys=True)+'\n')
    print(json.dumps({'selected': len(machines), 'excluded_inventory_union': len(excluded),
                      'bytes': args.output.stat().st_size, 'sha256': sha(args.output)}))


if __name__ == '__main__':
    main()
