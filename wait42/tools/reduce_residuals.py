#!/usr/bin/env python3
"""Remove exact family identities listed in reviewed proof indexes.

This is bookkeeping, not a Coq checker. Run the corresponding proof target
before assigning proof credit. Pending subtree roots are always retained.
The required input hash binds the reduction to a particular census snapshot.
"""
import argparse
import csv
import hashlib
import io
import json
import re
from pathlib import Path

SLOT = r'(?:[01][LR][ABCD]|---)'
MACHINE = re.compile(rf'{SLOT}{{2}}(?:_{SLOT}{{2}}){{3}}\Z')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def identity(row):
    machine, pointer = row.get('machine', ''), row.get('ptr', '')
    if not MACHINE.fullmatch(machine) or pointer not in {'1', '2', '3', '4'}:
        raise ValueError('Malformed machine or unused-state pointer')
    return machine, pointer


def read_rows(path, required):
    data = path.read_bytes()
    with io.StringIO(data.decode('utf-8'), newline='') as f:
        reader = csv.DictReader(f, delimiter='\t', strict=True)
        fields = reader.fieldnames
        if (not fields or len(set(fields)) != len(fields) or not required <= set(fields)
                or any('\n' in field or '\r' in field for field in fields)):
            raise ValueError(f'Invalid columns: {path}')
        try:
            rows = list(reader)
        except csv.Error as exc:
            raise ValueError(f'Malformed TSV: {path}: {exc}') from exc
    if any(None in row or any(v is None for v in row.values()) for row in rows):
        raise ValueError(f'Ragged row: {path}')
    if any('\n' in v or '\r' in v for row in rows for v in row.values()):
        raise ValueError(f'Multiline fields are not allowed in a residual index: {path}')
    return fields, rows, hashlib.sha256(data).hexdigest()


def reduce(source, expected_hash, indexes, output):
    if output.resolve() in {source.resolve(), *(p.resolve() for p in indexes)}:
        raise ValueError('Output must differ from all inputs')
    fields, rows, actual_hash = read_rows(source, {'kind', 'machine', 'ptr'})
    if actual_hash != expected_hash:
        raise ValueError('Source SHA256 does not match the requested snapshot')
    by_id = {}
    for row in rows:
        key = identity(row)
        if row['kind'] not in {'unknown', 'pending'}:
            raise ValueError('Residual kind must be unknown or pending')
        if key in by_id:
            raise ValueError('Duplicate residual family identity')
        by_id[key] = row
    proven, provenance = {}, []
    for index in indexes:
        _, proofs, index_hash = read_rows(index, {'machine', 'ptr', 'theorem'})
        local = set()
        for proof in proofs:
            key = identity(proof)
            theorem = proof['theorem']
            if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', theorem):
                raise ValueError('Invalid theorem name in proof index')
            if key not in by_id:
                raise ValueError('Proof index contains a family absent from the source snapshot')
            if (key, theorem) in local:
                raise ValueError('Duplicate proof-index entry')
            local.add((key, theorem))
            proven.setdefault(key, set()).add(theorem)
        provenance.append({'index': index.name, 'sha256': index_hash, 'rows': len(proofs)})
    retained = [r for r in rows if r['kind'] == 'pending' or identity(r) not in proven]
    removed = [r for r in rows if r['kind'] == 'unknown' and identity(r) in proven]
    # Validate everything before replacing any output.
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open('w', newline='') as f:
        writer = csv.DictWriter(f, fields, delimiter='\t', lineterminator='\n')
        writer.writeheader()
        writer.writerows(retained)
    return {
        'trust': 'exact identity bookkeeping; proof targets must be checked separately',
        'source_sha256': expected_hash, 'source_rows': len(rows),
        'proof_indexes': provenance, 'unique_indexed_families': len(proven),
        'removed': len(removed), 'remaining': len(retained),
        'pending_retained': sum(r['kind'] == 'pending' for r in retained),
        'output_sha256': digest(output), 'formal_universal_coverage': False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--source-sha256', required=True)
    parser.add_argument('--proof-index', type=Path, action='append', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.resolve() in {args.input.resolve(), *(p.resolve() for p in args.proof_index)}:
        parser.error('Output must differ from all inputs')
    try:
        result = reduce(args.input, args.source_sha256, args.proof_index, args.output)
    except (ValueError, OSError) as exc:
        parser.error(str(exc))
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
