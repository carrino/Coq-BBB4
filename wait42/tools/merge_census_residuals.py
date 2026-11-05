#!/usr/bin/env python3
"""Merge UNTRUSTED search worklists, never Coq coverage certificates.

Without --verify-ledgers, conservatively retain every unresolved identity.
With two exactly equal ledger family sets, intersect unknown identities while
retaining every pending identity. Missing residual rows are never interpreted
as resolved unless both ledger sets were checked. Pending families outside a
popped-node ledger remain pending. No proof TSV is accepted or auto-subtracted.

Example:
  python3 wait42/tools/merge_census_residuals.py --left LEFT.residual.tsv \
    --right RIGHT.residual.tsv --verify-ledgers LEFT.ledger.tsv RIGHT.ledger.tsv \
    --output /tmp/merged-census

Verification uses a temporary SQLite database with a 32 MiB page cache and
file-backed temporary storage, rather than keeping millions of keys in RAM.
Residual dictionaries are capped by --max-residual-rows (default 500,000 each).
Output: PREFIX.residual.tsv and PREFIX.summary.json; provenance columns retain
left/right missing and pending statuses. Identity is exact (machine, TNF ptr).
"""
import argparse
from collections import Counter
import csv
import hashlib
import itertools
import json
from pathlib import Path
import re
import sqlite3
import sys
import tempfile

MACHINE = re.compile(r'(?:---|[01][LR][ABCD]){2}(?:_(?:---|[01][LR][ABCD]){2}){3}')
STATUSES = {'unknown': 'unknown', 'unknown_edge': 'unknown_edge', 'pending': 'pending'}
LEDGER_KINDS = set(STATUSES) | {
    'halt_completion', 'cycle_hash_candidate', 'translated_cycle_candidate', 'tail_ngram_candidate'
}


def fingerprint(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return {'bytes': Path(path).stat().st_size, 'sha256': digest.hexdigest()}


def rows(path):
    """Require rectangular TSVs, unique headers, and canonical identities."""
    with Path(path).open(newline='') as stream:
        reader = csv.DictReader(stream, delimiter='\t')
        fields = reader.fieldnames
        if not fields or len(fields) != len(set(fields)) or not {'kind', 'machine', 'ptr'} <= set(fields):
            raise ValueError(f'{path}: required unique columns: kind, machine, ptr')
        for number, row in enumerate(reader, 2):
            if None in row or any(value is None for value in row.values()):
                raise ValueError(f'{path}:{number}: malformed TSV row width')
            machine, ptr = row['machine'], row['ptr']
            if MACHINE.fullmatch(machine) is None or ptr not in ('1', '2', '3', '4') or not row['kind']:
                raise ValueError(f'{path}:{number}: invalid machine, ptr, or kind')
            yield machine + '\t' + ptr, row


def read_residual(path, maximum):
    result = {}
    for identity, row in rows(path):
        if row['kind'] not in STATUSES:
            raise ValueError(f'{path}: invalid residual kind {row["kind"]!r}')
        if identity in result:
            raise ValueError(f'{path}: duplicate residual identity {identity!r}')
        if len(result) >= maximum:
            raise ValueError(f'{path}: residual row cap {maximum} exceeded')
        result[identity] = STATUSES[row['kind']]
    return result


def verify_ledgers(paths, residuals, temp_dir=None):
    """Exact equality, duplicate detection, and residual/ledger consistency."""
    with tempfile.TemporaryDirectory(prefix='census-family-merge-', dir=temp_dir) as tmp:
        connection = sqlite3.connect(str(Path(tmp) / 'families.sqlite3'))
        try:
            connection.execute('PRAGMA journal_mode=OFF')
            connection.execute('PRAGMA synchronous=OFF')
            connection.execute('PRAGMA cache_size=-32768')
            connection.execute('PRAGMA temp_store=FILE')
            counts, missing_pending = [], []
            for table, path, residual in zip(('left_families', 'right_families'), paths, residuals):
                connection.execute(f'CREATE TABLE {table} (identity TEXT PRIMARY KEY) WITHOUT ROWID')
                seen_residual = set()
                batch, count = [], 0
                for identity, row in rows(path):
                    ledger_kind = row['kind']
                    if ledger_kind not in LEDGER_KINDS:
                        raise ValueError(f'{path}: unsupported ledger kind {ledger_kind!r}')
                    if ledger_kind in STATUSES:
                        if residual.get(identity) != ledger_kind:
                            raise ValueError(f'{path}: unresolved ledger row absent or inconsistent in residual: {identity!r}')
                    elif identity in residual:
                        raise ValueError(f'{path}: residual identity has resolved ledger kind: {identity!r}')
                    if identity in residual:
                        seen_residual.add(identity)
                    batch.append((identity,))
                    count += 1
                    if len(batch) == 4096:
                        try:
                            connection.executemany(f'INSERT INTO {table} VALUES (?)', batch)
                        except sqlite3.IntegrityError as error:
                            raise ValueError(f'{path}: duplicate ledger identity') from error
                        batch.clear()
                try:
                    connection.executemany(f'INSERT INTO {table} VALUES (?)', batch)
                except sqlite3.IntegrityError as error:
                    raise ValueError(f'{path}: duplicate ledger identity') from error
                absent = residual.keys() - seen_residual
                if any(residual[identity] != 'pending' for identity in absent):
                    raise ValueError(f'{path}: unknown residual identity missing from ledger')
                missing_pending.append(len(absent))
                counts.append(count)
                connection.commit()
            if counts[0] != counts[1]:
                raise ValueError(f'ledger family universes differ: row counts {counts}')
            left = connection.execute('SELECT identity FROM left_families ORDER BY identity')
            right = connection.execute('SELECT identity FROM right_families ORDER BY identity')
            for first, second in itertools.zip_longest(left, right):
                if first != second:
                    raise ValueError(f'ledger family universes differ: {first!r} versus {second!r}')
            return {'equal_listed_family_sets': True, 'rows_per_ledger': counts,
                    'duplicates': 0, 'pending_residual_identities_outside_ledgers': missing_pending,
                    'algorithm': 'exact primary-key uniqueness and streamed equality of sorted SQLite identities',
                    'sqlite_page_cache_mib': 32,
                    'completeness_proved': False}
        finally:
            connection.close()


def merge(left, right, verified):
    pending = {identity for residual in (left, right)
               for identity, status in residual.items() if status == 'pending'}
    identities = (left.keys() & right.keys()) if verified else (left.keys() | right.keys())
    identities |= pending
    for identity in sorted(identities):
        ls, rs = left.get(identity, 'missing'), right.get(identity, 'missing')
        kind = 'pending' if 'pending' in (ls, rs) else (
            'unknown_edge' if 'unknown_edge' in (ls, rs) else 'unknown')
        machine, ptr = identity.split('\t')
        yield {'kind': kind, 'machine': machine, 'ptr': ptr,
               'left_status': ls, 'right_status': rs}


def execute(left_path, right_path, output_prefix, ledger_paths=None,
            maximum=500000, temp_dir=None):
    inputs = [Path(left_path), Path(right_path)]
    if ledger_paths:
        inputs += [Path(path) for path in ledger_paths]
    prefix = Path(output_prefix)
    residual_path = Path(str(prefix) + '.residual.tsv')
    summary_path = Path(str(prefix) + '.summary.json')
    if any(path.resolve() in {residual_path.resolve(), summary_path.resolve()} for path in inputs):
        raise ValueError('outputs must not overwrite inputs')
    before = {str(path): fingerprint(path) for path in inputs}
    left, right = (read_residual(path, maximum) for path in inputs[:2])
    verification = verify_ledgers(inputs[2:], (left, right), temp_dir) if ledger_paths else None
    output = merge(left, right, verification is not None)
    after = {str(path): fingerprint(path) for path in inputs}
    if before != after:
        raise ValueError('input files changed while merging')
    prefix.parent.mkdir(parents=True, exist_ok=True)
    fields = ['kind', 'machine', 'ptr', 'left_status', 'right_status']
    counts, missing_counts, output_rows = Counter(), Counter(), 0
    with tempfile.NamedTemporaryFile(mode='w', newline='', dir=prefix.parent,
                                     prefix=prefix.name + '-', delete=False) as stream:
        temporary = Path(stream.name)
        writer = csv.DictWriter(stream, fields, delimiter='\t', lineterminator='\n')
        writer.writeheader()
        for row in output:
            writer.writerow(row)
            output_rows += 1
            counts[row['kind']] += 1
            for side in ('left', 'right'):
                missing_counts[side] += row[side + '_status'] == 'missing'
    temporary.replace(residual_path)
    summary = {'schema_version': 1, 'trust': 'UNTRUSTED search worklist; no Coq coverage or proof claim',
               'coverage_proved': False, 'universal_coverage_credit': 0, 'kernel_credit': 0,
               'accepted_proofs': 0, 'identity': 'exact machine TAB TNF ptr',
               'mode': 'verified_unknown_intersection_preserving_all_pending' if verification else 'conservative_unresolved_union_without_ledger_verification',
               'intersection_authorized_by_equal_listed_ledger_sets': verification is not None,
               'ledger_verification': verification,
               'input_counts': [dict(Counter(left.values())), dict(Counter(right.values()))],
               'input_rows': [len(left), len(right)],
               'input_pending_rows': [sum(s == 'pending' for s in residual.values()) for residual in (left, right)],
               'output_rows': output_rows, 'output_counts': dict(counts),
               'unknown_rows': counts['unknown'] + counts['unknown_edge'], 'pending_rows': counts['pending'],
               'input_pending_retained': True,
               'output_missing_side_counts': {side: missing_counts[side] for side in ('left', 'right')},
               'residual_row_cap_per_input': maximum,
               'input_fingerprints': before,
               'output': {'path': str(residual_path), **fingerprint(residual_path)},
               'notes': ['Missing residual status is preserved in provenance columns.',
                         'Pending identities are retained even when missing from the other residual.',
                         'Equal listed ledger families do not prove complete enumeration or universal coverage.',
                         'No external proof list is read or automatically subtracted.']}
    summary_path.write_text(json.dumps(summary, indent=2) + '\n')
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--left', type=Path, required=True)
    parser.add_argument('--right', type=Path, required=True)
    parser.add_argument('--verify-ledgers', type=Path, nargs=2, metavar=('LEFT_LEDGER', 'RIGHT_LEDGER'))
    parser.add_argument('--output', type=Path, required=True, help='output prefix')
    parser.add_argument('--temp-dir', type=Path)
    parser.add_argument('--max-residual-rows', type=int, default=500000)
    args = parser.parse_args()
    if not 1 <= args.max_residual_rows <= 1000000:
        parser.error('--max-residual-rows must be 1..1000000')
    try:
        summary = execute(args.left, args.right, args.output, args.verify_ledgers,
                          args.max_residual_rows, args.temp_dir)
    except (ValueError, OSError, sqlite3.Error) as error:
        print(f'error: {error}', file=sys.stderr)
        return 2
    print(json.dumps({'summary': str(args.output) + '.summary.json',
                      'rows': summary['output_rows'], 'unknown': summary['unknown_rows'],
                      'pending': summary['pending_rows'], 'coverage_proved': False}))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
