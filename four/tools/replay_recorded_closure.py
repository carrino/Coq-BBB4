"""Replay a frozen closure board without tracking its redundant TSV ledger.

The compact input and historical report determine the exact ledger. Reconstruct
it only if absent, require its recorded digest, then let the unchanged checker
compile, recursively audit, and compare the complete recorded evidence.
"""
import argparse
import csv
import hashlib
import io
import json
from pathlib import Path
import sys

import check_closure_wave as original


def prepare_ledger(args):
    report = json.loads(args.report.read_text())
    if original.sha(args.input) != report['input_sha256']:
        raise ValueError('Frozen closure input changed')
    module = args.namespace+'.ClosureWaveAll'
    if report['board'] != module+'.board':
        raise ValueError('Recorded closure namespace differs')
    _, rows = original.load_input(args.input)
    if len(rows) != report['checked_families'] or len(rows) != report['census_linked_families']:
        raise ValueError('Recorded closure inventory differs')
    output = io.StringIO()
    writer = csv.DictWriter(output, original.FIELDS+[
        'census_linked', 'bounds_theorem', 'census_theorem'],
        delimiter='\t', lineterminator='\n')
    writer.writeheader()
    writer.writerows({**row, 'census_linked': 'yes',
                      'bounds_theorem': report['small_sound'],
                      'census_theorem': report['discharge_theorem']} for row in rows)
    expected = output.getvalue()
    if hashlib.sha256(expected.encode()).hexdigest() != report['ledger_sha256']:
        raise ValueError('Reconstructed closure ledger differs from the frozen report')
    if args.ledger.exists():
        if args.ledger.read_text() != expected:
            raise ValueError('Existing closure ledger differs from the frozen report')
        return None
    args.ledger.parent.mkdir(parents=True, exist_ok=True)
    args.ledger.write_text(expected)
    return args.ledger


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--build-dir', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--ledger', type=Path, required=True)
    parser.add_argument('--namespace', required=True)
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--timeout', type=int, default=1200)
    args = parser.parse_args()
    if not args.namespace.isidentifier() or args.timeout < 1:
        raise ValueError('Invalid namespace or timeout')
    created = prepare_ledger(args)
    sys.argv = [original.__file__, '--input', str(args.input),
                '--build-dir', str(args.build_dir), '--report', str(args.report),
                '--ledger', str(args.ledger), '--namespace', args.namespace,
                '--timeout', str(args.timeout)]
    if args.resume:
        sys.argv.append('--resume')
    try:
        original.main()
    except BaseException:
        if created is not None:
            created.unlink(missing_ok=True)
        raise


if __name__ == '__main__':
    main()
