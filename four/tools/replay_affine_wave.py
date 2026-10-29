"""Rebuild a recorded affine wave without tracking its redundant TSV ledger.

The compact certificate bundle and audited report are the frozen inputs. When
the expected ledger is absent, reconstruct it deterministically, then invoke
the original checker for compilation, recursive kernel audit, and exact report
comparison. Existing ledgers are never replaced. New research batches still
use check_affine_wave.py --refresh to create their first audited report.
"""
import argparse
import csv
import io
import json
from pathlib import Path
import re
import resource
import sys

import check_affine_wave as original


def prepare_ledger(args):
    report_path = args.report_prefix.with_suffix('.json')
    ledger_path = args.report_prefix.with_suffix('.tsv')
    report = json.loads(report_path.read_text())
    if report['input_sha256'] != original.sha(args.input) or report['source_sha256'] != original.source_hashes():
        raise ValueError('Frozen input or checker sources changed')
    module = f'BBB24AffineWave.{args.name}.All'
    if report['module'] != module:
        raise ValueError('Recorded namespace differs')
    data, paths = original.load_bundle(args.input, original.BUILD/args.name/'certs')
    if len(paths) != report['checked_families'] or len(paths) != report['census_linked_families']:
        raise ValueError('Recorded inventory differs')
    buffer = io.StringIO(newline='')
    writer = csv.DictWriter(buffer, fieldnames=['machine', 'proof_index', 'certificate_sha256', 'status',
        'state_bound', 'instruction_bound', 'census_linked', 'theorem'], delimiter='\t', lineterminator='\n')
    writer.writeheader()
    writer.writerows({'machine': path.stem, 'proof_index': index, 'certificate_sha256': original.sha(path),
        'status': 'coq_checked', 'state_bound': data['bound'], 'instruction_bound': data['bound'],
        'census_linked': 'yes', 'theorem': report['discharge_theorem']} for index, path in enumerate(paths))
    expected = buffer.getvalue()
    if ledger_path.exists():
        if ledger_path.read_text() != expected:
            raise ValueError('Existing ledger differs from the frozen inputs')
        return None
    # This is the expected ledger of the historical audited run. The wrapper
    # reports fresh validation only after the complete original checker passes.
    ledger_path.write_text(expected)
    return ledger_path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--name', required=True)
    parser.add_argument('--report-prefix', type=Path, required=True)
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--timeout', type=int, default=1800)
    args = parser.parse_args()
    if not re.fullmatch(r'[A-Z][A-Za-z0-9_]*', args.name) or args.timeout < 1:
        raise ValueError('Invalid name or timeout')
    # Large unchanged aggregate count proofs need more than the usual 8 MiB
    # process stack. This setting applies only to this replay and its children.
    soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
    required = 64*1024*1024
    if soft != resource.RLIM_INFINITY and soft < required:
        if hard != resource.RLIM_INFINITY and hard < required:
            raise ValueError('Affine aggregate replay needs a 64 MiB process stack limit')
        resource.setrlimit(resource.RLIMIT_STACK, (required, hard))
    created = prepare_ledger(args)
    sys.argv = [original.__file__, '--input', str(args.input), '--name', args.name,
                '--report-prefix', str(args.report_prefix), '--timeout', str(args.timeout)]
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
