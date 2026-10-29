"""Replay a complete affine search with the extracted checker (not proof evidence).

The residual includes all search misses and every non-true replay verdict. Named
Coq proof bundles, checked separately, are the only source of certified counts.
"""
import argparse
import csv
import hashlib
import json
import math
import subprocess
import time
from collections import Counter
from pathlib import Path

import affine_sweep


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(path, candidates, certdir):
    with path.open(newline='') as source:
        reader = csv.DictReader(source, delimiter='\t')
        if reader.fieldnames != ['certificate', 'machine', 'status', 'seconds']:
            raise ValueError('Unexpected extracted replay ledger header')
        rows = list(reader)
    if len(rows) != len(candidates):
        raise ValueError('Incomplete extracted replay ledger')
    allowed = {'replay_true', 'replay_false', 'unsupported', 'timeout',
               'stack_overflow', 'invalid_certificate', 'anchor_exceeds_bound'}
    for row, machine in zip(rows, candidates):
        if row['machine'] != machine:
            raise ValueError('Replay machine identity/order mismatch')
        if Path(row['certificate']).resolve() != (certdir / (machine+'.cert')).resolve():
            raise ValueError('Replay certificate path mismatch')
        seconds = float(row['seconds'])
        if row['status'] not in allowed or not math.isfinite(seconds) or seconds < 0:
            raise ValueError('Invalid replay verdict or timing')
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--search', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--probe', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--bound', type=int, default=4096)
    parser.add_argument('--cfuel', type=int, default=4096)
    parser.add_argument('--fuel', type=int, default=8192)
    parser.add_argument('--timeout', type=float, default=30)
    parser.add_argument('--reuse', action='store_true')
    args = parser.parse_args()
    if min(args.bound, args.cfuel, args.fuel) <= 0 or args.timeout <= 0 or not math.isfinite(args.timeout):
        raise ValueError('Replay budgets must be positive and finite')
    machines = affine_sweep.read_input(args.input)
    search = affine_sweep.read_output(args.search/'search.csv', machines)
    if len(search) != len(machines):
        raise ValueError('Replay sweep requires a complete search')
    candidates = [r[0] for r in search if r[1] == 'irules']
    args.output.mkdir(parents=True, exist_ok=True)
    certdir = args.search/'certs'
    paths = args.output/'input.txt'
    paths.write_text(''.join(str(certdir/(m+'.cert'))+'\n' for m in candidates))
    provenance = {'input_sha256': sha(args.input),
                  'search_csv_sha256': sha(args.search/'search.csv'),
                  'probe_binary_sha256': sha(args.probe),
                  'probe_input_sha256': sha(paths),
                  'bound': args.bound, 'cfuel': args.cfuel, 'fuel': args.fuel,
                  'timeout': args.timeout}
    manifest = args.output/'process.json'
    ledger = args.output/'replay.tsv'
    if args.reuse:
        if json.loads(manifest.read_text()) != provenance:
            raise ValueError('Reuse parameters or input changed')
        elapsed = None
    else:
        if ledger.exists():
            raise ValueError('Replay output exists; use --reuse or a new directory')
        manifest.write_text(json.dumps(provenance, indent=2)+'\n')
        start = time.monotonic()
        with ledger.open('w') as out, (args.output/'replay.log').open('w') as err:
            subprocess.run([str(args.probe.resolve()), str(args.bound), str(args.cfuel),
                            str(args.fuel), str(args.timeout), str(paths)],
                           stdout=out, stderr=err, check=True)
        elapsed = time.monotonic()-start
    rows = validate(ledger, candidates, certdir)
    accepted = {r['machine'] for r in rows if r['status'] == 'replay_true'}
    if sha(args.input) != provenance['input_sha256'] or sha(args.search/'search.csv') != provenance['search_csv_sha256']:
        raise ValueError('Search input/output changed during replay')
    accepted_path = args.output/'accepted.txt'
    remaining_path = args.output/'not-accepted.txt'
    accepted_path.write_text(''.join(m+'\n' for m in machines if m in accepted))
    remaining_path.write_text(''.join(m+'\n' for m in machines if m not in accepted))
    report = {'status': 'Complete extracted replay; not kernel proof evidence',
              'input_rows': len(machines), 'search_candidates': len(candidates),
              'search_misses': len(machines)-len(candidates),
              'replay_statuses': dict(sorted(Counter(r['status'] for r in rows).items())),
              'accepted_rows': len(accepted), 'not_accepted_rows': len(machines)-len(accepted),
              'elapsed_seconds': elapsed, 'row_seconds': sum(float(r['seconds']) for r in rows),
              'replay_tsv_sha256': sha(ledger), 'accepted_sha256': sha(accepted_path),
              'not_accepted_sha256': sha(remaining_path), 'parameters': provenance,
              'collector_source_sha256': sha(Path(__file__)),
              'kernel_checked_rows': 0, 'census_linked_rows': 0,
              'proof_accounting': 'Only separately audited Coq bundles discharge families.'}
    args.report.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: report[k] for k in ['input_rows', 'search_candidates', 'replay_statuses',
                                          'accepted_rows', 'not_accepted_rows']}))


if __name__ == '__main__':
    main()
