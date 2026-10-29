"""Freeze a stopped affine search, explicitly deferring its unprocessed suffix.

Run only after its search worker has stopped. Deferred rows are unresolved,
never certificates; including them in the snapshot makes the subsequent full
replay residual retain every machine in the original cohort.
"""
import argparse
import csv
import hashlib
import io
import json
import re
from pathlib import Path

import affine_sweep


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--reason', default='deferred_budget')
    args = parser.parse_args()
    if not re.fullmatch(r'deferred_[a-z_]+', args.reason):
        raise ValueError('Expected an explicit deferred_* reason')
    if args.report.exists():
        raise ValueError('A search report already exists; refusing to overwrite it')
    machines = affine_sweep.read_input(args.input)
    output = args.output/'search.csv'
    original_hash = sha(output)
    rows = affine_sweep.read_output(output, machines)
    processed = len(rows)
    parameters = json.loads((args.output/'process.json').read_text())
    if parameters['input_sha256'] != sha(args.input):
        raise ValueError('Search cohort changed')
    candidates = [r[0] for r in rows if r[1] == 'irules']
    for machine in candidates:
        text = (args.output/'certs'/(machine+'.cert')).read_text().splitlines()
        if text.count('machine '+machine) != 1 or not text or text[-1] != 'end':
            raise ValueError('Missing, incomplete or mismatched certificate')
    for machine in machines[processed:]:
        rows.append([machine, 'undecided', '0', '0', '0', '0', '0', '0', '?', '0', args.reason])
    buffer = io.StringIO(newline='')
    writer = csv.writer(buffer, lineterminator='\n')
    writer.writerow(['machine', 'status', 'anchor', 'k0', 'meta_a', 'meta_b', 'kmin', 'nrules', 'qh', 'score'])
    writer.writerows(rows)
    if sha(output) != original_hash:
        raise ValueError('Search is still writing output; stop it before finalizing')
    output.write_text(buffer.getvalue())
    candidate_file = args.output/'candidates.txt'
    missed_file = args.output/'not-accepted.txt'
    candidate_file.write_text(''.join(m+'\n' for m in candidates))
    missed_file.write_text(''.join(r[0]+'\n' for r in rows if r[1] == 'undecided'))
    report = {'status': 'Untrusted stopped-search checkpoint; unprocessed suffix explicitly deferred',
              'input_rows': len(machines), 'processed_rows': processed,
              'deferred_rows': len(machines)-processed, 'candidate_rows': len(candidates),
              'processed_undecided_rows': processed-len(candidates),
              'not_accepted_rows': len(machines)-len(candidates), 'deferred_reason': args.reason,
              'parameters': parameters, 'original_prefix_csv_sha256': original_hash,
              'search_csv_sha256': sha(output), 'candidate_sha256': sha(candidate_file),
              'not_accepted_sha256': sha(missed_file), 'finalizer_source_sha256': sha(Path(__file__)),
              'kernel_checked_rows': 0, 'census_linked_rows': 0,
              'proof_accounting': 'Deferred and failed rows remain unresolved. Only separately audited Coq bundles discharge families.'}
    args.report.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: report[k] for k in ['processed_rows', 'deferred_rows', 'candidate_rows', 'not_accepted_rows']}))


if __name__ == '__main__':
    main()
