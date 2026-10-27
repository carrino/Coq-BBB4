"""Bound each untrusted affine proposal search by CPU time, preserving misses.

A profiling timer survives exec and terminates only the current C subprocess.
This avoids scheduler-dependent short wall deadlines and isolates pathological
internal searches. CPU-budget and other resource failures remain undecided.
"""
import argparse
import csv
import hashlib
import io
import json
import math
import resource
import shutil
import signal
import subprocess
import time
from collections import Counter
from pathlib import Path

import affine_sweep

HEADER = ['machine', 'status', 'anchor', 'k0', 'meta_a', 'meta_b', 'kmin', 'nrules', 'qh', 'score']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def cpu_used():
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    return usage.ru_utime+usage.ru_stime


def run_one(binary, machine, certdir, steps, tape, cpu_seconds):
    def limit():
        signal.signal(signal.SIGPROF, signal.SIG_DFL)
        signal.setitimer(signal.ITIMER_PROF, cpu_seconds)
        hard = math.ceil(cpu_seconds)+2
        resource.setrlimit(resource.RLIMIT_CPU, (hard, hard))
    start = time.monotonic()
    cpu = cpu_used()
    try:
        result = subprocess.run([str(binary.resolve()), '--max-steps', str(steps),
                                 '--tape-cells', str(tape), '--why', '--cert-dir', str(certdir.resolve()), '-'],
                                input=machine+'\n', text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, preexec_fn=limit, timeout=120)
        code = result.returncode
        if code == -signal.SIGPROF or code == -signal.SIGXCPU:
            status = 'cpu_budget'
        elif code:
            status = 'process_failure'
        else:
            rows = list(csv.reader(io.StringIO(result.stdout)))
            if len(rows) != 2 or rows[0] != HEADER or len(rows[1]) < 10 or rows[1][0] != machine:
                raise ValueError('Malformed or mismatched affine search result')
            row = rows[1]
            if row[1] not in {'irules', 'undecided'}:
                raise ValueError('Unknown affine search verdict')
            if row[1] == 'irules':
                cert = (certdir/(machine+'.cert')).read_text().splitlines()
                if cert.count('machine '+machine) != 1 or not cert or cert[-1] != 'end':
                    raise ValueError('Missing, incomplete or mismatched certificate')
            return row, row[1], code, time.monotonic()-start, cpu_used()-cpu
    except subprocess.TimeoutExpired:
        code, status = None, 'wall_guard'
    row = [machine, 'undecided', '0', '0', '0', '0', '0', '0', '?', '0', status]
    return row, status, code, time.monotonic()-start, cpu_used()-cpu


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--irules', type=Path, required=True)
    parser.add_argument('--prefix-search', type=Path)
    parser.add_argument('--cpu-seconds', type=float, default=0.25)
    parser.add_argument('--steps', type=int, default=4096)
    parser.add_argument('--tape-cells', type=int, default=65536)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--resume', action='store_true')
    args = parser.parse_args()
    if not math.isfinite(args.cpu_seconds) or args.cpu_seconds <= 0 or args.steps <= 0 or args.tape_cells < 2*args.steps+1:
        raise ValueError('Invalid CPU, step or tape budget')
    machines = affine_sweep.read_input(args.input)
    args.output.mkdir(parents=True, exist_ok=True)
    certdir = args.output/'certs'
    certdir.mkdir(exist_ok=True)
    metadata = {'input_sha256': sha(args.input), 'binary_sha256': sha(args.irules),
                'cpu_seconds': args.cpu_seconds, 'steps': args.steps, 'tape_cells': args.tape_cells,
                'source_sha256': sha(Path(__file__)),
                'prefix_search_sha256': sha(args.prefix_search/'search.csv') if args.prefix_search else None}
    manifest = args.output/'process.json'
    output = args.output/'search.csv'
    timing = args.output/'timing.tsv'
    if manifest.exists():
        if not args.resume or json.loads(manifest.read_text()) != metadata:
            raise ValueError('Existing sweep or changed resume parameters')
        completed = affine_sweep.read_output(output, machines)
        # Discard an interrupted final output fragment before appending.
        buf = io.StringIO(newline=''); writer = csv.writer(buf, lineterminator='\n')
        writer.writerow(HEADER); writer.writerows(completed)
        output.write_text(buf.getvalue())
    else:
        if output.exists() or timing.exists():
            raise ValueError('Unrecognized existing sweep output')
        completed = affine_sweep.read_output(args.prefix_search/'search.csv', machines) if args.prefix_search else []
        for row in completed:
            if row[1] == 'irules':
                shutil.copyfile(args.prefix_search/'certs'/(row[0]+'.cert'), certdir/(row[0]+'.cert'))
        manifest.write_text(json.dumps(metadata, indent=2)+'\n')
        with output.open('w', newline='') as out:
            writer = csv.writer(out, lineterminator='\n'); writer.writerow(HEADER); writer.writerows(completed)
        timing.write_text('machine\tstatus\treturncode\twall_seconds\tcpu_seconds\n')
    start = time.monotonic()
    count = Counter()
    with output.open('a', newline='') as out, timing.open('a', newline='') as times:
        writer = csv.writer(out, lineterminator='\n')
        twriter = csv.writer(times, delimiter='\t', lineterminator='\n')
        for index, machine in enumerate(machines[len(completed):], len(completed)+1):
            row, status, code, wall, cpu = run_one(args.irules, machine, certdir,
                                                   args.steps, args.tape_cells, args.cpu_seconds)
            writer.writerow(row); out.flush()
            twriter.writerow([machine, status, code, f'{wall:.6f}', f'{cpu:.6f}']); times.flush()
            count[status] += 1
            if index % 256 == 0:
                print(json.dumps({'processed': index, 'total': len(machines),
                                  'this_run': dict(count), 'wall_seconds': round(time.monotonic()-start, 2)}), flush=True)
    if sha(args.input) != metadata['input_sha256'] or sha(args.irules) != metadata['binary_sha256']:
        raise ValueError('Search input or binary changed during execution')
    rows = affine_sweep.read_output(output, machines)
    candidates = [r[0] for r in rows if r[1] == 'irules']
    misses = [r[0] for r in rows if r[1] == 'undecided']
    (args.output/'candidates.txt').write_text(''.join(m+'\n' for m in candidates))
    (args.output/'not-accepted.txt').write_text(''.join(m+'\n' for m in misses))
    report = {'status': 'Complete untrusted CPU-bounded search', 'input_rows': len(machines),
              'candidate_rows': len(candidates), 'not_accepted_rows': len(misses),
              'prefix_rows_reused': len(completed), 'this_run_statuses': dict(count),
              'this_run_wall_seconds': time.monotonic()-start, 'parameters': metadata,
              'search_csv_sha256': sha(output), 'timing_tsv_sha256': sha(timing),
              'candidate_sha256': sha(args.output/'candidates.txt'),
              'not_accepted_sha256': sha(args.output/'not-accepted.txt'),
              'kernel_checked_rows': 0, 'census_linked_rows': 0,
              'proof_accounting': 'Every candidate still requires extracted replay and a separately audited Coq bundle.'}
    args.report.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: report[k] for k in ['input_rows', 'candidate_rows', 'not_accepted_rows', 'this_run_statuses']}))


if __name__ == '__main__':
    main()
