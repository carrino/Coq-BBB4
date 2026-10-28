"""Bounded, one-worker capacity/portfolio search on the exact proof residual.

This is an untrusted producer. Frozen search and proof implementations are
imported unchanged; a separate kernel replay must validate every success.
"""
import argparse
from collections import Counter
import csv
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'build/next-capacity'
PREFIX = ROOT / 'research/next-capacity'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix(path.suffix + '.tmp')
    temp.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
    temp.replace(path)


def prepare(args):
    both = ROOT / 'build/campaign-final/both-unproved-initial-cohort.txt'
    state = ROOT / 'build/campaign-final/state-unproved-initial-cohort.txt'
    queue = ROOT / 'build/campaign-next/queued.tsv'
    old_inputs = [ROOT / ('build/' + name + '/input.txt')
                  for name in ('weighted-followup64', 'weighted-followup512')]
    residual = set(both.read_text().splitlines())
    state_ids = set(state.read_text().splitlines())
    with queue.open() as stream:
        queued = {row['machine'] for row in csv.DictReader(stream, delimiter='\t')}
    prior = set().union(*(set(p.read_text().splitlines()) for p in old_inputs))
    eligible = residual - queued - prior
    ordered = sorted(eligible, key=lambda machine:
                     hashlib.sha256((args.seed + ':' + machine).encode()).hexdigest())
    sample = ordered[:args.rows]
    if not sample or len(sample) != args.rows:
        raise ValueError('Insufficient eligible rows')
    input_path = PREFIX.with_name(PREFIX.name + '-input.txt')
    content = ''.join(machine + '\n' for machine in sample)
    if input_path.exists() and input_path.read_text() != content:
        raise ValueError('Existing input differs; do not overwrite frozen pilot')
    input_path.write_text(content)
    manifest = {
        'scope': 'Untrusted discovery sample; no proof claim or population extrapolation.',
        'selection': {'method': 'First rows ordered by SHA256(seed + colon + machine)',
                      'seed': args.seed, 'rows': args.rows,
                      'both_residual': len(residual), 'state_residual': len(state_ids),
                      'all_queue_ids_excluded': len(queued),
                      'queue_ids_in_both_residual': len(residual & queued),
                      'prior_sample_ids_excluded': len(prior),
                      'eligible_after_exclusions': len(eligible),
                      'sample_state_unproved': len(set(sample) & state_ids),
                      'sample_queue_overlap': len(set(sample) & queued),
                      'sample_prior_overlap': len(set(sample) & prior)},
        'sources_sha256': {str(p.relative_to(ROOT)): sha(p)
                           for p in [both, state, queue, *old_inputs]},
        'input_sha256': sha(input_path),
        'binary_sha256': sha(ROOT / 'build/weighted-v2/dump'),
        'parameters': {'width': 2, 'anchor': 4096, 'fuel': 8193, 'rounds': 33,
                       'graph_orientation_seconds': 0.5, 'node_limit': 2048,
                       'target_lp_seconds': 2, 'wall_width': 16,
                       'machine_wall_seconds': 20, 'address_space_bytes': 1610612736,
                       'workers': 1},
        'solver_sources_sha256': {str(p.relative_to(ROOT)): sha(p) for p in [
            Path(__file__), ROOT / 'tools/weighted_portfolio_search.py',
            ROOT / 'tools/weighted_capacity_search.py', ROOT / 'tools/weighted_search_v2.py',
            ROOT / 'tools/weighted_search.py', ROOT / 'tools/weighted_codec_v2.py',
            ROOT / 'tools/weighted_graphs_v2.ml']}}
    path = PREFIX.with_name(PREFIX.name + '-manifest.json')
    if path.exists() and json.loads(path.read_text()) != manifest:
        raise ValueError('Existing manifest differs')
    write_json(path, manifest)
    print(json.dumps(manifest['selection']), flush=True)


def worker(args):
    resource.setrlimit(resource.RLIMIT_AS, (1610612736, 1610612736))
    import weighted_search_v2 as search
    import weighted_portfolio_search as portfolio
    search.install_budget()
    directory = BASE / f'row-{args.index:04d}'
    directory.mkdir(parents=True, exist_ok=True)
    (directory / 'input.txt').write_text(args.machine + '\n')
    counts, variants = Counter(), []
    command = [str(ROOT / 'build/weighted-v2/dump'), str(directory / 'input.txt'),
               '2', '4096', '8193', '33', '0.5', '2048']
    with (directory / 'graphs.jsonl').open('w') as output:
        subprocess.run(command, stdout=output, stderr=subprocess.PIPE, check=True, timeout=5)
    events = [json.loads(line) for line in (directory / 'graphs.jsonl').read_text().splitlines()]
    if [(e['machine'], e['mirror']) for e in events] != [(args.machine, 0), (args.machine, 1)]:
        raise ValueError('Graph inventory mismatch')
    ordinary = None
    with (directory / 'variants.jsonl').open('w') as output:
        for event in events:
            counts['graph_status_' + event['status']] += 1
            if event['status'] == 'ordinary_candidate':
                ordinary = {'kind': 'ordinary', 'machine': args.machine,
                            'mirror': event['mirror'], 'n': 2, 't': 4096,
                            'fuel': 8193, 'rounds': 33}
            graph = event.get('graph')
            if graph is None:
                continue
            variant = portfolio.solve_targets(graph, 2, 16, counts)
            variants.append(variant)
            counts['graphs_solved'] += 1
            output.write(json.dumps(variant, separators=(',', ':')) + '\n')
            output.flush()
    candidate = ordinary or portfolio.choose(args.machine, variants)
    present_targets = set().union(*(set(v['found']) for v in variants)) if variants else set()
    recurrence_targets = set().union(*(set(k for k, value in v['found'].items()
                                          if value in ('ranked', 'weighted'))
                                     for v in variants)) if variants else set()
    result = {'machine': args.machine, 'counts': dict(counts), 'candidate': candidate,
              'maximum_targets_in_one_variant': max((len(v['found']) for v in variants), default=0),
              'union_targets': sorted(present_targets), 'recurrence_targets': sorted(recurrence_targets),
              'worker_maxrss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
    write_json(directory / 'result.json', result)


def run(args):
    manifest_path = PREFIX.with_name(PREFIX.name + '-manifest.json')
    manifest = json.loads(manifest_path.read_text())
    for group in ('sources_sha256', 'solver_sources_sha256'):
        if any(sha(ROOT / p) != digest for p, digest in manifest[group].items()):
            raise ValueError('Manifest source changed')
    input_path = PREFIX.with_name(PREFIX.name + '-input.txt')
    if sha(input_path) != manifest['input_sha256']:
        raise ValueError('Input changed')
    machines = input_path.read_text().splitlines()
    BASE.mkdir(parents=True, exist_ok=True)
    ledger = BASE / 'results.jsonl'
    rows = [json.loads(line) for line in ledger.read_text().splitlines()] if ledger.exists() else []
    if [row['machine'] for row in rows] != machines[:len(rows)]:
        raise ValueError('Ledger is not an input prefix')
    started = time.monotonic()
    env = dict(os.environ, OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1', MKL_NUM_THREADS='1')
    with ledger.open('a') as output:
        for index, machine in enumerate(machines[len(rows):], len(rows)):
            directory = BASE / f'row-{index:04d}'
            directory.mkdir(parents=True, exist_ok=True)
            begin = time.monotonic()
            with (directory / 'worker.log').open('w') as log:
                process = subprocess.Popen([sys.executable, str(Path(__file__).resolve()),
                    'worker', '--machine', machine, '--index', str(index)], stdout=log,
                    stderr=subprocess.STDOUT, env=env, start_new_session=True)
                try:
                    code = process.wait(timeout=20)
                    status = 'completed' if code == 0 else 'worker_failure'
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    code = process.wait()
                    status = 'machine_wall_timeout'
            row = {'machine': machine, 'index': index, 'status': status, 'returncode': code,
                   'wall_seconds': round(time.monotonic() - begin, 6)}
            if status == 'completed':
                row.update(json.loads((directory / 'result.json').read_text()))
            rows.append(row)
            output.write(json.dumps(row, separators=(',', ':')) + '\n')
            output.flush()
            if (index + 1) % 16 == 0 or row.get('candidate'):
                print(json.dumps({'rows_tested': index + 1,
                    'candidate_count': sum(bool(r.get('candidate')) for r in rows),
                    'last_status': status, 'last_kind': (row.get('candidate') or {}).get('kind'),
                    'run_wall_seconds': round(time.monotonic()-started, 2)}), flush=True)
    from weighted_codec_v2 import pack, bundle_encode
    candidates = [row['candidate'] for row in rows if row.get('candidate')]
    counts = Counter(row['status'] for row in rows)
    for row in rows:
        counts.update(row.get('counts', {}))
    groups = {}
    for candidate in candidates:
        kind = candidate['kind']
        if kind == 'portfolio':
            compact = {'kind': 'weighted', 'machine': candidate['machine'],
                       'choices': candidate['choices'],
                       'portfolio': [pack(v) for v in candidate['variants']]}
        elif kind in ('capacity', 'weighted'):
            compact = pack(candidate['variant'])
            if kind == 'capacity':
                compact['capacities'] = candidate['variant']['capacities']
        else:
            compact = candidate
        groups.setdefault(kind, []).append(compact)
    for kind, compact in groups.items():
        stem = PREFIX.with_name(PREFIX.name + '-' + kind)
        certificate = stem.with_name(stem.name + '-certificates.json')
        certificate.write_text(bundle_encode(compact))
        registry = {'format': 'BBB24 next capacity pilot certificates v1',
                    'status': 'Untrusted witnesses; separate Coq replay and census discharge required.',
                    'source': {'manifest_sha256': sha(manifest_path), 'ledger_sha256': sha(ledger)},
                    'rows': len(compact), 'kinds': dict(Counter(r['kind'] for r in compact)),
                    'bundles': [{'path': str(certificate.relative_to(ROOT)), 'rows': len(compact),
                                 'bytes': certificate.stat().st_size, 'sha256': sha(certificate)}]}
        write_json(stem.with_name(stem.name + '-registry.json'), registry)
        write_json(stem.with_name(stem.name + '-machines.json'),
                   {'rows': [{'machine': row['machine']} for row in compact]})
    report = {'scope': 'Search candidates only; no kernel proof claim.',
              'manifest_sha256': sha(manifest_path), 'ledger_sha256': sha(ledger),
              'input_rows': len(machines), 'actually_tested_rows': len(rows),
              'counts': dict(counts), 'candidate_kinds': dict(Counter(r['kind'] for r in candidates)),
              'incremental_unique_candidate_ids': [r['machine'] for r in candidates],
              'incremental_unique_candidates': len(candidates),
              'incremental_kernel_audited': 0,
              'maximum_worker_rss_kib': max((r.get('worker_maxrss_kib', 0) for r in rows), default=0),
              'summed_machine_wall_seconds': sum(r['wall_seconds'] for r in rows),
              'completed_misses': sum(r['status'] == 'completed' and not r.get('candidate') for r in rows),
              'near_misses_seven_targets': [r['machine'] for r in rows if
                  not r.get('candidate') and r.get('maximum_targets_in_one_variant') == 7]}
    write_json(PREFIX.with_name(PREFIX.name + '-search-report.json'), report)
    print(json.dumps(report), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('prepare', 'run', 'worker'))
    parser.add_argument('--rows', type=int, default=128)
    parser.add_argument('--seed', default='bbb24-next-capacity-2026-10-27')
    parser.add_argument('--machine')
    parser.add_argument('--index', type=int)
    args = parser.parse_args()
    {'prepare': prepare, 'run': run, 'worker': worker}[args.mode](args)
