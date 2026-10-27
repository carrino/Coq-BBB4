"""Untrusted state-capacity pilot on 32 fixed ordinary weighted-state misses."""
import argparse
from collections import Counter
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
BASE = ROOT / 'build/burn2-state-capacity'
PREFIX = ROOT / 'research/burn2-state-capacity'
SELECTION = ROOT / 'build/burn2-state/state-capacity-pilot-input.json'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(value, indent=2, sort_keys=True) + '\n'
    if path.exists() and path.read_text() != text and path.parent == PREFIX.parent:
        raise ValueError('Existing published input differs')
    path.write_text(text)


def worker(args):
    resource.setrlimit(resource.RLIMIT_AS, (2147483648, 2147483648))
    import weighted_search_v2 as search
    import weighted_portfolio_search as portfolio
    search.install_budget()
    row = json.loads(SELECTION.read_text())[args.index]
    graph_specs = {(item['path'], item['mirror']) for item in row['graphs']}
    events = {}
    for filename in sorted({item['path'] for item in row['graphs']}):
        with (ROOT.parent / filename).open() as stream:
            for line in stream:
                event = json.loads(line)
                if event['machine'] == row['machine'] and (filename, event['mirror']) in graph_specs:
                    events[event['mirror']] = event
    assert set(events) == {item['mirror'] for item in row['graphs']}
    counts, attempts, candidate = Counter(), [], None
    for mirror, event in sorted(events.items()):
        graph = event['graph']
        assert graph['machine'] == row['machine'] and graph['mirror'] == mirror
        variant = portfolio.solve_targets(graph, 3, 32, counts)
        present_states = {node[0] for node in graph['nodes']}
        choices, selected = [], set()
        for state in range(2):
            options = [target for target, kind in variant['found'].items()
                       if target // 4 == state and kind in ('ranked', 'weighted', 'capacity')]
            if state not in present_states:
                choices.append(0)
            elif options:
                target = min(options, key=lambda target:
                             ({'ranked': 0, 'weighted': 1, 'capacity': 2}[variant['found'][target]], target))
                selected.add(target)
                choices.append(target % 4)
            else:
                break
        attempts.append({'mirror': mirror, 'nodes': len(graph['nodes']), 'found': variant['found'],
                         'state_choices': choices})
        if len(choices) == 2:
            variant['certs'] = {key: value for key, value in variant['certs'].items() if int(key) in selected}
            variant['capacities'] = {key: value for key, value in variant['capacities'].items()
                                     if int(key) in selected}
            candidate = {'variant': variant, 'state_choices': choices}
            break
    directory = BASE / f'row-{args.index:03d}'
    save(directory / 'result.json', {'machine': row['machine'], 'candidate': candidate,
        'counts': dict(counts), 'attempts': attempts,
        'worker_maxrss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss})


def main(args):
    rows = json.loads(SELECTION.read_text())
    assert len(rows) == 32 and len({row['machine'] for row in rows}) == 32
    BASE.mkdir(parents=True, exist_ok=True)
    sources = [Path(__file__), SELECTION, ROOT / 'tools/weighted_portfolio_search.py',
        ROOT / 'tools/weighted_capacity_search.py', ROOT / 'tools/weighted_search_v2.py',
        ROOT / 'tools/weighted_search.py', ROOT / 'tools/weighted_codec_v2.py']
    sources += [ROOT.parent / filename for filename in sorted({g['path'] for row in rows for g in row['graphs']})]
    manifest = {'scope': 'Untrusted state-only capacity discovery; no proof claim.',
                'rows': rows, 'sources_sha256': {str(p.relative_to(ROOT)): sha(p) for p in sources},
                'parameters': {'workers': 1, 'lp_target_seconds': 3, 'wall_width': 32,
                    'machine_seconds': 90, 'address_space_bytes': 2147483648}}
    save(PREFIX.with_name(PREFIX.name + '-manifest.json'), manifest)
    ledger = BASE / 'results.jsonl'
    results = [json.loads(line) for line in ledger.read_text().splitlines()] if ledger.exists() else []
    assert [row['machine'] for row in results] == [row['machine'] for row in rows[:len(results)]]
    env = dict(os.environ, OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1', MKL_NUM_THREADS='1')
    with ledger.open('a') as stream:
        for index in range(len(results), len(rows)):
            directory = BASE / f'row-{index:03d}'
            directory.mkdir(parents=True, exist_ok=True)
            started = time.monotonic()
            with (directory / 'worker.log').open('w') as log:
                process = subprocess.Popen([sys.executable, str(Path(__file__).resolve()),
                    'worker', '--index', str(index)], stdout=log, stderr=subprocess.STDOUT,
                    env=env, start_new_session=True)
                try:
                    code = process.wait(timeout=90)
                    status = 'completed' if code == 0 else 'worker_failure'
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    code = process.wait()
                    status = 'machine_timeout'
            result = {'machine': rows[index]['machine'], 'index': index, 'status': status,
                      'returncode': code, 'wall_seconds': round(time.monotonic() - started, 3)}
            if status == 'completed':
                result.update(json.loads((directory / 'result.json').read_text()))
            results.append(result)
            stream.write(json.dumps(result, separators=(',', ':')) + '\n'); stream.flush()
            print(json.dumps({'rows': len(results), 'candidates': sum(bool(r.get('candidate')) for r in results),
                              'last_status': status}), flush=True)
    from weighted_codec_v2 import pack, bundle_encode
    compact = []
    for result in results:
        candidate = result.get('candidate')
        if candidate:
            row = pack(candidate['variant'])
            row['capacities'] = candidate['variant']['capacities']
            row['state_choices'] = candidate['state_choices']
            compact.append(row)
    if compact:
        certificate = PREFIX.with_name(PREFIX.name + '-certificates.json')
        text = bundle_encode(compact)
        if certificate.exists() and certificate.read_text() != text:
            raise ValueError('Existing compact state capacities differ')
        certificate.write_text(text)
        save(PREFIX.with_name(PREFIX.name + '-input.json'), {'rows': len(compact),
             'scope': 'Untrusted state-only certificates; no instruction claim.',
             'bundles': [{'path': str(certificate.relative_to(ROOT)), 'rows': len(compact),
                          'sha256': sha(certificate), 'bytes': certificate.stat().st_size}]})
    assert all(sha(ROOT / name) == digest for name, digest in manifest['sources_sha256'].items())
    save(PREFIX.with_name(PREFIX.name + '-search-report.json'), {
        'scope': 'Untrusted state-only search candidates; no proof claim.',
        'manifest_sha256': sha(PREFIX.with_name(PREFIX.name + '-manifest.json')),
        'ledger_sha256': sha(ledger), 'rows': len(results), 'candidates': len(compact),
        'statuses': dict(Counter(row['status'] for row in results)),
        'candidate_ids': [row['machine'] for row in compact],
        'summed_wall_seconds': sum(row['wall_seconds'] for row in results),
        'per_machine': [{key: value for key, value in row.items() if key != 'candidate'} for row in results]})


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('run', 'worker'))
    parser.add_argument('--index', type=int)
    args = parser.parse_args()
    (worker if args.mode == 'worker' else main)(args)
