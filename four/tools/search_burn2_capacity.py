"""Bounded, untrusted width refinement of the 54 capacity near misses.

The frozen first-round graphs remain read-only. Their target witnesses are
combined with new width-three/four graphs; only separate Coq replay can turn
these candidates into proofs.
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
BASE = ROOT / 'build/burn2-capacity'
PREFIX = ROOT / 'research/burn2-capacity'
OLD = ROOT / 'build/next-capacity'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(obj, indent=2, sort_keys=True) + '\n'
    if path.exists() and path.read_text() != text and path.parent == PREFIX.parent:
        raise ValueError('Refusing to overwrite published evidence: ' + str(path))
    path.write_text(text)


def selected():
    rows = [json.loads(line) for line in (OLD / 'results.jsonl').read_text().splitlines()]
    near = [row for row in rows if not row.get('candidate') and
            row.get('maximum_targets_in_one_variant') == 7]
    residual = set((ROOT / 'build/next-burndown/both-remaining.txt').read_text().splitlines())
    with (ROOT / 'build/next-burndown/queued.tsv').open() as stream:
        queue = {row['machine'] for row in csv.DictReader(stream, delimiter='\t')}
    assert len(near) == 54
    assert all(row['machine'] in residual - queue for row in near)
    return near


def worker(args):
    resource.setrlimit(resource.RLIMIT_AS, (2147483648, 2147483648))
    import weighted_search_v2 as search
    import weighted_portfolio_search as portfolio
    search.install_budget()
    old = selected()[args.index]
    machine = old['machine']
    directory = BASE / f'row-{args.index:03d}'
    directory.mkdir(parents=True, exist_ok=True)
    input_path = directory / 'input.txt'
    input_path.write_text(machine + '\n')
    old_path = OLD / f"row-{old['index']:04d}" / 'variants.jsonl'
    variants = [json.loads(line) for line in old_path.read_text().splitlines()]
    for variant in variants:
        variant['found'] = {int(k): v for k, v in variant['found'].items()}
    counts, events = Counter(), []
    candidate = portfolio.choose(machine, variants)
    assert candidate is None
    for width in (3, 4):
        graph_path = directory / f'graphs-width{width}.jsonl'
        with graph_path.open('w') as out:
            subprocess.run([str(ROOT / 'build/weighted-v2/dump'), str(input_path),
                            str(width), '4096', '8193', '65', '2', '4096'],
                           stdout=out, stderr=subprocess.PIPE, check=True, timeout=8)
        graph_events = [json.loads(line) for line in graph_path.read_text().splitlines()]
        assert [(e['machine'], e['mirror']) for e in graph_events] == [(machine, 0), (machine, 1)]
        for event in graph_events:
            events.append({k: v for k, v in event.items() if k != 'graph'})
            counts['graph_status_' + event['status']] += 1
            if event['status'] == 'ordinary_candidate':
                candidate = {'kind': 'ordinary', 'machine': machine,
                             'mirror': event['mirror'], 'n': width, 't': 4096,
                             'fuel': 8193, 'rounds': 65}
                break
            if event.get('graph'):
                variants.append(portfolio.solve_targets(event['graph'], 3, 32, counts))
                candidate = portfolio.choose(machine, variants)
                if candidate:
                    break
        if candidate:
            break
    (directory / 'variants.jsonl').write_text(''.join(json.dumps(v, separators=(',', ':')) + '\n'
                                                   for v in variants))
    save(directory / 'result.json', {
        'machine': machine, 'old_index': old['index'], 'old_variants_sha256': sha(old_path),
        'candidate': candidate, 'counts': dict(counts), 'events': events,
        'maximum_targets_in_one_variant': max(len(v['found']) for v in variants),
        'recurrence_targets': sorted(set().union(*(set(k for k, value in v['found'].items()
                                                if value in ('ranked', 'weighted'))
                                               for v in variants))),
        'worker_maxrss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss})


def main(args):
    rows = selected()
    BASE.mkdir(parents=True, exist_ok=True)
    sources = [Path(__file__), ROOT / 'tools/weighted_portfolio_search.py',
               ROOT / 'tools/weighted_capacity_search.py', ROOT / 'tools/weighted_search_v2.py',
               ROOT / 'tools/weighted_search.py', ROOT / 'tools/weighted_codec_v2.py',
               ROOT / 'tools/weighted_graphs_v2.ml', ROOT / 'build/weighted-v2/dump',
               OLD / 'results.jsonl', ROOT / 'build/next-burndown/both-remaining.txt',
               ROOT / 'build/next-burndown/queued.tsv']
    manifest = {'scope': 'Untrusted targeted width refinement; no proof claim.',
                'machines': [row['machine'] for row in rows],
                'sources_sha256': {str(p.relative_to(ROOT)): sha(p) for p in sources},
                'parameters': {'widths': [3, 4], 'anchor': 4096, 'fuel': 8193, 'rounds': 65,
                               'graph_seconds': 2, 'node_limit': 4096, 'target_lp_seconds': 3,
                               'wall_width': 32, 'machine_seconds': 90, 'workers': 1,
                               'address_space_bytes': 2147483648}}
    save(PREFIX.with_name(PREFIX.name + '-manifest.json'), manifest)
    ledger = BASE / 'results.jsonl'
    results = [json.loads(line) for line in ledger.read_text().splitlines()] if ledger.exists() else []
    assert [r['machine'] for r in results] == [r['machine'] for r in rows[:len(results)]]
    env = dict(os.environ, OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1', MKL_NUM_THREADS='1')
    with ledger.open('a') as out:
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
            out.write(json.dumps(result, separators=(',', ':')) + '\n'); out.flush()
            print(json.dumps({'rows': len(results), 'candidates': sum(bool(r.get('candidate')) for r in results),
                              'last_status': status, 'last_seconds': result['wall_seconds']}), flush=True)
    from weighted_codec_v2 import pack, bundle_encode
    groups = {}
    for result in results:
        candidate = result.get('candidate')
        if not candidate:
            continue
        kind = candidate['kind']
        if kind == 'portfolio':
            compact = {'kind': 'weighted', 'machine': candidate['machine'],
                       'choices': candidate['choices'], 'portfolio': [pack(v) for v in candidate['variants']]}
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
        text = bundle_encode(compact)
        if certificate.exists() and certificate.read_text() != text:
            raise ValueError('Existing compact certificates differ')
        certificate.write_text(text)
        save(stem.with_name(stem.name + '-registry.json'), {
            'format': 'BBB24 targeted capacity refinement v1', 'rows': len(compact),
            'status': 'Untrusted witnesses; separate Coq replay required.',
            'bundles': [{'path': str(certificate.relative_to(ROOT)), 'rows': len(compact),
                         'bytes': certificate.stat().st_size, 'sha256': sha(certificate)}]})
        save(stem.with_name(stem.name + '-machines.json'),
             {'rows': [{'machine': r['machine']} for r in compact]})
    assert all(sha(ROOT / path) == digest for path, digest in manifest['sources_sha256'].items())
    save(PREFIX.with_name(PREFIX.name + '-search-report.json'), {
        'scope': 'Search candidates only; no kernel proof claim.',
        'rows': len(results), 'ledger_sha256': sha(ledger),
        'manifest_sha256': sha(PREFIX.with_name(PREFIX.name + '-manifest.json')),
        'statuses': dict(Counter(r['status'] for r in results)),
        'candidate_kinds': {kind: len(compact) for kind, compact in groups.items()},
        'summed_wall_seconds': sum(r['wall_seconds'] for r in results),
        'per_machine': [{k:v for k,v in r.items() if k not in ('candidate',)} |
                        {'candidate_kind': (r.get('candidate') or {}).get('kind')} for r in results]})


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('run', 'worker'))
    parser.add_argument('--index', type=int)
    args = parser.parse_args()
    (worker if args.mode == 'worker' else main)(args)
