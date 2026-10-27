"""Untrusted single-machine retry of a graph rejected only by the export cap."""
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'build/burn2-capacity-cap8192'
PREFIX = ROOT / 'research/burn2-capacity-cap8192'
MACHINE = '1LB0LB---3RA_3RB2RA3LB1RA'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def publish(path, value):
    text = json.dumps(value, indent=2, sort_keys=True) + '\n'
    if path.exists() and path.read_text() != text:
        raise ValueError('Refusing to overwrite frozen report: ' + str(path))
    path.write_text(text)


def main():
    if PREFIX.with_name(PREFIX.name + '-search-report.json').exists():
        raise ValueError('This bounded experiment is already frozen; preserve its runtime evidence')
    resource.setrlimit(resource.RLIMIT_AS, (2147483648, 2147483648))
    for variable in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
        os.environ[variable] = '1'
    import weighted_search_v2 as search
    import weighted_portfolio_search as portfolio
    from weighted_codec_v2 import pack, bundle_encode
    search.install_budget()
    OUTPUT.mkdir(parents=True, exist_ok=True)
    input_path = OUTPUT / 'input.txt'
    input_path.write_text(MACHINE + '\n')
    old_variants = ROOT / 'build/burn2-capacity/row-043/variants.jsonl'
    old_result = ROOT / 'build/burn2-capacity/row-043/result.json'
    prior = json.loads(old_result.read_text())
    assert prior['machine'] == MACHINE and not prior['candidate']
    variants = [json.loads(line) for line in old_variants.read_text().splitlines()]
    for variant in variants:
        variant['found'] = {int(k): v for k, v in variant['found'].items()}
    sources = [Path(__file__), ROOT / 'tools/weighted_portfolio_search.py',
               ROOT / 'tools/weighted_capacity_search.py', ROOT / 'tools/weighted_search_v2.py',
               ROOT / 'tools/weighted_search.py', ROOT / 'tools/weighted_codec_v2.py',
               ROOT / 'build/weighted-v2/dump', old_variants, old_result]
    hashes = {str(path.relative_to(ROOT)): sha(path) for path in sources}
    started = time.monotonic()
    graph_path = OUTPUT / 'graphs.jsonl'
    with graph_path.open('w') as stream:
        subprocess.run([str(ROOT / 'build/weighted-v2/dump'), str(input_path),
                        '4', '4096', '8193', '65', '2', '8192'],
                       stdout=stream, stderr=subprocess.PIPE, check=True, timeout=8)
    events = [json.loads(line) for line in graph_path.read_text().splitlines()]
    assert [(event['machine'], event['mirror']) for event in events] == [(MACHINE, 0), (MACHINE, 1)]
    counts, ordinary = Counter(), None
    for event in events:
        counts['graph_status_' + event['status']] += 1
        if event['status'] == 'ordinary_candidate':
            ordinary = {'kind': 'ordinary', 'machine': MACHINE, 'mirror': event['mirror'],
                        'n': 4, 't': 4096, 'fuel': 8193, 'rounds': 65}
        if event.get('graph'):
            variants.append(portfolio.solve_targets(event['graph'], 3, 32, counts))
    candidate = ordinary or portfolio.choose(MACHINE, variants)
    (OUTPUT / 'variants.jsonl').write_text(''.join(json.dumps(v, separators=(',', ':')) + '\n'
                                                for v in variants))
    (OUTPUT / 'candidate.json').write_text(json.dumps(candidate, indent=2) + '\n')
    if candidate:
        kind = candidate['kind']
        if kind == 'portfolio':
            compact = {'kind': 'weighted', 'machine': MACHINE, 'choices': candidate['choices'],
                       'portfolio': [pack(v) for v in candidate['variants']]}
        elif kind == 'ordinary':
            compact = candidate
        else:
            compact = pack(candidate['variant'])
            if kind == 'capacity':
                compact['capacities'] = candidate['variant']['capacities']
        certificate = PREFIX.with_name(PREFIX.name + '-certificates.json')
        text = bundle_encode([compact])
        if certificate.exists() and certificate.read_text() != text:
            raise ValueError('Existing certificates differ')
        certificate.write_text(text)
        publish(PREFIX.with_name(PREFIX.name + '-registry.json'), {
            'format': 'BBB24 capacity export-cap retry v1', 'rows': 1,
            'status': 'Untrusted candidate; separate Coq proof required.',
            'bundles': [{'path': str(certificate.relative_to(ROOT)), 'rows': 1,
                         'bytes': certificate.stat().st_size, 'sha256': sha(certificate)}]})
    assert all(sha(ROOT / path) == digest for path, digest in hashes.items())
    report = {'scope': 'Untrusted single-machine experiment; no proof claim.', 'machine': MACHINE,
              'sources_sha256': hashes, 'parameters': {'width': 4, 'anchor': 4096, 'fuel': 8193,
              'rounds': 65, 'native_seconds': 2, 'node_cap': 8192, 'target_lp_seconds': 3,
              'wall_width': 32, 'address_space_bytes': 2147483648},
              'candidate_kind': candidate['kind'] if candidate else None, 'counts': dict(counts),
              'graph_sha256': sha(graph_path), 'wall_seconds': round(time.monotonic() - started, 3),
              'events': [{k: v for k, v in event.items() if k != 'graph'} for event in events]}
    publish(PREFIX.with_name(PREFIX.name + '-search-report.json'), report)
    print(json.dumps({key: report[key] for key in ('machine', 'candidate_kind', 'counts', 'wall_seconds')}))


if __name__ == '__main__':
    main()
