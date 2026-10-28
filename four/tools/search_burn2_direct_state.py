"""Untrusted rankings for edges avoiding an entire state, with original labels.

Only edge selection differs from the existing exact weighted/capacity search.
Every node label and transition is preserved. No instruction-bound claim is
made; a dedicated direct-state Coq checker must validate every candidate.
"""
from collections import Counter
from fractions import Fraction
import hashlib
import json
from math import lcm
import os
from pathlib import Path
import resource
import time

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'build/burn2-direct-state'
PREFIX = ROOT / 'research/burn2-direct-state'
INPUT = ROOT / 'build/burn2-state/state-capacity-pilot-input.json'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def edges_avoiding(graph, state):
    return [(i, j) for i, adjacent in enumerate(graph['edges']) for j in adjacent
            if graph['nodes'][i][0] != state and graph['nodes'][j][0] != state]


def solve(graph, state, binary, diagnostics):
    import weighted_search_v2 as search
    nodes, edges, components = graph['nodes'], edges_avoiding(graph, state), []
    for _ in range(64):
        if not edges:
            return components
        groups = search.shared.scc(len(nodes), edges)
        cross = {(int(groups[i]), int(groups[j])) for i, j in edges if groups[i] != groups[j]}
        ranks = {int(group): 0 for group in groups}
        for _ in range(len(ranks)):
            changed = False
            for left, right in cross:
                value = ranks[right] + 1
                if ranks[left] < value:
                    ranks[left] = value
                    changed = True
            if not changed:
                break
        components.append({'kind': 'rank', 'rank': [ranks[int(group)] for group in groups]})
        edges = [(i, j) for i, j in edges if groups[i] == groups[j]]
        if not edges:
            return components
        buckets = {}
        for edge in edges:
            buckets.setdefault(int(groups[edge[0]]), []).append(edge)
        progress, remaining = False, []
        for group, local in sorted(buckets.items()):
            for kind in ('linear', 'w') if binary else ('linear',):
                # exact_lp uses this explicit edge set; its legacy target argument
                # is unused by both its inequalities and the proposal LP.
                answer = search.exact_lp(graph, 4 * state, local, kind, diagnostics)
                if answer is None:
                    continue
                rest, values = answer
                components.append({'kind': kind, 'values': values,
                                   'active': sorted({v for edge in local for v in edge})})
                progress, local = True, rest
                break
            remaining += local
        if not progress:
            return None
        edges = remaining
    diagnostics['lex_round_budget'] += 1
    return None


def capacity(graph, state):
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import coo_matrix
    import weighted_search_v2 as search
    nodes, edges = graph['nodes'], edges_avoiding(graph, state)
    if not edges:
        return {'K': 1, 'weights': [0] * 12, 'bias': [0] * len(nodes)}
    rows, _ = search.inequalities(graph, edges, 'linear')
    directions = [graph['trans'][4 * nodes[i][0] + nodes[i][2]][1] for i, j in edges]
    rr, cc, vv = [], [], []
    for index, row in enumerate(rows):
        for column, value in row.items():
            if value:
                rr.append(index); cc.append(column); vv.append(value)
    size = 12 + len(nodes)
    matrix = coo_matrix((vv, (rr, cc)), shape=(len(edges), size)).tocsr()
    bounds = [(0, 0) if i in (0, 4, 8) else (0, None) for i in range(size)]
    result = linprog(np.array([1.] * 12 + [1. / len(nodes)] * len(nodes)),
                    A_ub=matrix, b_ub=np.array(directions), bounds=bounds, method='highs')
    if not result.success:
        return None
    for limit in (1000, 100000, 10000000):
        fractions = [Fraction(float(x)).limit_denominator(limit) for x in result.x]
        scale = lcm(*(x.denominator for x in fractions))
        values = [int(x * scale) for x in fractions]
        if min(values, default=0) < 0 or max([scale, *values]).bit_length() > 4096 or any(values[i] for i in (0, 4, 8)):
            continue
        if all(sum(values[k] * value for k, value in row.items()) <= scale * direction
               for row, direction in zip(rows, directions)):
            return {'K': scale, 'weights': values[:12], 'bias': values[12:]}
    return None


def main():
    report_path = PREFIX.with_name(PREFIX.name + '-search-report.json')
    if report_path.exists():
        raise ValueError('Experiment already frozen; preserve its evidence')
    resource.setrlimit(resource.RLIMIT_AS, (2147483648, 2147483648))
    for name in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
        os.environ[name] = '1'
    import weighted_search_v2 as search
    from weighted_codec_v2 import pack, bundle_encode
    search.install_budget()
    rows = json.loads(INPUT.read_text())
    assert len(rows) == 32
    BASE.mkdir(parents=True, exist_ok=True)
    graph_files = sorted({graph['path'] for row in rows for graph in row['graphs']})
    sources = [Path(__file__), INPUT, ROOT / 'tools/weighted_search_v2.py',
               ROOT / 'tools/weighted_search.py', ROOT.parent / 'tools/multisymbol/weighted_certificates.py']
    sources += [ROOT.parent / filename for filename in graph_files]
    hashes = {str(path.relative_to(ROOT.parent)): sha(path) for path in sources}
    ledger, candidates, all_counts = [], [], Counter()
    for row in rows:
        started = time.monotonic()
        events = {}
        for filename in sorted({graph['path'] for graph in row['graphs']}):
            with (ROOT.parent / filename).open() as stream:
                for line in stream:
                    event = json.loads(line)
                    if event['machine'] == row['machine']:
                        events[event['mirror']] = event
        attempts, candidate = [], None
        for mirror, event in sorted(events.items()):
            graph, certs, capacities, kinds = event['graph'], {}, {}, []
            original = json.dumps(graph, sort_keys=True)
            for state in range(2):
                try:
                    with search.budget(3):
                        components = solve(graph, state, False, all_counts)
                        cap = None
                        kind = 'additive'
                        if components is None:
                            cap = capacity(graph, state)
                            if cap is not None:
                                components = solve(graph, state, True, all_counts)
                                kind = 'capacity_binary'
                        if components is None:
                            kinds.append('failed'); break
                        certs[str(4 * state)] = {'k': 0, 'guards': [], 'inside': [], 'components': components}
                        if cap is not None and any(c['kind'] == 'w' for c in components):
                            capacities[str(4 * state)] = cap
                        else:
                            kind = 'additive'
                        kinds.append(kind)
                except search.BudgetExpired:
                    all_counts['target_timeouts'] += 1
                    kinds.append('timeout'); break
            assert json.dumps(graph, sort_keys=True) == original
            attempts.append({'mirror': mirror, 'nodes': len(graph['nodes']), 'state_methods': kinds})
            if len(certs) == 2:
                candidate = {'graph': graph, 'certs': certs, 'capacities': capacities,
                             'state_methods': kinds, 'direct_state_targets': True}
                candidates.append(candidate)
                break
        result = {'machine': row['machine'], 'attempts': attempts,
                  'candidate': candidate is not None, 'seconds': round(time.monotonic() - started, 3)}
        ledger.append(result)
        with (BASE / 'results.jsonl').open('a') as stream:
            stream.write(json.dumps(result) + '\n')
        print(json.dumps({'rows': len(ledger), 'candidates': len(candidates), 'last': result}), flush=True)
    compact = []
    for candidate in candidates:
        item = pack(candidate)
        item['capacities'] = candidate['capacities']
        item['state_methods'] = candidate['state_methods']
        item['direct_state_targets'] = True
        compact.append(item)
    (BASE / 'candidates.jsonl').write_text(''.join(json.dumps(row, separators=(',', ':')) + '\n' for row in candidates))
    if compact:
        certificate = PREFIX.with_name(PREFIX.name + '-certificates.json')
        certificate.write_text(bundle_encode(compact))
        PREFIX.with_name(PREFIX.name + '-input.json').write_text(json.dumps({
            'scope': 'Untrusted direct-state target certificates; no instruction claim.', 'rows': len(compact),
            'bundles': [{'path': str(certificate.relative_to(ROOT)), 'rows': len(compact), 'sha256': sha(certificate)}]}, indent=2) + '\n')
    assert all(sha(ROOT.parent / filename) == digest for filename, digest in hashes.items())
    report = {'scope': 'Untrusted direct-state search; dedicated Coq replay required.',
              'sources_sha256': hashes, 'rows': len(rows), 'candidates': len(compact),
              'candidate_methods': dict(Counter('capacity_binary' if row['capacities'] else 'additive' for row in candidates)),
              'component_types': dict(Counter(component['kind'] for row in candidates
                  for cert in row['certs'].values() for component in cert['components'])),
              'guarded_binary_attempted': False, 'counts': dict(all_counts), 'per_machine': ledger}
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')


if __name__ == '__main__':
    main()
