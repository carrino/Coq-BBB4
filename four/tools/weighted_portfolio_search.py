"""Find untrusted weighted, capacity, or multi-graph recurrence witnesses.

Every target is explored independently, allowing different closed graphs or
orientations to certify different instructions. Portfolio output requires an
actual recurrence witness for all eight instructions: an absent instruction
is sufficient only for a single-graph bounded certificate, never recurrence.
The supplied Coq checker, not this producer, determines certificate validity.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import time

import weighted_capacity_search as capacity
import weighted_search_v2 as search


def solve_targets(graph, timeout, wall_width, counts):
    found, capacities, certificates = {}, {}, {}
    present = {4*node[0]+node[2] for node in graph['nodes']}
    for target in range(8):
        if target not in present:
            found[target] = 'absent'
            continue
        if target in graph['ranked']:
            found[target] = 'ranked'
            continue
        try:
            with search.budget(timeout):
                width = next((k for k in range(1, wall_width+1)
                              if search.shared.wall(graph, target, k)), None)
                components = search.solve(graph, target, width is not None, counts)
                cap = None
                if components is None and width is None:
                    cap = capacity.capacity(graph, target)
                    if cap is not None:
                        components = search.solve(graph, target, True, counts)
                if components is not None:
                    found[target] = 'capacity' if cap else 'weighted'
                    wall = (search.shared.wallcert(graph, target, width) if width else
                            {'k': 0, 'guards': [], 'inside': []})
                    certificates[str(target)] = {**wall, 'components': components}
                    if cap is not None and any(c['kind'] == 'w' for c in components):
                        capacities[str(target)] = cap
        except search.BudgetExpired:
            counts['target_timeouts'] += 1
    return {'graph': graph, 'certs': certificates,
            'capacities': capacities, 'found': found}


def choose(machine, variants):
    complete = [variant for variant in variants if len(variant['found']) == 8]
    if complete:
        best = min(complete, key=lambda variant: bool(variant['capacities']))
        return {'kind': 'capacity' if best['capacities'] else 'weighted',
                'machine': machine, 'variant': best}
    choices = {}
    for target in range(8):
        options = [(index, variant['found'][target])
                   for index, variant in enumerate(variants)
                   if variant['found'].get(target) in ('ranked', 'weighted')]
        if options:
            choices[str(target)] = min(options, key=lambda x: x[1] != 'ranked')[0]
    if len(choices) == 8:
        used = sorted(set(choices.values()))
        # The checker bounds the number of supplied parts by eight. Removing
        # unused graphs preserves the exact selected target certificate.
        renumber = {old: new for new, old in enumerate(used)}
        return {'kind': 'portfolio', 'machine': machine,
                'variants': [variants[index] for index in used],
                'choices': {target: renumber[index] for target, index in choices.items()}}
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--graphs', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--timeout', type=float, default=2)
    parser.add_argument('--wall-width', type=int, default=16)
    parser.add_argument('--node-limit', type=int, default=2048)
    args = parser.parse_args()
    if not 0 < args.timeout < float('inf') or args.wall_width < 0 or args.node_limit < 1:
        parser.error('Invalid search budget')
    search.install_budget()
    started, cpu = time.monotonic(), time.process_time()
    digest = hashlib.sha256(args.graphs.read_bytes()).hexdigest()
    counts, groups, ordinary = Counter(), {}, set()
    with args.graphs.open() as source:
        for line in source:
            event = json.loads(line)
            counts['graph_status_'+event['status']] += 1
            if event['status'] == 'ordinary_candidate':
                ordinary.add(event['machine'])
            graph = event.get('graph')
            if graph is None:
                continue
            if graph['machine'] != event['machine']:
                raise ValueError('Graph/event machine mismatch')
            if len(graph['nodes']) > args.node_limit:
                counts['node_limit'] += 1
                continue
            variant = solve_targets(graph, args.timeout, args.wall_width, counts)
            groups.setdefault(graph['machine'], []).append(variant)
            counts['graphs'] += 1
    outputs = []
    for machine, variants in groups.items():
        if machine in ordinary:
            continue
        result = choose(machine, variants)
        if result is not None:
            outputs.append(result)
            counts[result['kind']+'_candidate'] += 1
    if hashlib.sha256(args.graphs.read_bytes()).hexdigest() != digest:
        raise ValueError('Graph input changed during search')
    args.output.write_text(''.join(json.dumps(row, separators=(',', ':'))+'\n' for row in outputs))
    report = {
        'scope': 'Untrusted candidate producer; every certificate requires Coq replay.',
        'ordinary_candidates_skipped': len(ordinary),
        'counts': dict(counts), 'graph_input_sha256': digest,
        'producer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'parameters': {'target_timeout': args.timeout, 'wall_width': args.wall_width,
                       'node_limit': args.node_limit},
        'wall_seconds': time.monotonic()-started, 'cpu_seconds': time.process_time()-cpu}
    args.report.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report), flush=True)


if __name__ == '__main__':
    main()
