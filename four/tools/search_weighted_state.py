"""Search for one recurrent instruction per live state in a closed weighted graph.

This is an untrusted producer. Every result needs check_weighted_state.py;
timeouts, graph failures, and unattempted rows remain in the residual.
"""
import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

from generate_pipeline_examples import codes
from weighted_campaign_v2 import atomic_json, emit_bundles, recover, sha
from weighted_codec_v2 import pack
from weighted_search_v2 import BudgetExpired, budget, install_budget, shared, solve

ROOT = Path(__file__).resolve().parents[1]


def solve_state(graph, wall_width, diagnostics):
    live = Counter(4*node[0]+node[2] for node in graph['nodes'])
    states = sorted({node[0] for node in graph['nodes']})
    certificates, choices = {}, [0, 0]
    for state in states:
        # Absent labels can be vacuously ranked; only present labels are eligible.
        options = sorted((target for target in live if target//4 == state),
                         key=lambda target: (target not in graph['ranked'], -live[target], target))
        found = False
        for target in options:
            if target in graph['ranked']:
                choices[state] = target % 4; found = True; break
            width = next((k for k in range(1, wall_width+1) if shared.wall(graph, target, k)), None)
            components = solve(graph, target, width is not None, diagnostics)
            if components is None:
                continue
            wall = shared.wallcert(graph, target, width) if width else {'k': 0, 'guards': [], 'inside': []}
            certificates[target] = {**wall, 'components': components}
            choices[state] = target % 4; found = True; break
        if not found:
            diagnostics['failed_state_'+str(state)] += 1
            return None
    result = pack({'graph': graph, 'certs': certificates})
    result['state_choices'] = choices
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--bundle-dir', type=Path, required=True)
    parser.add_argument('--registry', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--binary', type=Path, default=ROOT/'build/weighted-v2/dump')
    parser.add_argument('--width', type=int, default=2)
    parser.add_argument('--anchor', type=int, default=256)
    parser.add_argument('--graph-timeout', type=float, default=0.5)
    parser.add_argument('--lp-timeout', type=float, default=3)
    parser.add_argument('--node-limit', type=int, default=4096)
    parser.add_argument('--max-rows', type=int, default=0, help='Zero attempts the complete input')
    args = parser.parse_args()
    if not (1 <= args.width <= 8 and 0 <= args.anchor <= 4096 and args.node_limit > 0 and
            0 < args.graph_timeout < float('inf') and 0 < args.lp_timeout < float('inf') and args.max_rows >= 0):
        parser.error('Invalid search budget')
    machines = args.input.read_text().splitlines()
    if not machines or len(set(machines)) != len(machines):
        raise ValueError('Empty or duplicate input')
    for machine in machines:
        codes(machine)
    tools = ('search_weighted_state.py', 'weighted_campaign_v2.py', 'weighted_codec_v2.py',
             'weighted_search.py', 'weighted_search_v2.py', 'generate_pipeline_examples.py',
             'ExtractWeightedV2.v', 'weighted_graphs_v2.ml')
    sources = {'tools/'+name: sha(ROOT/'tools'/name) for name in tools}
    sources['../tools/multisymbol/weighted_certificates.py'] = sha(ROOT.parent/'tools/multisymbol/weighted_certificates.py')
    manifest = {'scope': 'State-only search; no checked proof claims.', 'input_rows': len(machines),
                'input_sha256': sha(args.input), 'binary_sha256': sha(args.binary), 'source_sha256': sources,
                'parameters': {'width': args.width, 'anchor': args.anchor, 'fuel': 8193, 'rounds': 33,
                               'graph_timeout': args.graph_timeout, 'lp_timeout': args.lp_timeout,
                               'node_limit': args.node_limit, 'wall_width': 16}}
    args.output_dir.mkdir(parents=True, exist_ok=True)
    manifest_path = args.output_dir/'manifest.json'
    if manifest_path.exists() and json.loads(manifest_path.read_text()) != manifest:
        raise ValueError('Frozen state search inputs changed')
    atomic_json(manifest_path, manifest)
    ledger = args.output_dir/'results.jsonl'
    results = recover(ledger)
    if [row['machine'] for row in results] != machines[:len(results)]:
        raise ValueError('Saved search is not an exact input prefix')
    limit = min(args.max_rows or len(machines), len(machines))
    install_budget()
    start = time.monotonic()
    with ledger.open('a') as output:
        for offset in range(len(results), limit, 16):
            batch = machines[offset:min(offset+16, limit)]
            chunk = args.output_dir/'chunk-input.txt'; chunk.write_text(''.join(m+'\n' for m in batch))
            graph_path = args.output_dir/'chunk-graphs.jsonl'
            command = [str(args.binary.resolve()), str(chunk.resolve()), str(args.width), str(args.anchor),
                       '8193', '33', str(args.graph_timeout), str(args.node_limit)]
            with graph_path.open('w') as stream:
                subprocess.run(command, stdout=stream, stderr=subprocess.PIPE, check=True,
                               timeout=max(60, (2*args.graph_timeout+2)*len(batch)))
            events = [json.loads(line) for line in graph_path.read_text().splitlines()]
            if [(e['machine'], e['mirror']) for e in events] != [(m, flip) for m in batch for flip in (0, 1)]:
                raise ValueError('Graph inventory differs')
            for index, machine in enumerate(batch):
                pair = events[2*index:2*index+2]
                candidate, diagnostics = None, Counter()
                for event in pair:
                    graph = event.get('graph')
                    if graph is None:
                        continue
                    try:
                        with budget(args.lp_timeout):
                            candidate = solve_state(graph, 16, diagnostics)
                        if candidate is not None:
                            break
                    except BudgetExpired:
                        diagnostics['lp_timeout'] += 1
                row = {'machine': machine, 'candidate': candidate, 'diagnostics': dict(diagnostics),
                       'orientations': [{k: v for k, v in event.items() if k != 'graph'} for event in pair]}
                output.write(json.dumps(row, separators=(',', ':'))+'\n'); output.flush(); os.fsync(output.fileno())
                results.append(row)
            print(json.dumps({'completed': len(results), 'input_rows': len(machines),
                              'candidates': sum(row['candidate'] is not None for row in results),
                              'seconds_this_process': round(time.monotonic()-start, 2)}), flush=True)
    if sha(args.input) != manifest['input_sha256'] or sha(args.binary) != manifest['binary_sha256']:
        raise ValueError('Search input or binary changed')
    if any(sha(ROOT/name) != digest for name, digest in sources.items()):
        raise ValueError('Search source changed')
    registry = emit_bundles(results, args.bundle_dir, args.registry,
                            {'manifest_sha256': sha(manifest_path), 'results_sha256': sha(ledger),
                             'input_sha256': sha(args.input), 'attempted_rows': len(results),
                             'scope': 'State-only candidate certificates; instruction recurrence is not checked.'})
    accepted = {row['machine'] for row in results if row['candidate'] is not None}
    residual = args.output_dir/'not-accepted.txt'
    residual.write_text(''.join(m+'\n' for m in machines if m not in accepted))
    report = {'status': 'Untrusted state search; zero kernel or census-link claims.',
              'input_rows': len(machines), 'attempted_rows': len(results),
              'deferred_rows': len(machines)-len(results), 'candidate_rows': len(accepted),
              'not_accepted_rows': len(machines)-len(accepted), 'not_accepted_sha256': sha(residual),
              'manifest': manifest, 'results_sha256': sha(ledger), 'registry_sha256': sha(args.registry),
              'kernel_checked_rows': 0, 'census_linked_rows': 0}
    atomic_json(args.report, report)
    print(json.dumps({k: report[k] for k in ('attempted_rows', 'candidate_rows', 'not_accepted_rows')}), flush=True)


if __name__ == '__main__':
    main()
