"""Extract state witnesses from saved instruction-capacity near-miss graphs.

This untrusted selector reuses one ordinary recurrent instruction per state.
The existing WeightedState checker rechecks graph closure and recurrence;
neither native ranked flags nor the saved search report constitute proof.
"""
import hashlib
import json
from pathlib import Path

from weighted_codec_v2 import bundle_encode, pack

ROOT = Path(__file__).resolve().parents[1]
PREFIX = ROOT / 'research/burn3-capacity-state'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exact(path, contents):
    if path.exists() and path.read_text() != contents:
        raise ValueError('Refusing to change frozen selection: ' + str(path))
    path.write_text(contents)


def save(path, value):
    exact(path, json.dumps(value, indent=2, sort_keys=True) + '\n')


def main():
    manifest = ROOT / 'research/burn2-capacity-manifest.json'
    summary = ROOT / 'research/burn2-capacity-summary.json'
    residual = ROOT / 'build/next-burndown/state-remaining.txt'
    sources = {str(path.relative_to(ROOT)): sha(path) for path in
               (Path(__file__), ROOT / 'tools/weighted_codec_v2.py', manifest, summary, residual)}
    old = set(residual.read_text().splitlines())
    accepted = set(json.loads(summary.read_text())['new_state_ids'])
    machines = json.loads(manifest.read_text())['machines']
    pending = [(i, machine) for i, machine in enumerate(machines) if machine in old - accepted]
    if len(pending) != 5:
        raise ValueError('Expected exactly five remaining state obligations')
    compact, selected = [], []
    for index, machine in pending:
        path = ROOT / f'build/burn2-capacity/row-{index:03d}/variants.jsonl'
        sources[str(path.relative_to(ROOT))] = sha(path)
        variants = [json.loads(line) for line in path.read_text().splitlines()]
        eligible = []
        for variant_index, variant in enumerate(variants):
            graph = variant['graph']
            if graph['machine'] != machine:
                raise ValueError('Saved graph belongs to a different machine')
            present = {4 * node[0] + node[2] for node in graph['nodes']}
            choices = []
            for state in range(2):
                options = sorted(target for target in present & set(graph['ranked'])
                                 if target // 4 == state)
                if not options:
                    break
                choices.append(options[0] % 4)
            if len(choices) == 2:
                eligible.append((len(graph['nodes']), graph['mirror'], variant_index, graph, choices))
        if not eligible:
            raise ValueError('No shared graph with an ordinary witness for each state: ' + machine)
        _, _, variant_index, graph, choices = min(eligible, key=lambda row: row[:3])
        row = pack({'graph': graph, 'certs': {}})
        row['state_choices'] = choices
        compact.append(row)
        selected.append({'machine': machine, 'capacity_index': index,
                         'variant_index': variant_index, 'nodes': len(graph['nodes']),
                         'width': graph['n'], 'anchor': graph['t'], 'mirror': graph['mirror'],
                         'state_choices': choices})
    if any(sha(ROOT / name) != digest for name, digest in sources.items()):
        raise ValueError('Selection source changed during extraction')
    bundle = PREFIX.with_name(PREFIX.name + '-certificates.json')
    exact(bundle, bundle_encode(compact))
    selection = {'scope': 'Untrusted certificate extraction; no proof claim until kernel replay.',
                 'sources_sha256': sources, 'selected_rows': len(compact), 'selected': selected,
                 'method': 'One present ordinary-ranked instruction per state in one shared closed graph; no capacity witnesses or new theorem.'}
    save(PREFIX.with_name(PREFIX.name + '-selection.json'), selection)
    save(PREFIX.with_name(PREFIX.name + '-input.json'), {
        'format': 'BBB24 compact weighted certificates v2', 'rows': len(compact),
        'scope': 'State-only; no instruction-bound claim.', 'selection': selection,
        'bundles': [{'path': str(bundle.relative_to(ROOT)), 'rows': len(compact),
                     'bytes': bundle.stat().st_size, 'sha256': sha(bundle)}]})
    print(json.dumps(selected, indent=2))


if __name__ == '__main__':
    main()
