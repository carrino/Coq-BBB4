"""Finite-trace diagnostics for remaining capacity instruction obligations.

Search flags and finite simulations are untrusted observations, not recurrence
or permanent-extinction proofs. No proof inventory is changed by this tool.
"""
from collections import Counter, deque
import hashlib
import json
from pathlib import Path
import resource

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'build/burn2-capacity'
OUTPUT = ROOT / 'research/burn3-capacity-instruction-diagnostics.json'
POINTS = (4096, 65536, 1000000)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def trace(machine, targets):
    text = machine.replace('_', '')
    transitions = []
    for index in range(8):
        cell = text[3 * index:3 * index + 3]
        transitions.append(None if cell == '---' else
                           (int(cell[0]), -1 if cell[1] == 'L' else 1, ord(cell[2]) - 65))
    tape, position, state, executed = {}, 0, 0, 0
    visits, previous, last = [0] * 8, [0] * 8, [None] * 8
    recent = {target: deque(maxlen=16) for target in targets}
    max_gap = {target: 0 for target in targets}
    observations, undefined = [], None
    for stop in POINTS:
        while executed < stop and undefined is None:
            target = 4 * state + tape.get(position, 0)
            transition = transitions[target]
            if transition is None:
                undefined = {'configuration_step': executed, 'instruction': target}
                break
            if target in recent:
                recent[target].append(executed)
                if last[target] is not None:
                    max_gap[target] = max(max_gap[target], executed - last[target])
            visits[target] += 1
            last[target] = executed
            write, move, state = transition
            if write:
                tape[position] = write
            else:
                tape.pop(position, None)
            position += move
            executed += 1
        observations.append({'requested_steps': stop, 'executed_steps': executed,
            'visits': visits.copy(), 'visits_in_interval': [x-y for x,y in zip(visits, previous)],
            'last_firing_configuration_step': last.copy(), 'head_position': position,
            'nonblank_cells': len(tape), 'undefined_transition': undefined})
        previous = visits.copy()
    final = observations[-1]
    classes = {}
    for target in targets:
        if undefined:
            category = 'undefined_transition_reached'
        elif final['visits_in_interval'][target]:
            category = 'observed_in_final_interval'
        elif last[target] is None:
            category = 'not_observed_within_budget'
        elif last[target] < 4096:
            category = 'last_observed_before_anchor'
        else:
            category = 'last_observed_after_anchor'
        classes[str(target)] = {'category': category, 'last_firing': last[target],
                                'total_firings': visits[target], 'maximum_observed_gap': max_gap[target],
                                'recent_firing_steps': list(recent[target])}
    return {'observations': observations, 'targets': classes}


def main():
    resource.setrlimit(resource.RLIMIT_AS, (1073741824, 1073741824))
    ledger = BASE / 'results.jsonl'
    pins = {str(ledger.relative_to(ROOT)): sha(ledger),
            str(Path(__file__).relative_to(ROOT)): sha(Path(__file__))}
    results = []
    for row in [json.loads(line) for line in ledger.read_text().splitlines()]:
        if row.get('candidate'):
            continue
        path = BASE / f"row-{row['index']:03d}/variants.jsonl"
        pins[str(path.relative_to(ROOT))] = sha(path)
        variants = [json.loads(line) for line in path.read_text().splitlines()]
        recurrence = {int(t) for v in variants for t, kind in v['found'].items()
                      if kind in ('ranked', 'weighted')}
        capacity_recurrence = {int(t) for v in variants for t, kind in v['found'].items()
                               if kind in ('ranked', 'weighted', 'capacity')}
        bounded = {int(t) for v in variants for t in v['found']}
        missing = sorted(set(range(8)) - bounded)
        if len(missing) != 1:
            raise ValueError('Expected exactly one uncovered target per instruction miss')
        result = {'machine': row['machine'], 'index': row['index'],
                  'missing_any_witness': missing,
                  'missing_recurrence': sorted(set(range(8)) - recurrence),
                  'missing_recurrence_with_capacity': sorted(set(range(8)) - capacity_recurrence),
                  'variants': [{'width': v['graph']['n'], 'anchor': v['graph']['t'],
                                'mirror': v['graph']['mirror'], 'nodes': len(v['graph']['nodes']),
                                'found': v['found']} for v in variants],
                  **trace(row['machine'], missing)}
        results.append(result)
        print(json.dumps({'rows': len(results), 'machine': row['machine'],
                          'target': missing[0], 'category': result['targets'][str(missing[0])]['category']}), flush=True)
    if len(results) != 41 or any(sha(ROOT / name) != digest for name, digest in pins.items()):
        raise ValueError('Input changed or incomplete diagnostic inventory')
    counts = Counter(item['category'] for row in results for item in row['targets'].values())
    report = {'scope': 'Bounded exact finite simulation and untrusted graph flags; no proof claims.',
              'sources_sha256': pins, 'rows': results, 'instruction_order':
              [f'{q}{s}' for q in 'AB' for s in range(4)],
              'observation_points': POINTS, 'workers': 1,
              'firing_convention': 'Instruction at configuration step k executes the transition from k to k+1.',
              'categories': dict(counts)}
    text = json.dumps(report, indent=2, sort_keys=True) + '\n'
    if OUTPUT.exists() and OUTPUT.read_text() != text:
        raise ValueError('Refusing to overwrite changed diagnostics')
    OUTPUT.write_text(text)
    print(json.dumps(dict(counts)), flush=True)


if __name__ == '__main__':
    main()
