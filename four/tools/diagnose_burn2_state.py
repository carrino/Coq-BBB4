"""Bounded untrusted visit diagnostics for the fixed 32 state-search misses."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import resource
import time

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / 'build/burn2-state/state-capacity-pilot-input.json'
OUTPUT = ROOT / 'research/burn2-state-diagnostics.json'
POINTS = (4096, 65536, 1000000)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def trace(machine):
    text = machine.replace('_', '')
    transitions = []
    for index in range(8):
        cell = text[3 * index:3 * index + 3]
        transitions.append(None if cell == '---' else
                           (int(cell[0]), -1 if cell[1] == 'L' else 1, ord(cell[2]) - ord('A')))
    tape, position, state = {}, 0, 0
    last, visits, previous_visits = [0, None], [1, 0], [1, 0]
    observations, executed, halted = [], 0, None
    for stop in POINTS:
        interval_runs, run_length, run_state = [0, 0], 0, None
        while executed < stop and halted is None:
            transition = transitions[4 * state + tape.get(position, 0)]
            if transition is None:
                halted = {'configuration_step': executed, 'state': chr(65 + state),
                          'read_symbol': tape.get(position, 0)}
                break
            write, move, state = transition
            if write:
                tape[position] = write
            else:
                tape.pop(position, None)
            position += move
            executed += 1
            visits[state] += 1
            last[state] = executed
            run_length = run_length + 1 if run_state == state else 1
            run_state = state
            interval_runs[state] = max(interval_runs[state], run_length)
        interval = [visits[q] - previous_visits[q] for q in range(2)]
        observations.append({'requested_step': stop, 'executed_steps': executed,
            'last_state_visit': last.copy(), 'visits_including_initial': visits.copy(),
            'visits_in_interval': interval, 'longest_same_state_run_in_interval': interval_runs,
            'head_position': position, 'nonblank_cells': len(tape), 'halt': halted})
        previous_visits = visits.copy()
    last_interval = observations[-1]['visits_in_interval']
    if halted:
        cluster = 'halted'
    elif all(last_interval):
        cluster = 'both_states_recent_long_excursions' if max(observations[-1]['longest_same_state_run_in_interval']) > 256 else 'both_states_recent_short_excursions'
    else:
        missing = last_interval.index(0)
        cluster = 'one_state_observed_tail_late_last_visit' if (last[missing] or 0) > 4096 else 'one_state_observed_tail_early_last_visit'
    return {'machine': machine, 'cluster': cluster, 'observations': observations}


def main():
    resource.setrlimit(resource.RLIMIT_AS, (1073741824, 1073741824))
    selected = json.loads(INPUT.read_text())
    assert len(selected) == 32 and len({row['machine'] for row in selected}) == 32
    started, rows = time.monotonic(), []
    for selected_row in selected:
        row = trace(selected_row['machine'])
        rows.append(row)
        print(json.dumps({'rows': len(rows), 'machine': row['machine'], 'cluster': row['cluster']}), flush=True)
    report = {'scope': 'Finite simulation diagnostics only; no proof of recurrence, tail permanence or bound.',
              'input_sha256': sha(INPUT), 'producer_sha256': sha(Path(__file__)),
              'observation_points': list(POINTS), 'state_order': ['A', 'B'],
              'visit_convention': 'Configuration step 0 is the initial A visit; interval counts cover (previous point, requested point].',
              'rows': rows, 'clusters': dict(Counter(row['cluster'] for row in rows)),
              'workers': 1, 'maximum_steps_per_machine': POINTS[-1]}
    text = json.dumps(report, indent=2, sort_keys=True) + '\n'
    if OUTPUT.exists() and OUTPUT.read_text() != text:
        raise ValueError('Refusing to overwrite changed diagnostic report')
    OUTPUT.write_text(text)
    print(json.dumps({'clusters': report['clusters'], 'seconds': round(time.monotonic() - started, 3)}))


if __name__ == '__main__':
    main()
