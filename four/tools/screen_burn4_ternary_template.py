"""Read-only residual screen for the six-transition ternary counter template.

The twelve tested images are blank-preserving symbol permutations and reflection.
Only matched tables receive a bounded prefix check. Counter-phase recognition
allows a dormant left suffix beyond the sentinel, as in tc_block's parameter l.
No search result is a Coq proof or changes the verified inventory.
"""
import hashlib
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'research/burn4-ternary-template-screen.json'
RESIDUAL = ROOT / 'build/burn3-burndown/both-remaining.txt'
STATE_RESIDUAL = ROOT / 'build/burn3-burndown/state-remaining.txt'
MACHINE = '1LB2LB3LB2RA_3RA1RA1LB1RB'
SUPPORT = [0, 1, 2, 3, 5, 6]
PREFIX_LIMIT = 4096


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exact(path, value):
    text = json.dumps(value, indent=2, sort_keys=True)+'\n'
    if path.exists() and path.read_text() != text:
        raise ValueError('Frozen screen differs: '+str(path))
    if not path.exists():
        path.write_text(text)


def cells(machine):
    if len(machine) != 25 or machine[12] != '_':
        raise ValueError('Invalid machine string')
    flat = machine.replace('_', '')
    return [flat[3*i:3*i+3] for i in range(8)]


def entry(machine, sigma, mirror):
    table = [None if c == '---' else
             (int(c[0]), -1 if c[1] == 'L' else 1, ord(c[2])-65)
             for c in cells(machine)]
    inverse = {s: i for i, s in enumerate(sigma)}
    orientation = -1 if mirror else 1
    tape, position, state = {}, 0, 0
    last_bad = {4: None, 7: None}
    for step in range(PREFIX_LIMIT+1):
        head = tape.get(position, 0)
        # Translate into the counter's canonical orientation and alphabet.
        transformed = {orientation*(p-position): inverse[h] for p, h in tape.items()}
        if state == 0 and head == 0 and all(p < 0 for p in transformed):
            n = 0
            while transformed.get(-n-1, 0) == 2:
                n += 1
            if transformed.get(-n-1, 0) == 1:
                lo = min(transformed)
                suffix = [transformed.get(p, 0) for p in range(-n-2, lo-1, -1)]
                return {'status': 'counter_entry', 'entry_step': step,
                        'counter_n': n, 'dormant_left_suffix': suffix,
                        'last_bad_firings_in_prefix': last_bad,
                        'simulated_steps': step}
        if step == PREFIX_LIMIT:
            break
        instruction = 4*state+head
        canonical = 4*state+inverse[head]
        if canonical in last_bad:
            last_bad[canonical] = step
        transition = table[instruction]
        if transition is None:
            return {'status': 'undefined_transition', 'simulated_steps': step,
                    'instruction': instruction}
        write, direction, state = transition
        if write:
            tape[position] = write
        else:
            tape.pop(position, None)
        position += direction
    return {'status': 'prefix_limit', 'simulated_steps': PREFIX_LIMIT}


def main():
    source_paths = [Path(__file__), RESIDUAL, STATE_RESIDUAL,
                    ROOT/'research/burn3-burndown-summary.json',
                    ROOT/'research/burn4-ternary-counter-checked.json',
                    ROOT/'research/burn4-ternary-counter/Counter.v',
                    ROOT/'research/burn4-ternary-counter-machines.json']
    sources = {str(p.relative_to(ROOT)): sha(p) for p in source_paths}
    residual = RESIDUAL.read_text().splitlines()
    if len(residual) != 31495 or len(set(residual)) != len(residual):
        raise ValueError('Unexpected exact instruction residual')
    summary = json.loads((ROOT/'research/burn3-burndown-summary.json').read_text())
    if sha(RESIDUAL) != summary['outputs']['both-remaining.txt']['sha256']:
        raise ValueError('Residual does not match its published summary')
    already = {row['machine'] for row in json.loads(
        (ROOT/'research/burn4-ternary-counter-machines.json').read_text())['rows']}
    if already != {MACHINE}:
        raise ValueError('Unexpected original counter inventory')
    patterns = []
    original = cells(MACHINE)
    for perm in itertools.permutations([1, 2, 3]):
        sigma = [0, *perm]
        for mirror in (False, True):
            constraints = []
            for target in SUPPORT:
                q, h = divmod(target, 4)
                c = original[target]
                direction = {'L': 'R', 'R': 'L'}[c[1]] if mirror else c[1]
                constraints.append((4*q+sigma[h], str(sigma[int(c[0])])+direction+c[2]))
            patterns.append((sigma, mirror, constraints))
    matches = []
    for machine in residual:
        table = cells(machine)
        for sigma, mirror, constraints in patterns:
            if all(table[index] == value for index, value in constraints):
                matches.append({'machine': machine, 'symbol_map': sigma, 'mirror': mirror,
                                'already_accepted_original': machine in already,
                                **entry(machine, sigma, mirror)})
    new = [row for row in matches if not row['already_accepted_original']
           and row['status'] == 'counter_entry']
    state_pending = set(STATE_RESIDUAL.read_text().splitlines())
    report = {'scope': 'Untrusted exact table matches and bounded phase-entry checks; no proof claim.',
              'sources_sha256': sources, 'residual_rows': len(residual),
              'image_patterns': len(patterns), 'fixed_instruction_ids': SUPPORT,
              'prefix_limit_per_match': PREFIX_LIMIT, 'matches': matches,
              'matched_ids': len({row['machine'] for row in matches}),
              'new_counter_entry_ids': len({row['machine'] for row in new}),
              'new_ids_still_state_pending': sorted({r['machine'] for r in new}&state_pending),
              'total_simulated_steps': sum(row['simulated_steps'] for row in matches)}
    if any(sha(ROOT/name) != digest for name, digest in sources.items()):
        raise ValueError('Frozen screen input changed')
    exact(OUTPUT, report)
    print(json.dumps({'matched_ids': report['matched_ids'],
                      'new_counter_entry_ids': report['new_counter_entry_ids'],
                      'new_ids_still_state_pending': report['new_ids_still_state_pending'],
                      'total_simulated_steps': report['total_simulated_steps']}))


if __name__ == '__main__':
    main()
