"""Bounded pure-Python search for the proved relaxed-marker predicate.

This discovery scan proves nothing. Every accepted table/mask/weight tuple
must still pass the Coq checker, exact census inventory and full kernel audit.
It scans the fixed694 history misses and preserves its published search report.
"""
import argparse
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path
import resource

from generate_pipeline_examples import codes
from marker_state_profile_v2 import ore_goal

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / 'research/burn3-relaxed-marker-search-input.json'
REPORT = ROOT / 'research/burn3-relaxed-marker-search.json'
EXAMPLE = '1LB2RA2RA1RA_2RB3LB0LB3LA'
MASKS = range(2, 16, 2)
WEIGHTS = [(0,) + values for values in itertools.product(range(5), repeat=3)]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def preserve(table, mask):
    if any(v == 16 for v in table):
        return False
    for cell, value in enumerate(table):
        if cell == 0 or ((mask >> (cell % 4)) & 1):
            if value // 2 % 2:
                if value % 2 != 0:
                    return False
            elif not ((mask >> (value // 4)) & 1):
                return False
    return True


def capacity(table, weights):
    return all(w <= 4 for w in weights) and all(
        value % 2 == 0 or weights[value // 4] - weights[symbol] <= (1 if value // 2 % 2 else -1)
        for symbol, value in enumerate(table[4:]))


def predicate(table, mask, weights):
    return (not (mask & 1) and preserve(table, mask) and table[4] % 4 == 3
            and capacity(table, weights) and any(ore_goal(table, 1, mirror) for mirror in (0, 1)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    resource.setrlimit(resource.RLIMIT_AS, (1073741824, 1073741824))
    data = json.loads(INPUT.read_text())
    machines = data['rows']
    if len(machines) != 694 or len(set(machines)) != len(machines):
        raise ValueError('Expected694 distinct history misses')
    if sha(ROOT / data['source_report']) != data['source_report_sha256']:
        raise ValueError('Frozen history search report differs')
    controls = [(10, (0, 1, 1, 0), True), (2, (0, 1, 1, 0), False),
                (8, (0, 1, 1, 0), False), (11, (0, 1, 1, 0), False),
                (10, (0, 0, 1, 0), False), (10, (0, 1, 2, 0), False)]
    example_table = codes(EXAMPLE)
    for mask, weights, expected in controls:
        if predicate(example_table, mask, weights) != expected:
            raise ValueError('Known Coq regression control differs')
    paths = [Path(__file__), INPUT, ROOT / data['source_report'],
             ROOT / 'research/burn3-relaxed-marker-checked.json',
             ROOT / 'proof-sources/burn3-relaxed-marker/RelaxedMarker.v',
             ROOT / 'proof-sources/burn3-relaxed-marker/Regression.v',
             ROOT / 'theories/OneStateReach.v', ROOT / 'theories/MarkerState.v',
             ROOT / 'theories/MarkerPotential.v', ROOT / 'tools/marker_state_profile_v2.py',
             ROOT / 'tools/generate_pipeline_examples.py']
    pins = {str(p.relative_to(ROOT)): sha(p) for p in paths}
    rows, rejections = [], Counter()
    for machine in machines:
        table = codes(machine)
        if 16 in table:
            rejections['partial_table'] += 1
            continue
        if table[4] % 4 != 3:
            rejections['B_blank_not_right_stay_B'] += 1
            continue
        if not any(ore_goal(table, 1, mirror) for mirror in (0, 1)):
            rejections['other_state_reachability'] += 1
            continue
        masks = [mask for mask in MASKS if preserve(table, mask)]
        if not masks:
            rejections['marker_preservation'] += 1
            continue
        weights = next((weights for weights in WEIGHTS if capacity(table, weights)), None)
        if weights is None:
            rejections['capacity_inequalities'] += 1
            continue
        mask = min(masks, key=lambda value: (value.bit_count(), value))
        if not predicate(table, mask, weights):
            raise ValueError('Selected witness fails exact discovery predicate')
        old_exit = all(table[4 + symbol] % 2 == 0 for symbol in range(4) if (mask >> symbol) & 1)
        rows.append({'machine': machine, 'code': sum(value * 17**i for i, value in enumerate(table)),
                     'marker_mask': mask, 'weights': list(weights),
                     'same_parameters_satisfy_original_immediate_exit_clause': old_exit,
                     'already_audited_example': machine == EXAMPLE})
    if not any(row['machine'] == EXAMPLE for row in rows):
        raise ValueError('The audited positive control was not recovered')
    report = {'scope': 'Untrusted bounded discovery for a proved checker; candidate counts are not kernel discharges.',
              'input_rows': len(machines), 'candidate_rows': len(rows),
              'new_candidates_beyond_audited_example': sum(not row['already_audited_example'] for row in rows),
              'parameters': {'state_bound': 0, 'nonblank_marker_masks': list(MASKS),
                             'weight0': 0, 'other_weights': [0, 1, 2, 3, 4], 'workers': 1},
              'control_rows': len(controls), 'rejection_counts': dict(rejections),
              'rows': rows, 'source_sha256': pins}
    if any(sha(ROOT / name) != digest for name, digest in pins.items()):
        raise ValueError('Pinned discovery inputs changed during search')
    text = json.dumps(report, indent=2, sort_keys=True) + '\n'
    if args.check:
        if REPORT.read_text() != text:
            raise ValueError('Frozen search report differs')
    elif REPORT.exists():
        if REPORT.read_text() != text:
            raise ValueError('Refusing to overwrite a changed search report')
    else:
        REPORT.write_text(text)
    print(json.dumps({key: report[key] for key in ('input_rows', 'candidate_rows',
          'new_candidates_beyond_audited_example', 'rejection_counts')}))


if __name__ == '__main__':
    main()
