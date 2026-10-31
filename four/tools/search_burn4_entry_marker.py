"""Bounded discovery for the proved B-entry marker predicate; no proof credit.

Search the frozen 667-family state residual with seven nonblank marker masks
and 125 weight tuples. Coq replay, exact inventory and full audit remain required.
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
INPUT = ROOT / 'research/burn4-history-input.txt'
MANIFEST = ROOT / 'research/burn4-history-input-manifest.json'
REPORT = ROOT / 'research/burn4-entry-marker-search.json'
MASKS = range(2, 16, 2)
WEIGHTS = [(0,) + values for values in itertools.product(range(5), repeat=3)]
INPUT_SHA256 = '68cb79c438fe81efecb8823338dc06d6dd106b3da3beed5432e9b243e2971de8'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def preserve(table, mask):
    return all(value != 16 and (value % 2 == 0
        or (cell >= 4 and not ((mask >> (cell % 4)) & 1))
        or (value // 2 % 2 == 0 and ((mask >> (value // 4)) & 1)))
        for cell, value in enumerate(table))


def capacity(table, weights):
    return all(w <= 4 for w in weights) and all(value != 16 and (
        value % 2 == 0 or weights[value // 4] - weights[symbol]
        <= (1 if value // 2 % 2 else -1)) for symbol, value in enumerate(table[4:]))


def predicate(table, mask, weights):
    return (not (mask & 1) and preserve(table, mask) and capacity(table, weights)
            and any(ore_goal(table, 1, mirror) for mirror in (0, 1)))


def controls():
    positive = [5, 8, 10, 6, 11, 14, 1, 0]
    cases = [(positive, 2, (0, 0, 1, 0), True),
        ([5, 10, 10, 6, 11, 13, 1, 12], 10, (0, 1, 1, 0), True),
        ([7, 8, 10, 6, 11, 14, 1, 0], 2, (0, 0, 1, 0), False),
        ([9, 8, 10, 6, 11, 14, 1, 0], 2, (0, 0, 1, 0), False),
        ([5, 8, 10, 6, 11, 7, 1, 0], 2, (0, 0, 1, 0), False),
        ([5, 8, 10, 6, 11, 1, 1, 0], 2, (0, 1, 1, 0), False),
        (positive, 2, (0, 0, 0, 0), False), (positive, 2, (0, 0, 2, 0), False),
        (positive, 2, (0, 5, 1, 0), False),
        ([5, 8, 10, 16, 11, 14, 1, 0], 2, (0, 0, 1, 0), False),
        ([5, 4, 10, 6, 11, 14, 1, 0], 2, (0, 0, 1, 0), False),
        (positive, 3, (0, 0, 1, 0), False)]
    for table, mask, weights, expected in cases:
        if predicate(table, mask, weights) != expected:
            raise ValueError('Coq regression control differs')
    return len(cases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    resource.setrlimit(resource.RLIMIT_AS, (1073741824, 1073741824))
    machines = INPUT.read_text().splitlines()
    manifest = json.loads(MANIFEST.read_text())
    if (sha(INPUT) != INPUT_SHA256 or manifest['remaining_sha256'] != INPUT_SHA256
        or len(machines) != 667 or len(set(machines)) != 667):
        raise ValueError('Expected exact frozen 667-family residual')
    control_count = controls()
    paths = [Path(__file__), INPUT, MANIFEST,
        ROOT / 'proof-sources/burn4-entry-marker/EntryMarker.v',
        ROOT / 'proof-sources/burn4-entry-marker/EntryRegression.v',
        ROOT / 'theories/OneStateReach.v', ROOT / 'theories/MarkerState.v',
        ROOT / 'theories/MarkerPotential.v', ROOT / 'tools/marker_state_profile_v2.py',
        ROOT / 'tools/generate_pipeline_examples.py']
    pins = {str(p.relative_to(ROOT)): sha(p) for p in paths}
    rows, rejected = [], Counter()
    for machine in machines:
        table = codes(machine)
        if 16 in table:
            rejected['partial_table'] += 1
            continue
        if not any(ore_goal(table, 1, mirror) for mirror in (0, 1)):
            rejected['other_state_uniform_reachability'] += 1
            continue
        masks = [mask for mask in MASKS if preserve(table, mask)]
        if not masks:
            rejected['entry_or_B_marker_preservation'] += 1
            continue
        weights = next((w for w in WEIGHTS if capacity(table, w)), None)
        if weights is None:
            rejected['capacity_inequalities'] += 1
            continue
        mask = masks[0]
        if not predicate(table, mask, weights):
            raise ValueError('Selected tuple fails exact predicate')
        rows.append({'machine': machine, 'code': sum(v * 17**i for i, v in enumerate(table)),
                     'marker_mask': mask, 'weights': list(weights)})
    report = {'scope': 'Untrusted finite predicate search; candidates are not kernel discharges.',
        'input_rows': len(machines), 'candidate_rows': len(rows),
        'parameters': {'state_bound': 0, 'nonblank_marker_masks': list(MASKS),
                       'weight0': 0, 'other_weights': [0, 1, 2, 3, 4], 'workers': 1},
        'control_rows': control_count, 'rejection_counts': dict(rejected),
        'source_sha256': pins, 'rows': rows}
    if any(sha(ROOT / name) != digest for name, digest in pins.items()):
        raise ValueError('Pinned discovery sources changed during search')
    text = json.dumps(report, indent=2, sort_keys=True) + '\n'
    if args.check or REPORT.exists():
        if REPORT.read_text() != text:
            raise ValueError('Frozen search report differs')
    else:
        REPORT.write_text(text)
    print(json.dumps({key: report[key] for key in ('input_rows', 'candidate_rows', 'rejection_counts')}))


if __name__ == '__main__':
    main()
