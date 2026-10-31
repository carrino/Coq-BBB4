"""Finite controls for quaternary sibling checksum macros; these are not proofs."""
import argparse
import itertools
import time
import json
from pathlib import Path
import burn10_marker_history_pilot as helper

ROOT = helper.ROOT
REPORT = ROOT / 'research/burn17-quaternary-sibling-native.json'
MACHINE = '1LB2LB0LB1RA_2RB2RA3LB1RB'


def run(table, conf, count):
    state, left, head, right = conf
    for _ in range(count):
        cell = table[4 * state + head]
        write, direction, state = cell // 4, cell // 2 % 2, cell % 2
        if direction:
            left = [write] + left
            head, right = (right[0] if right else 0), right[1:]
        else:
            right = [write] + right
            head, left = (left[0] if left else 0), left[1:]
    return state, left, head, right


def front(state, left, right):
    return state, left, (right[0] if right else 0), right[1:]


def back(state, left, right):
    return state, left[1:], (left[0] if left else 0), right


def encode(digits):
    return [symbol for digit in digits for symbol in
            ((1 if digit % 2 == 0 else 2), (1 if digit < 2 else 2))]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    start = time.monotonic()
    table = helper.codes(MACHINE)
    macros = steps = 0
    for size in range(1, 8):
        for digits in itertools.product(range(4), repeat=size):
            head = sum(digits) % 3
            carry = next((i for i, d in enumerate(digits) if d != 3), size)
            if carry == size:
                following = [1] + [0] * (size - 1) + [2]
                gap, new_head = 4 * size + 3, 0
            else:
                following = [0] * carry + [digits[carry] + 1] + list(digits[carry + 1:])
                gap = 4 * carry + (4 if digits[carry] == 1 else 2)
                new_head = (head + 1) % 3
            assert run(table, (0, encode(digits), head, []), gap) == (0, encode(following), new_head, [])
            assert new_head == sum(following) % 3
            macros += 1
            steps += gap
    assert macros == 21844 and steps == 87369
    assert run(table, (0, [], 0, []), 3) == (0, [2, 2], 0, [])
    assert run(table, (0, [2, 2], 1, []), 7) != (0, encode([1, 2]), 0, [])
    sources = [Path(__file__), Path(helper.__file__), ROOT / 'tools/generate_pipeline_examples.py']
    stable = dict(
        scope='Finite synthetic controls only; no proof credit.',
        rows=[dict(machine=MACHINE, code=sum(v * 17**i for i, v in enumerate(table)))],
        max_digits=7, main_configurations=macros, simulated_macro_steps=steps,
        source_sha256={str(p.relative_to(ROOT)): helper.sha(p) for p in sources},
        encoding=['11', '21', '12', '22'], checksum='head equals digit sum modulo3',
        short_gap='4*carry+2 for digits0/2', long_gap='4*carry+4 for digit1',
        overflow_gap='4*digits+3', overflow_digits='1, then digits-1 zeros, then2',
        excluded_corner='all-maximal digits with head1 do not satisfy the overflow rule')
    if args.check:
        saved = json.loads(REPORT.read_text())
        assert all(saved[k] == v for k, v in stable.items())
        print('All 21,844 quaternary sibling checksum macros replayed exactly.')
    else:
        if REPORT.exists():
            raise ValueError('Frozen native report exists; use --check')
        helper.exact(REPORT, dict(stable, seconds=round(time.monotonic() - start, 6)))
        print('Native quaternary sibling checksum controls passed; no proof credit.')


if __name__ == '__main__':
    main()
