"""Finite controls for double-zero binary-rank macros; these are not proofs."""
import argparse
import itertools
import time
import json
from pathlib import Path
import burn10_marker_history_pilot as helper

ROOT = helper.ROOT
REPORT = ROOT / 'research/burn17-double-zero-rank-native.json'
MACHINE = '1LB0RA0LB2RA_1RB3LB2LB1LA'


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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    start = time.monotonic()
    table = helper.codes(MACHINE)
    contexts = [[]] + [[a] for a in range(4)] + [
        list(t) for t in itertools.product(range(4), repeat=2)]
    local_macros = steps = 0
    for n in range(8):
        for left, right in itertools.product(contexts, repeat=2):
            gap = 4*n+8
            assert run(table, back(1, [0,0]+left, [0]*n+[2]+right), gap) == back(1, [0,0]+left, [2]*n+[0]+right)
            finish = 3*n+7
            assert run(table, back(1, [0,0]+left, [0]*n+[1]+right), finish) == front(0, [2]*n+[0,0]+left, [3]+right)
            local_macros += 2
            steps += gap + finish
    drains = 0
    for size in range(8):
        for digits in itertools.product(range(2), repeat=size):
            current = list(digits)
            value = sum(d*2**i for i, d in enumerate(current))
            gap = 0
            while value:
                carry = next(i for i, d in enumerate(current) if d)
                current = [1]*carry + [0] + current[carry+1:]
                following = sum(d*2**i for i, d in enumerate(current))
                assert value == following + 1
                value = following
                gap += 4*carry+8
            gap += 3*size+7
            assert run(table, back(1, [0,0], [2*d for d in digits]+[1]), gap) == front(0, [2]*size+[0,0], [3])
            drains += 1
            steps += gap
    assert run(table, (0, [], 0, []), 9) == (0, [2,0,0], 0, [])
    assert run(table, back(1, [0,3], [1]), 7) != front(0, [0,3], [3])
    assert run(table, back(1, [0,0], []), 7) != front(0, [0,0], [3])
    assert local_macros == 7056 and drains == 255
    sources = [Path(__file__), Path(helper.__file__), ROOT / 'tools/generate_pipeline_examples.py']
    stable = dict(
        scope='Finite synthetic controls only; no proof credit.',
        rows=[dict(machine=MACHINE, code=sum(v * 17**i for i, v in enumerate(table)))],
        local_macros=local_macros, context_max_length=2,
        max_bits=7, drains=drains, includes_empty_bits=True, simulated_macro_steps=steps,
        source_sha256={str(p.relative_to(ROOT)): helper.sha(p) for p in sources},
        decrement='0^k2 -> 2^k0, binary value decreases by exactly1',
        decrement_cost='4*k+8', finish_cost='3*length+7',
        boundary='B scans the nearest of two zero cells; terminal1 on the right',
        negative_controls=['changed outer zero', 'absent terminal1'])
    if args.check:
        saved = json.loads(REPORT.read_text())
        assert all(saved[k] == v for k, v in stable.items())
        print('All double-zero rank macros and 255 countdowns replayed exactly.')
    else:
        if REPORT.exists():
            raise ValueError('Frozen native report exists; use --check')
        helper.exact(REPORT, dict(stable, seconds=round(time.monotonic() - start, 6)))
        print('Native double-zero rank controls passed; no proof credit.')


if __name__ == '__main__':
    main()
