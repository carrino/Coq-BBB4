"""Finite S012 rightmost-marker and return controls; zero proof credit."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

from generate_pipeline_examples import codes

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / 'research/burn18-s012-rightmost-native.json'
MACHINE = '1LB0RA0LA0LB_3RB2RA2LB1LB'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def step(table, conf):
    q, left, head, right = conf
    value = table[4*q+head]
    assert value != 16
    write, direction, q = value//4, bool(value & 2), value % 2
    if direction:
        return q, [write, *left], right[0] if right else 0, right[1:]
    return q, left[1:], left[0] if left else 0, [write, *right]


def last_nonzero(word):
    return next((symbol for symbol in reversed(word) if symbol != 0), 0)


def inv(conf):
    q, _, head, right = conf
    last = last_nonzero([head, *right])
    return last == 1 or (q == 0 and last == 0)


def reaches_A(table, conf):
    for count in range(257):
        if conf[0] == 0:
            return count
        if count < 256:
            conf = step(table, conf)
    raise AssertionError('Finite return control exhausted')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    table = codes(MACHINE)
    contexts = [list(word) for size in range(4) for word in itertools.product(range(4), repeat=size)]
    admitted = zero_returns = maximum_return = 0
    for q, left, head, right in itertools.product(range(2), contexts, range(4), contexts):
        conf = q, left, head, right
        if inv(conf):
            assert inv(step(table, conf))
            admitted += 1
            if q == 1 and head == 0:
                maximum_return = max(maximum_return, reaches_A(table, conf))
                zero_returns += 1
    left_contexts = [list(word) for size in range(5) for word in itertools.product(range(4), repeat=size)]
    right_contexts = [list(word) for size in range(3) for word in itertools.product(range(4), repeat=size)]
    nonzero_returns = 0
    for left, head, right in itertools.product(left_contexts, (1, 2, 3), right_contexts):
        maximum_return = max(maximum_return, reaches_A(table, (1, left, head, right)))
        nonzero_returns += 1
    conf = 0, [], 0, []
    assert inv(conf)
    visits = [0, 0]
    for _ in range(4096):
        assert inv(conf)
        visits[conf[0]] += 1
        conf = step(table, conf)
    for left in ([], [1], [3, 2, 1]):
        conf = 1, left, 0, []
        assert not inv(conf)
        for count in range(17):
            assert conf == (1, [3]*count+left, 0, [])
            conf = step(table, conf)
    assert inv((1, [2, 3], 0, [3, 2, 1, 0, 0]))
    assert not inv((1, [], 1, [2, 0]))
    assert inv((0, [3, 1], 0, [0, 0]))
    assert not inv((1, [3, 1], 0, [0, 0]))
    sources = [Path(__file__), ROOT/'tools/generate_pipeline_examples.py']
    data = dict(scope='Finite native invariant and return controls only; zero proof credit.',
                rows=[dict(machine=MACHINE, code=sum(v*17**i for i, v in enumerate(table)))],
                invariant='Last nonzero of head::right is 1, or the entire suffix is zero and state is A.',
                one_step_context_max_length=3, admitted_one_step_controls=admitted,
                B_zero_marker_return_controls=zero_returns, B_nonzero_return_controls=nonzero_returns,
                maximum_observed_control_return=maximum_return, maximum_left_return_context=4,
                actual_blank_steps=4096, actual_state_visits=visits,
                negative_B_blank_tail_contexts=3, negative_B_blank_tail_steps=17,
                source_sha256={str(p.relative_to(ROOT)): sha(p) for p in sources},
                checked_state_families=0, checked_instruction_families=0)
    if args.check:
        assert json.loads(REPORT.read_text()) == data
    else:
        if REPORT.exists():
            raise ValueError('Frozen native report exists; use --check')
        REPORT.write_text(json.dumps(data, indent=2, sort_keys=True)+'\n')
    print(json.dumps({k: data[k] for k in ('admitted_one_step_controls', 'B_zero_marker_return_controls',
                                         'B_nonzero_return_controls', 'maximum_observed_control_return')}), flush=True)


if __name__ == '__main__':
    main()
