"""Independent finite algebra, step and boundary controls for S069; no proof credit."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
from generate_pipeline_examples import codes

ROOT = Path(__file__).resolve().parents[1]
PREFIX = ROOT / 'research/burn23-s069-transducer'
MACHINE = '1LB2RA1LA1RB_2RB2LB3LB1RA'

def artifact(suffix):
    return PREFIX.with_name(PREFIX.name + '-' + suffix)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def parity(word):
    return sum(symbol == 2 for symbol in word) % 2

def crossing(q, p, symbol):
    # The four-state transducer, independent of the native TM step decoder.
    if symbol == 0:
        return q, 1-p
    if symbol == 3:
        return 1-q, p
    if q == 0:
        return 0, 1-p if symbol == 1 else p
    return (1-p if symbol == 1 else p), 1

def result(q, p, word):
    for symbol in word:
        q, p = crossing(q, p, symbol)
    return q

def step(table, conf):
    q, left, head, right = conf
    value = table[4*q+head]
    assert value != 16
    write, direction, q = value//4, bool(value & 2), value % 2
    if direction:
        return q, [write, *left], right[0] if right else 0, right[1:]
    return q, left[1:], left[0] if left else 0, [write, *right]

def invariant(conf):
    q, left, head, right = conf
    return (all(x in (1, 2) for x in left)
            and all(x in (1, 2, 3) for x in right)
            and result(q, parity(left), [head, *right]) == 0)

def reaches_A(table, conf):
    for count in range(65):
        if conf[0] == 0:
            return count
        if count < 64:
            conf = step(table, conf)
    raise AssertionError('B finite-left return control exhausted')

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    inp = artifact('native-input.json')
    data_in = json.loads(inp.read_text())
    assert data_in['machine'] == MACHINE
    frozen_frontier = ROOT / data_in['frontier_source']
    assert sha(frozen_frontier) == data_in['frontier_sha256']
    assert MACHINE in frozen_frontier.read_text().splitlines()
    table = codes(MACHINE)
    # Each local algebra equation is checked on the entire four-element domain.
    algebra_left = algebra_right = 0
    for q, head in itertools.product(range(2), range(4)):
        value = table[4*q+head]
        write, rightward, qn = value//4, bool(value & 2), value % 2
        if rightward:
            assert write in (1, 2)
            for p in range(2):
                assert crossing(q, p, head) == (qn, p ^ (write == 2))
                algebra_right += 1
        else:
            assert write in (1, 2, 3)
            assert crossing(*crossing(qn, 0, 0), write) == crossing(q, 0, head)
            algebra_left += 1
            for left_head, tail_parity in itertools.product((1, 2), range(2)):
                old_parity = tail_parity ^ (left_head == 2)
                after_left = crossing(qn, tail_parity, left_head)
                assert crossing(*after_left, write) == crossing(q, old_parity, head)
                algebra_left += 1
    lefts = [list(w) for n in range(data_in['maximum_left_length']+1)
             for w in itertools.product((1, 2), repeat=n)]
    rights = [list(w) for n in range(data_in['maximum_right_length']+1)
              for w in itertools.product((1, 2, 3), repeat=n)]
    all_steps = admitted = B0_returns = B_nonzero_returns = maximum_return = 0
    for q, left, head, right in itertools.product(range(2), lefts, range(4), rights):
        conf = q, left, head, right
        next_conf = step(table, conf)
        q1, l1, h1, r1 = next_conf
        assert all(x in (1, 2) for x in l1)
        assert all(x in (1, 2, 3) for x in r1)
        assert result(q, parity(left), [head, *right]) == result(q1, parity(l1), [h1, *r1])
        all_steps += 1
        if invariant(conf):
            assert invariant(next_conf)
            admitted += 1
            if q == 1 and head == 0:
                maximum_return = max(maximum_return, reaches_A(table, conf))
                B0_returns += 1
    for left, head, right in itertools.product(lefts, (1, 2, 3), rights):
        maximum_return = max(maximum_return, reaches_A(table, (1, left, head, right)))
        B_nonzero_returns += 1
    conf = 0, [], 0, []
    actual_visits = [0, 0]
    for _ in range(data_in['actual_blank_steps']):
        assert invariant(conf)
        actual_visits[conf[0]] += 1
        conf = step(table, conf)
    negatives = 0
    for left in ([], [1], [2, 2], [1, 2, 1, 2, 2]):
        conf = 1, left, 0, []
        assert not invariant(conf)
        for count in range(17):
            assert conf == (1, [2]*count+left, 0, [])
            conf = step(table, conf)
        negatives += 1
        conf = 0, left, 3, []
        assert not invariant(conf)
        assert step(table, conf) == (1, [1, *left], 0, [])
        negatives += 1
    for conf in ((1, [], 1, []), (1, [2], 2, []),
                 (0, [3], 0, []), (0, [], 0, [0])):
        assert not invariant(conf)
        negatives += 1
    assert invariant((1, [2], 1, []))
    assert invariant((1, [1, 2, 2], 2, []))
    assert invariant((0, [2], 3, [3]))
    sources = [Path(__file__), ROOT/'tools/generate_pipeline_examples.py']
    data = dict(scope='Finite algebra and native controls only; zero proof credit.',
                rows=[dict(machine=MACHINE, code=sum(v*17**i for i, v in enumerate(table)))],
                invariant='Left word is over {1,2}, right word has no zero, and the four-state crossing fold over head::right exits A.',
                left_algebra_cases=algebra_left, right_algebra_cases=algebra_right,
                all_one_step_controls=all_steps, admitted_one_step_controls=admitted,
                B_zero_nonblank_right_return_controls=B0_returns,
                B_nonzero_return_controls=B_nonzero_returns,
                maximum_observed_control_return=maximum_return,
                actual_blank_steps=data_in['actual_blank_steps'], actual_state_visits=actual_visits,
                negative_boundary_controls=negatives,
                inputs_sha256={str(p.relative_to(ROOT)): sha(p) for p in (inp, frozen_frontier)},
                source_sha256={str(p.relative_to(ROOT)): sha(p) for p in sources},
                checked_state_families=0, checked_instruction_families=0)
    report = artifact('native.json')
    if args.check:
        assert json.loads(report.read_text()) == data
    else:
        if report.exists():
            raise ValueError('Frozen native report exists; use --check')
        report.write_text(json.dumps(data, indent=2, sort_keys=True)+'\n')
    print(json.dumps({k: data[k] for k in ('left_algebra_cases', 'right_algebra_cases',
                                         'all_one_step_controls', 'admitted_one_step_controls',
                                         'B_nonzero_return_controls', 'maximum_observed_control_return')}), flush=True)

if __name__ == '__main__':
    main()
