"""Finite controls for the unique-zero grammar; these controls are not proofs."""
import argparse
import hashlib
import itertools
import json
import time
from pathlib import Path
from generate_pipeline_examples import codes

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / 'research/burn17-zero-marker-native.json'
MACHINE = '1LB2LB0LB1RA_2RB2RA3LB0RA'


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


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


def checksum(word):
    return sum((symbol == 2) * 2**i for i, symbol in enumerate(word)) % 3


def allowed(word):
    if 0 not in word:
        return len(word) % 2 == 0 and all(s == 2 for s in word)
    at = word.index(0)
    return (len(word) % 2 == 1 and at + 1 < len(word)
            and all(s in (1, 2) for s in word[:at])
            and all(s == 2 for s in word[at + 1:]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    start = time.monotonic()
    table = codes(MACHINE)
    contexts = [list(p) for n in range(3) for p in itertools.product(range(4), repeat=n)]
    macros = 0
    for carry in range(8):
        for left, right in itertools.product(contexts, repeat=2):
            for head in range(3):
                assert run(table, (0, [2] * carry + [1] + left, head, right), 2 * carry + 2) == (
                    0, [1] * carry + [2] + left, (head + 1) % 3, right)
                assert run(table, (0, [2] * (carry + 1) + [0] + left, head, right), 2 * (carry + 1) + 2) == (
                    0, [1] * carry + [0, 2] + left, (head + 1) % 3, right)
                macros += 2
    outer_macros = 0
    for carry in range(1, 17):
        for head in range(3):
            assert run(table, (0, [2] * carry, head, []), 2 * carry + 2) == (
                0, [1] * (carry - 1) + [0, 2], (head + 1) % 3, [])
            outer_macros += 1
    main_configurations = steps = 0
    for pairs in range(1, 7):
        size = 2 * pairs
        for prefix_length in range(size):
            suffix_length = size - prefix_length
            for prefix in itertools.product((1, 2), repeat=prefix_length):
                word = list(prefix) + [0] + [2] * suffix_length
                head = checksum(word)
                assert allowed(word)
                if 1 in prefix:
                    carry = prefix.index(1)
                    following = [1] * carry + [2] + list(prefix[carry + 1:]) + [0] + [2] * suffix_length
                    gap, new_head = 2 * carry + 2, (head + 1) % 3
                elif prefix:
                    following = [1] * (prefix_length - 1) + [0] + [2] * (suffix_length + 1)
                    gap, new_head = 2 * prefix_length + 2, (head + 1) % 3
                else:
                    assert suffix_length % 2 == 0 and head == 0
                    following = [2] * (suffix_length + 2)
                    gap, new_head = 3, 0
                assert allowed(following) and checksum(following) == new_head
                assert run(table, (0, word, head, []), gap) == (0, following, new_head, [])
                main_configurations += 1
                steps += gap
    for pairs in range(9):
        word = [2] * (2 * pairs)
        assert checksum(word) == 0 and allowed(word)
        following = [1] * (2 * pairs - 1) + [0, 2] if pairs else [2, 2]
        gap, head = (4 * pairs + 2, 1) if pairs else (3, 0)
        assert allowed(following) and checksum(following) == head
        assert run(table, (0, word, 0, []), gap) == (0, following, head, [])
        main_configurations += 1
        steps += gap
    assert checksum([0, 2]) == 2 and not allowed([0, 2])
    assert run(table, (0, [0, 2], 2, []), 3) == (1, [2, 2, 2], 0, [])
    assert macros == 21168 and outer_macros == 48 and main_configurations == 5463
    sources = [Path(__file__), ROOT / 'tools/generate_pipeline_examples.py']
    stable = dict(
        scope='Finite synthetic controls only; no proof credit.',
        rows=[dict(machine=MACHINE, code=sum(v * 17**i for i, v in enumerate(table)))],
        source_sha256={str(p.relative_to(ROOT)): sha(p) for p in sources},
        grammar='2^(2*n), or p 0 2^b with p over1,2; b>0; length(p)+b even',
        checksum='head equals binary value of positions containing symbol2, modulo3',
        arbitrary_context_max_length=2, arbitrary_context_macros=macros,
        outer_carry_macros=outer_macros, marker_main_max_prefix_plus_suffix=12,
        main_configurations=main_configurations, simulated_main_steps=steps,
        excluded_seed=dict(left=[0, 2], head=2, steps=3, result_state='B', result_head=0,
                           result_left=[2, 2, 2], result_right=[]))
    if args.check:
        saved = json.loads(REPORT.read_text())
        assert all(saved[k] == v for k, v in stable.items())
        print('All unique-zero grammar and arbitrary-context controls replayed exactly.')
    else:
        if REPORT.exists():
            raise ValueError('Frozen native report exists; use --check')
        REPORT.write_text(json.dumps(dict(stable, seconds=round(time.monotonic() - start, 6)), indent=2, sort_keys=True) + '\n')
        print('Native unique-zero grammar controls passed; no proof credit.')


if __name__ == '__main__':
    main()
