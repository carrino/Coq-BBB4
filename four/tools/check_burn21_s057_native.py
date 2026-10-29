"""Independent full Python replay of S057's proposed permanent-B entry.

Native observations grant no proof credit. The formal package must recompute
the finite prefix in Coq and prove the infinite drift separately.
"""
import argparse
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path

from generate_pipeline_examples import codes

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / 'build/burn21-s057-drift'
INPUT = ROOT / 'research/burn21-s057-native-input.json'
REPORT = ROOT / 'research/burn21-s057-native.json'
ORIGIN = ROOT / 'research/burn21-s057-source-result.json'
CPP = ROOT / 'research/burn21-s057-source-probe.cpp'
MACHINE = '1LB2LB1RB1RA_1RB3LA3RA2LB'
STEPS = 2333909


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exact(path, value):
    text = json.dumps(value, indent=2, sort_keys=True)+'\n'
    if path.exists():
        assert path.read_text() == text, str(path)
    else:
        path.write_text(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    BUILD.mkdir(parents=True, exist_ok=True)
    raw = MACHINE.replace('_', '')
    table = [(int(raw[i]), -1 if raw[i+1] == 'L' else 1, ord(raw[i+2])-65) for i in range(0, 24, 3)]
    encoded = codes(MACHINE)
    assert encoded == [4*w+(2 if d == 1 else 0)+q for w, d, q in table]
    assert table[4] == (1, 1, 1) and all(w != 0 for w, _, _ in table)
    origin = json.loads(ORIGIN.read_text())
    assert origin['machine'] == MACHINE and origin['steps'] == STEPS and origin['right_blank_B_escape']
    sources = [Path(__file__), ROOT/'tools/generate_pipeline_examples.py', CPP, ORIGIN]
    manifest = dict(scope='Independent Python replay only; zero proof credit.', machine=MACHINE,
                    steps=STEPS, state_bound=4194304, checkpoint_stride=65536,
                    source_sha256={str(p.relative_to(ROOT)): sha(p) for p in sources})
    if args.check:
        assert json.loads(INPUT.read_text()) == manifest
    else:
        exact(INPUT, manifest)
    tape = {}
    q = head = left = 0
    right = -1
    last = [0, 0]
    visits, reads = Counter(), Counter()
    checkpoints = []
    first10000 = hashlib.sha256()
    for time in range(STEPS+1):
        symbol = tape.get(head, 0)
        visits[q] += 1
        reads[(q, symbol)] += 1
        last[q] = time
        if time < 10000:
            first10000.update(f'{time}:{q}:{head}:{symbol};'.encode())
        if time % 65536 == 0 or time == STEPS:
            checkpoints.append(dict(time=time, state=q, position=head,
                                    left=[tape.get(p, 0) for p in range(head-1, left-1, -1)],
                                    head=symbol,
                                    right=[tape.get(p, 0) for p in range(head+1, right+1)]))
        if q == 1 and head > right:
            assert symbol == 0 and time == STEPS
            break
        assert time < STEPS
        write, direction, target = table[4*q+symbol]
        tape[head] = write
        if left > right:
            left = right = head
        else:
            left, right = min(left, head), max(right, head)
        head += direction
        q = target
    assert (q, head, left, right, last) == (1, 13, -3327, 12, [2333908, 2333909])
    assert [left, right] == origin['nonzero_span'] and head == origin['position'] and last == origin['last_visits']
    assert len(tape) == right-left+1 == 3340
    final_left = [tape[p] for p in range(head-1, left-1, -1)]
    encoded_left = bytes(final_left)
    checkpoint_path = BUILD/'python-checkpoints.json'
    exact(checkpoint_path, dict(machine=MACHINE, checkpoints=checkpoints))
    data = dict(scope='Independent native confirmation only; zero state or instruction proof credit.',
                input_sha256=sha(INPUT), rows=[dict(machine=MACHINE, code=sum(v*17**i for i, v in enumerate(encoded)))],
                first_escape_time=STEPS, last_native_A_visit=last[0], final_state=q, final_position=head,
                nonzero_span=[left, right], final_left_length=len(final_left), final_head=0,
                final_right=[], final_left_sha256=hashlib.sha256(encoded_left).hexdigest(),
                final_left_runs=[[symbol, len(list(group))] for symbol, group in itertools.groupby(final_left)],
                state_visits=dict(visits), read_counts=[dict(state=q, symbol=s, count=n) for (q, s), n in sorted(reads.items())],
                first10000_transition_sha256=first10000.hexdigest(),
                checkpoint_path=str(checkpoint_path.relative_to(ROOT)), checkpoint_sha256=sha(checkpoint_path),
                checked_state_families=0, checked_instruction_families=0)
    data = json.loads(json.dumps(data))
    if args.check:
        assert json.loads(REPORT.read_text()) == data
    else:
        exact(REPORT, data)
    print(json.dumps({k: data[k] for k in ('first_escape_time', 'last_native_A_visit', 'final_state',
                                         'final_position', 'nonzero_span', 'final_left_length')}), flush=True)


if __name__ == '__main__':
    main()
