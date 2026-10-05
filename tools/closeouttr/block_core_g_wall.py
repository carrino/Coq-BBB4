#!/usr/bin/env python3
"""Reproduce the finite right-wall certificate in BlockCoreGReturnTr.v.

Discovery is untrusted: the Coq fw_check and terminal-shape lemmas replay
all edges and target configurations.  Words are nearest-first at each side.
"""
import argparse
from collections import deque
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / 'theories/Counters/BlockCoreGReturnTr.v'
BEGIN = '(* BEGIN GENERATED WALL CERTIFICATE *)\n'
END = '(* END GENERATED WALL CERTIFICATE *)'
WIDTH = 21
FRONTS = ('10100001010101011', '10101001010101011')
MARKER = '101010101001'
# Canonical full table 1LD0LB_1LC0RD_1LA0LC_1RB1RD.
TABLE = {
    (0, 0): (1, -1, 3), (0, 1): (0, -1, 1),
    (1, 0): (1, -1, 2), (1, 1): (0, 1, 3),
    (2, 0): (1, -1, 0), (2, 1): (0, -1, 2),
    (3, 0): (1, 1, 1), (3, 1): (1, 1, 3),
}


def mask(word):
    return sum(int(bit) << i for i, bit in enumerate(word))


def word(value):
    return [(value >> i) & 1 for i in range(WIDTH)]


def closure():
    guards = {mask(front) for front in FRONTS}
    todo = deque((value, q, 0) for value in sorted(guards) for q in (1, 3))
    inside = set()
    while todo:
        current = todo.popleft()
        if current in inside:
            continue
        inside.add(current)
        value, q, position = current
        read = (value >> position) & 1
        if (q, read) == (0, 0):
            bits = word(value)
            assert position >= 4
            assert ''.join(map(str, bits[position + 1:])) == MARKER
            assert bits[position - 3:position][::-1] == [1, 0, 1]
            continue
        write, direction, next_q = TABLE[q, read]
        next_value = value | (1 << position) if write else value & ~(1 << position)
        next_position = position + direction
        assert next_position < WIDTH, 'Unprotected right escape'
        if next_position < 0:
            guards.add(next_value)
            todo.extend((next_value, entry_q, 0) for entry_q in (1, 3))
        else:
            todo.append((next_value, next_q, next_position))
    return sorted(guards), sorted(inside)


def syms(bits):
    return '[' + ';'.join('S' + str(bit) for bit in bits) + ']'


def certificate():
    guards, inside = closure()
    lines = ['Definition bcg_guards:list(list Sym):=[',
             ';\n'.join(syms(word(value)) for value in guards) + '].',
             'Definition bcg_inside:list cconf:=[']
    configs = []
    for value, q, position in inside:
        bits = word(value)
        configs.append(f'(St{"ABCD"[q]},({syms(bits[:position][::-1])},'
                       f'S{bits[position]},{syms(bits[position + 1:])}))')
    lines.append(';\n'.join(configs) + '].')
    return '\n'.join(lines) + '\n', len(guards), len(inside)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    generated, guards, inside = certificate()
    source = DEST.read_text()
    before, rest = source.split(BEGIN, 1)
    current, after = rest.split(END, 1)
    if args.check:
        if current != generated:
            raise SystemExit('BlockCoreGReturnTr.v wall certificate is stale')
    else:
        DEST.write_text(before + BEGIN + generated + END + after)
    print(f'G wall certificate: {guards} boundary words, {inside} internal configurations')


if __name__ == '__main__':
    main()
