#!/usr/bin/env python3
"""Regenerate the core-M B1 binary-fold coefficient tables.

The integer certificate is stored in block_core_m_fold.json. Prefixes are
nearest-cell first and ordered lexicographically (000000 through 111111).
Each bias array is left-prefix major, right-prefix minor; the omitted B1
array is zero because the checker stops at that instruction.

Only the marked table definitions in BlockCoreMB1FoldDataTr.v are replaced.
Its handwritten finite checker and soundness lemmas are preserved. Coq's
bmf_*_checked lemmas verify the inequalities; no LP solver or floating-point
arithmetic is needed to reproduce or check these tables.
"""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DATA = Path(__file__).with_suffix('.json')
OUTPUT = ROOT / 'theories/Counters/BlockCoreMB1FoldDataTr.v'
BEGIN = '(* BEGIN GENERATED B1 BINARY-FOLD CERTIFICATE *)'
END = '(* END GENERATED B1 BINARY-FOLD CERTIFICATE *)'
QH = ('00', '01', '10', '20', '21', '30', '31')


def integer_array(value, size, label):
    if not isinstance(value, list) or len(value) != size:
        raise ValueError(f'{label}: expected {size} coefficients')
    if any(type(coefficient) is not int for coefficient in value):
        raise ValueError(f'{label}: coefficients must be integers')
    return value


def load_certificate(path):
    data = json.loads(path.read_text())
    metadata = {
        'format': 'bbb4-binary-fold-v1',
        'machine': '0LB1RD_1LC0LC_1RA1LA_1LA0RD',
        'prefix_bits': 6,
        'prefix_order': 'lexicographic bits, nearest cell first',
        'bias_order': 'left prefix major, right prefix minor',
        'omitted_instruction': 'B1',
    }
    if set(data) != set(metadata) | {'ls', 'rs', 'vl', 'vr', 'bias'}:
        raise ValueError('unexpected certificate fields')
    for key, value in metadata.items():
        if data[key] != value:
            raise ValueError(f'unsupported {key}: {data[key]!r}')
    for key, size in (('ls', 128), ('rs', 128), ('vl', 64), ('vr', 64)):
        integer_array(data[key], size, key)
    if not isinstance(data['bias'], dict) or set(data['bias']) != set(QH):
        raise ValueError('bias must contain exactly the seven non-B1 instructions')
    for key in QH:
        integer_array(data['bias'][key], 4096, f'bias[{key}]')
    return data


def coq_integer(value):
    return f'({value})' if value < 0 else str(value)


def tree(values, leaf=coq_integer):
    if len(values) == 1:
        return f'(BMFLeaf {leaf(values[0])})'
    middle = len(values) // 2
    return f'(BMFNode {tree(values[:middle], leaf)} {tree(values[middle:], leaf)})'


def render(data):
    lines = [BEGIN]
    for key, depth in (('ls', 7), ('rs', 7), ('vl', 6), ('vr', 6)):
        lines += [f'Definition bmf_{key}_data:bmf_tree Z {depth}:=',
                  tree(data[key]) + '.']
    for q in range(4):
        for h in range(2):
            key = f'{q}{h}'
            values = data['bias'].get(key, [0] * 4096)
            rows = [values[offset:offset + 64] for offset in range(0, 4096, 64)]
            lines += [f'Definition bmf_b{key}:bmf_tree(bmf_tree Z 6)6:=',
                      tree(rows, tree) + '.']
    lines.append(END)
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='fail if tables are stale')
    args = parser.parse_args()
    data = load_certificate(DATA)
    old = OUTPUT.read_text()
    if old.count(BEGIN) != 1 or old.count(END) != 1:
        raise SystemExit('expected exactly one marked B1 coefficient region')
    start, end = old.index(BEGIN), old.index(END)
    if start >= end:
        raise SystemExit('B1 coefficient markers are out of order')
    stop = end + len(END)
    new = old[:start] + render(data) + old[stop:]
    if args.check:
        if old != new:
            raise SystemExit('M B1 binary-fold certificate tables are stale')
        print('M B1 binary-fold certificate is current (28672 bias coefficients)')
    elif old != new:
        OUTPUT.write_text(new)
        print('Regenerated M B1 binary-fold coefficient tables')
    else:
        print('M B1 binary-fold coefficient tables are unchanged')


if __name__ == '__main__':
    main()
