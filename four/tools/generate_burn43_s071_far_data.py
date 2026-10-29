"""Losslessly render the compact S071 FAR witness as pure Coq finite tables.

This renderer supplies data, not proof evidence. The Coq checker validates all
closure obligations and concrete block computations. The large Coq literals
belong in the ignored build directory.
"""
from collections import defaultdict
import argparse
import hashlib
import json
from pathlib import Path

NAMESPACE = 'BBB24Burn43S071FAR'
WITNESS_SHA256 = '4d46c690dc0278af170837f5648bc141752f675ef5450c36d8f1bf20160f9259'
DATA_SHA256 = '60d0873c8710825c68dbfa75e0f3a9fbcad595c074a507b24a7150ba191248cf'


def shifted(native_id):
    assert type(native_id) is int and native_id >= 0
    return native_id + 1


def slot(q, native_r):
    assert type(q) is int and q in (0, 1)
    return 2 * shifted(native_r) + q


def flatten(node):
    if node is None:
        return {}
    left, value, right = node
    out = {2 * k: v for k, v in flatten(left).items()}
    out.update({2 * k + 1: v for k, v in flatten(right).items()})
    if value is not None:
        out[1] = value
    return out


def trie(items):
    """PositiveMap follows the low bit first; independently undo every tree."""
    items = dict(items)
    assert all(type(k) is int and k >= 1 for k in items)
    if not items:
        return None
    left = {k // 2: v for k, v in items.items() if k > 1 and k % 2 == 0}
    right = {k // 2: v for k, v in items.items() if k > 1 and k % 2 == 1}
    node = (trie(left), items.get(1), trie(right))
    assert flatten(node) == items
    return node


def render(node, value):
    if node is None:
        return 'PM.Leaf'
    left, item, right = node
    middle = 'None' if item is None else '(Some ' + value(item) + ')'
    return '(PM.Node ' + render(left, value) + ' ' + middle + ' ' + render(right, value) + ')'


def positive(k):
    assert type(k) is int and k > 0
    return str(k) + '%positive'


def positives(values):
    return '[' + ';'.join(positive(v) for v in values) + ']'


def grouped(rows, key, value):
    out = defaultdict(list)
    for row in rows:
        out[key(row)].append(value(row))
    return {k: sorted(set(v)) for k, v in out.items()}


def tables(data):
    assert data['kind'] == 'summary-FAR' and data['goal'] == 'spinout'
    assert data['mirrored'] is False and data['block_len'] == 2
    assert data['pending_h2_spinout_targets'] == []
    assert data['words'][0] == [0, 0]
    push = defaultdict(dict)
    for w, before, after in data['push']:
        assert shifted(before) not in push[shifted(w)]
        push[shifted(w)][shifted(before)] = shifted(after)
    out = {
        'words': {shifted(i): tuple(w) for i, w in enumerate(data['words'])},
        'h3': {shifted(c): (shifted(w), bool(q), shifted(r))
               for c, (w, q, r) in enumerate(data['h3'])},
        'push': dict(push),
        'h2': {slot(q, r): True for q, r in data['h2']},
        'retl': {slot(q, r): True for q, r in data['retl']},
        'pre3l': {shifted(c): True for c in data['pre3l']},
        'ret2': grouped(data['ret2'], lambda x: slot(x[0], x[1]),
                        lambda x: slot(x[2], x[3])),
        'ret3': grouped(data['ret3'], lambda x: shifted(x[0]),
                        lambda x: slot(x[1], x[2])),
        'pre32': grouped(data['pre32'], lambda x: shifted(x[0]),
                         lambda x: slot(x[1], x[2])),
        'pre33': grouped(data['pre33'], lambda x: shifted(x[0]),
                         lambda x: shifted(x[1])),
    }
    # Undo every identifier shift, grouping, and packed H2 node independently.
    assert sorted((w - 1, r - 1, rn - 1) for w, inner in out['push'].items()
                  for r, rn in inner.items()) == sorted(map(tuple, data['push']))
    assert sorted((k % 2, k // 2 - 1) for k in out['h2']) == sorted(map(tuple, data['h2']))
    assert sorted((k % 2, k // 2 - 1) for k in out['retl']) == sorted(map(tuple, data['retl']))
    assert sorted(k - 1 for k in out['pre3l']) == sorted(data['pre3l'])
    assert sorted((a % 2, a // 2 - 1, b % 2, b // 2 - 1)
                  for a, bs in out['ret2'].items() for b in bs) == sorted(map(tuple, data['ret2']))
    for name in ('ret3', 'pre32'):
        assert sorted((a - 1, b % 2, b // 2 - 1)
                      for a, bs in out[name].items() for b in bs) == sorted(map(tuple, data[name]))
    assert sorted((a - 1, b - 1) for a, bs in out['pre33'].items()
                  for b in bs) == sorted(map(tuple, data['pre33']))
    assert [out['words'][i + 1] for i in range(len(data['words']))] == list(map(tuple, data['words']))
    assert [(out['h3'][i + 1][0] - 1, int(out['h3'][i + 1][1]), out['h3'][i + 1][2] - 1)
            for i in range(len(data['h3']))] == list(map(tuple, data['h3']))
    return out


def render_data(data):
    ts = tables(data)
    types = {'words': '(nat * nat)%type', 'h3': 'h3row',
             'push': '(PM.t positive)', 'h2': 'unit', 'retl': 'unit', 'pre3l': 'unit',
             'ret2': '(list positive)', 'ret3': '(list positive)',
             'pre32': '(list positive)', 'pre33': '(list positive)'}
    values = {
        'words': lambda v: '(' + str(v[0]) + ',' + str(v[1]) + ')',
        'h3': lambda v: '(Row ' + positive(v[0]) + ' ' + str(v[1]).lower() + ' ' + positive(v[2]) + ')',
        'push': lambda inner: render(trie(inner), positive),
        'h2': lambda _: 'tt', 'retl': lambda _: 'tt', 'pre3l': lambda _: 'tt',
        'ret2': positives, 'ret3': positives, 'pre32': positives, 'pre33': positives,
    }
    source = ['(** Frozen original S071 FAR data; finite literals only. *)',
              'From Coq Require Import List PArith FSets.FMapPositive.',
              f'From {NAMESPACE} Require Import Sparse DataSchema.', 'Import ListNotations.',
              'Arguments PM.Leaf {A}.', 'Arguments PM.Node {A} _ _ _.', '']
    for name, table in ts.items():
        source += ['Definition data_' + name + ' : PM.t ' + types[name] + ' :=',
                   '  ' + render(trie(table), values[name]) + '.', '']
    source += ['Definition certificate : rawcert :=',
               '  Cert data_words data_h3 data_push data_h2 data_retl data_pre3l',
               '       data_ret2 data_ret3 data_pre32 data_pre33.', '']
    index = {}
    for c, (w, q, r) in enumerate(data['h3']):
        bucket = index.setdefault(w + 1, {})
        key = slot(q, r)
        assert key not in bucket
        bucket[key] = c + 1
    assert sum(map(len, index.values())) == len(data['h3'])
    assert all(data['h3'][c - 1] == [w - 1, key % 2, key // 2 - 1]
               for w, bucket in index.items() for key, c in bucket.items())
    source += ['(** Untrusted search index; every use must validate the found row. *)',
               'Definition nodeindex : PM.t (PM.t positive) :=',
               '  ' + render(trie(index), lambda inner: render(trie(inner), positive)) + '.', '']
    return '\n'.join(source)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--witness', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert hashlib.sha256(args.witness.read_bytes()).hexdigest() == WITNESS_SHA256
    source = render_data(json.loads(args.witness.read_text()))
    assert hashlib.sha256(source.encode()).hexdigest() == DATA_SHA256
    if args.output.exists() and args.output.read_text() != source:
        raise ValueError('Frozen generated Coq source differs: ' + str(args.output))
    if not args.output.exists():
        args.output.write_text(source)


if __name__ == '__main__':
    main()
