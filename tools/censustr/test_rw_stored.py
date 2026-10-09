#!/usr/bin/env python3
"""Check lossless packing, failed corruption checks, and source replay."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

import rw_stored as s


class StoredTests(unittest.TestCase):
    def setUp(self):
        self.row = dict(spec='0RB0RB_0LC0LC_0RD0RD_0LA0LA', L=1, T=2,
                        t=0, fuel=128, M=8)
        self.data = s.search(self.row)

    def test_search_and_json_replay_agree(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp)/'data.json'
            path.write_text(json.dumps(self.data))
            self.assertEqual(s.render(s.read(path)), s.render(self.data))
        self.assertEqual(len(s.decoded(self.data)['keys']), 5)

    def test_corruption_is_detected(self):
        corrupt = copy.deepcopy(self.data)
        corrupt['rank_deltas'][0] += 1
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp)/'data.json'
            path.write_text(json.dumps(corrupt))
            with self.assertRaisesRegex(ValueError, 'digest mismatch'):
                s.read(path)

    def test_tables_cross_chunks_and_four_digit_ranks(self):
        keys = [2**180+i*137 for i in range(300)]
        ranks = list(range(1, 301))
        values = list(zip(keys, ranks))
        ki = {k:i+1 for i,k in enumerate(keys)}
        ri = {r:i+1 for i,r in enumerate(ranks)}
        packed = s.pack_table(values, ki, ri)
        self.assertEqual(len(packed), 3)
        self.assertEqual(s.unpack_table(packed, keys, ranks), [list(x) for x in values])
        self.assertEqual(s.unpack_table(s.pack_table(keys,ki), keys), keys)

    def test_truncated_or_oversized_payloads_fail(self):
        for bad in [['100'], ['10000'], ['888888'], ['10001'*129]]:
            with self.assertRaises((ValueError, IndexError)):
                s.unpack_table(bad, list(range(1, 201)), [1])
        with self.assertRaises(ValueError):
            s.totals([1,0])

    def test_coalescing_keeps_rank_boundaries_and_disjoint_potentials(self):
        rank = ['rank', [[10, 1]]]
        left = ['meas', 'N/L', 1, [[10, 2], [20, 99]], [10]]
        right = ['meas', 'N/L', 1, [[20, 3]], [20]]
        self.assertEqual(s.coalesce_measures([rank, left, right, rank]),
                         [rank, ['meas', 'N/L', 1, [[10, 2], [20, 3]], [10, 20]], rank])
        self.assertEqual(s.coalesce_measures([left, rank, right]), [left, rank, right])
        overlapping = ['meas', 'N/L', 1, [[10, 3]], [10]]
        self.assertEqual(s.coalesce_measures([left, overlapping]), [left, overlapping])

    def test_compacted_source_replays_and_is_idempotent(self):
        result = s.compact(self.data)
        self.assertEqual(result, s.compact(result))
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'compact.json'
            path.write_text(json.dumps(result))
            self.assertEqual(s.read(path), result)


if __name__ == '__main__':
    unittest.main()
