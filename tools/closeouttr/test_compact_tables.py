import re
import unittest
from unittest.mock import patch

import compact_tables as c


class CompactTablesTests(unittest.TestCase):
    def setUp(self):
        self.limit = patch.object(c, 'MIN_BYTES', 0)
        self.limit.start()
        self.addCleanup(self.limit.stop)

    @staticmethod
    def source(table):
        return ('From Coq Require Import List NArith.\nImport ListNotations.\n'
                'Definition certificate := ' + table + '.\n')

    def assert_roundtrip(self, source):
        packed = c.rewrite(source, 'CBT_TEST_00')
        self.assertIn(c.BEGIN, packed)
        self.assertEqual(c.rewrite(packed, 'CBT_TEST_00'), packed)
        self.assertEqual(re.sub(r'\s+', '', c.expand(packed)), re.sub(r'\s+', '', source))
        return packed

    def test_maps_and_gates_cross_chunk_boundaries(self):
        keys = [100000 + i * i for i in range(300)]
        pairs = '[' + '; '.join(f'({k}%positive, {i % 193})' for i, k in enumerate(keys)) + ']'
        gate = '[' + '; '.join(f'{k}%positive' for k in keys[::2]) + ']'
        packed = self.assert_roundtrip(self.source(pairs) + 'Definition gate := ' + gate + '.\n')
        self.assertIn('hfd_dphi', packed)
        self.assertIn('hfd_dgate', packed)

    def test_known_wire_format_and_chunk_restart(self):
        self.assertEqual(c.encode([(1, 1), (10, 255)]), ['10191ff'])
        self.assertEqual(c.decode(['10191ff'], True), [(1, 1), (10, 255)])
        chunks = c.encode([(i, None) for i in range(1, 130)])
        self.assertEqual(chunks[0], '1' * 128)
        self.assertEqual(chunks[1], '982')  # 129, relative to zero in a new chunk
        self.assertEqual(c.decode(chunks, False), [(i, None) for i in range(1, 130)])

    def test_N_decoder_requires_exact_definition(self):
        table = '[' + '; '.join(f'({1000+i}%positive, {i}%N)' for i in range(8)) + ']'
        source = c.NDECODE + '\n' + self.source('potential_decode ' + table)
        packed = c.rewrite(source, 'CBT_TEST_00')
        expected = source.replace('potential_decode ' + table, table.replace('%N', ''))
        self.assertEqual(re.sub(r'\s+', '', c.expand(packed)), re.sub(r'\s+', '', expected))
        altered = source.replace('N.to_nat(snd kv)', 'S(N.to_nat(snd kv))')
        self.assertEqual(c.rewrite(altered, 'CBT_TEST_00'), altered)

    def test_duplicate_or_unsorted_keys_stay_literal(self):
        for keys in [[1, 2, 3, 3, 4, 5, 6, 7], [8, 7, 6, 5, 4, 3, 2, 1]]:
            source = self.source('[' + '; '.join(f'{k}%positive' for k in keys) + ']')
            self.assertEqual(c.rewrite(source, 'CBT_TEST_00'), source)

    def test_rank_dictionary_overflow_stays_literal(self):
        source = self.source('[' + '; '.join(f'({i+1}%positive, {i})' for i in range(256)) + ']')
        self.assertEqual(c.rewrite(source, 'CBT_TEST_00'), source)

    def test_reject_truncated_and_invalid_payloads(self):
        for chunks, pairs in [(['8'], False), (['11'], True), (['100'], True),
                              (['0'], False), (['8888881'], False), (['1' * 129], False)]:
            with self.subTest(chunks=chunks, pairs=pairs), self.assertRaises(ValueError):
                c.decode(chunks, pairs)


if __name__ == '__main__':
    unittest.main()
