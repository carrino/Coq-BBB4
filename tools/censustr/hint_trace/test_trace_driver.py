"""Typed packet parser regressions, including one retained native packet.

These tests do not invoke Coq or regenerate hints.
"""
import unittest
import fcntl
import os
import tempfile
from unittest.mock import patch
from pathlib import Path
import trace_driver as driver


class TypedPacketCases(unittest.TestCase):
    def test_complete_inventory(self):
        text = '''= TrInventoryV1 96 10 200 3 4096 13
          (TrIndicesConsV1 10 (TrIndicesConsV1 106 TrIndicesNilV1))
          : TraceInventoryPacketV1'''
        packet = driver.parse_inventory(text)
        driver.validate_inventory_packet(packet, {'unit': 10})
        self.assertEqual(packet['indices'], [10, 106])

    def test_complete_typed_rows_and_scopes(self):
        text = '''= TrShardV1 96 10 106 200 true true 2
          (TrRowsConsV1 (123%positive) 8
            (TrRowsConsV1 (456)%positive 37 TrRowsNilV1))
          : BBB4HintTrace.TraceWalkTr.TraceShardPacketV1'''
        packet = driver.parse_shard(text)
        self.assertEqual(packet['rows'], [(123, 8), (456, 37)])
        self.assertEqual(packet['row_count'], 2)

    def test_empty_successful_shard(self):
        packet = driver.parse_shard(
            '= TrShardV1 96 10 10 100 true true 0 TrRowsNilV1 : TraceShardPacketV1')
        self.assertEqual(packet['rows'], [])

    def test_typed_positive_constructors(self):
        packet = driver.parse_shard('''
            = TrShardV1 96 10 586 1792 true true 3
              (TrRowsConsV1 (BinNums.xO (BinNums.xI BinNums.xH)) 20
                (TrRowsConsV1 BinNums.xH 0
                  (TrRowsConsV1 (xI (xO (xI xH))) 37 TrRowsNilV1)))
              : TraceShardPacketV1''')
        self.assertEqual(packet['rows'], [(6, 20), (1, 0), (13, 37)])
        decimal = driver.parse_shard('''= TrShardV1 96 10 586 1792 true true 3
          (TrRowsConsV1 6%positive 20 (TrRowsConsV1 1%positive 0
            (TrRowsConsV1 13%positive 37 TrRowsNilV1))) : TraceShardPacketV1''')
        self.assertEqual(packet['rows'], decimal['rows'])
        for value in ('(BinNums.xO 1)', '(BinNums.xI BinNums.xO)',
                      '(xO xH xH)', '(xI xO xH)',
                      '(BinNums.xO (S BinNums.xH))',
                      '(' + 'BinNums.xO (' * 65 + 'BinNums.xH' + ')' * 66):
            with self.subTest(value=value), self.assertRaises(ValueError):
                driver.parse_shard(f'''= TrShardV1 96 10 586 1792 true true 1
                  (TrRowsConsV1 {value} 20 TrRowsNilV1) : TraceShardPacketV1''')

    def test_actual_native_nonempty_packet(self):
        # Real exit-zero native stdout retained from the initial failed
        # decimal-only parse. This test does not change that run's status.
        raw = (Path(__file__).parent / 'fixtures/native-shard-586.stdout').read_text()
        packet = driver.parse_shard(raw)
        self.assertEqual(packet['index'], 586)
        self.assertEqual(packet['row_count'], 177)
        self.assertTrue(packet['present'] and packet['complete'])
        self.assertEqual(packet['rows'][0][1], 20)
        rows = driver.validated_rows(packet['rows'], Path(__file__).resolve().parents[3])
        self.assertEqual(len(rows), 177)

    def test_reject_partial_or_mistyped_output(self):
        malformed = [
            '= TrShardV1 96 10 10 100 true true 1 (TrRowsConsV1 123%positive 8',
            '= TrShardV1 96 10 10 100 true true 0 ... : TraceShardPacketV1',
            '= [123%positive; 8%positive] : list positive',
            '= TrShardV1 96 10 10 100 true true 2 (TrRowsConsV1 123 8 TrRowsNilV1) : TraceShardPacketV1',
            '= TrShardV1 96 10 10 100 true true 0 TrRowsNilV1 : TraceShardPacketV1\n'
            '= TrShardV1 96 10 10 100 true true 0 TrRowsNilV1 : TraceShardPacketV1',
        ]
        for text in malformed:
            with self.subTest(text=text), self.assertRaises(ValueError):
                driver.parse_shard(text)

    def test_reject_incomplete_and_wrong_shards(self):
        manifest = {'unit': 10, 'inventory': {'frontier_count': 200, 'indices': [10, 106]}}
        packet = {'units': 96, 'unit': 10, 'index': 106, 'frontier_count': 200,
                  'present': True, 'complete': True}
        driver.validate_shard_packet(packet, manifest, 106)
        for field, value in [('present', False), ('complete', False), ('index', 107),
                             ('frontier_count', 201), ('unit', 11), ('units', 95)]:
            with self.subTest(field=field), self.assertRaises(ValueError):
                driver.validate_shard_packet(dict(packet, **{field: value}), manifest, 106)

    def test_reject_partial_inventory(self):
        packet = {'units': 96, 'unit': 10, 'frontier_count': 200, 'levels': 3,
                  'rounds': 4096, 'pop_exponent': 13, 'indices': [10]}
        with self.assertRaises(ValueError):
            driver.validate_inventory_packet(packet, {'unit': 10})

    def test_rows_are_sorted_deduplicated_and_conflicts_rejected(self):
        with patch.object(driver, 'decoder', return_value=lambda key: str(key)):
            self.assertEqual(driver.validated_rows([(2, 4), (1, 8), (2, 4)], Path('.')),
                             [[1, 8], [2, 4]])
            for rows in [[(1, 4), (1, 5)], [(1, 38)], [(0, 1)], [(17**8 + 1, 1)]]:
                with self.subTest(rows=rows), self.assertRaises(ValueError):
                    driver.validated_rows(rows, Path('.'))


class CompilerLockCases(unittest.TestCase):
    def test_standalone_acquires_exclusively_and_closes(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'lock'
            with patch.object(driver.fcntl, 'flock', wraps=fcntl.flock) as flock:
                with driver.compiler_lock(path) as held:
                    self.assertEqual(os.fstat(held).st_ino, path.stat().st_ino)
                    flock.assert_called_once()
                    self.assertEqual(flock.call_args.args[0].fileno(), held)
                    self.assertEqual(flock.call_args.args[1], fcntl.LOCK_EX)
                with self.assertRaises(OSError):
                    os.fstat(held)

    def test_inherited_descriptor_is_duplicated_without_flock_or_unlock(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'lock'
            with path.open('a') as outer:
                fcntl.flock(outer, fcntl.LOCK_EX)
                with patch.object(driver.fcntl, 'flock', side_effect=AssertionError('nested flock')):
                    with driver.compiler_lock(path, outer.fileno()) as held:
                        self.assertNotEqual(held, outer.fileno())
                        self.assertEqual(os.fstat(held).st_ino, os.fstat(outer.fileno()).st_ino)
                    self.assertEqual(os.fstat(outer.fileno()).st_ino, path.stat().st_ino)

    def test_inherited_wrong_file_is_rejected_without_touching_original(self):
        with tempfile.TemporaryDirectory() as directory:
            expected = Path(directory) / 'expected'
            expected.touch()
            with (Path(directory) / 'other').open('a') as outer:
                with self.assertRaisesRegex(ValueError, 'does not identify'):
                    with driver.compiler_lock(expected, outer.fileno()):
                        self.fail('wrong descriptor accepted')
                self.assertNotEqual(os.fstat(outer.fileno()).st_ino, expected.stat().st_ino)


if __name__ == '__main__':
    unittest.main()
