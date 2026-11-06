#!/usr/bin/env python3
"""Meaningful boundary tests for untrusted worklist merging."""
import csv
import json
from pathlib import Path
import tempfile
import unittest

import merge_census_residuals as tool

A = '0RA---_------_------_------'
B = '1RA---_------_------_------'
C = '0RB---_------_------_------'


def row(machine, kind='unknown'):
    return {'kind': kind, 'machine': machine, 'ptr': '1'}


class MergeTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, name, rows):
        path = self.root / name
        with path.open('w') as stream:
            writer = csv.DictWriter(stream, ['kind', 'machine', 'ptr'], delimiter='\t')
            writer.writeheader()
            writer.writerows(rows)
        return path

    def execute(self, left, right, ledgers=None):
        lp, rp = self.write('left.tsv', left), self.write('right.tsv', right)
        ledger_paths = None
        if ledgers:
            ledger_paths = [self.write('ll.tsv', ledgers[0]), self.write('rl.tsv', ledgers[1])]
        result = tool.execute(lp, rp, self.root / 'merged', ledger_paths)
        with (self.root / 'merged.residual.tsv').open() as stream:
            output = list(csv.DictReader(stream, delimiter='\t'))
        return result, output

    def test_without_ledgers_retains_missing_unknowns(self):
        summary, rows = self.execute([row(A)], [row(B)])
        self.assertEqual(summary['unknown_rows'], 2)
        self.assertFalse(summary['intersection_authorized_by_equal_listed_ledger_sets'])
        by_machine = {r['machine']: r for r in rows}
        self.assertEqual(by_machine[A]['right_status'], 'missing')
        self.assertEqual(by_machine[B]['left_status'], 'missing')
        self.assertEqual(summary['kernel_credit'], 0)

    def test_verified_intersection_can_remove_resolved_identities(self):
        summary, rows = self.execute([row(A)], [row(B)],
                                    ([row(A), row(B, 'translated_cycle_candidate')],
                                     [row(A, 'translated_cycle_candidate'), row(B)]))
        self.assertEqual(rows, [])
        self.assertEqual(summary['unknown_rows'], 0)
        self.assertFalse(summary['coverage_proved'])
        self.assertTrue(summary['ledger_verification']['equal_listed_family_sets'])

    def test_changed_universe_same_size_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'universes differ'):
            self.execute([row(A)], [row(B)], ([row(A)], [row(B)]))
        self.assertFalse((self.root / 'merged.residual.tsv').exists())

    def test_pending_outside_popped_ledger_is_preserved(self):
        summary, rows = self.execute([row(A), row(B, 'pending')], [],
                                    ([row(A)], [row(A, 'translated_cycle_candidate')]))
        self.assertEqual(summary['pending_rows'], 1)
        self.assertEqual(summary['unknown_rows'], 0)
        self.assertEqual(rows[0]['kind'], 'pending')
        self.assertEqual(rows[0]['right_status'], 'missing')
        self.assertEqual(summary['ledger_verification']['pending_residual_identities_outside_ledgers'], [1, 0])

    def test_pending_dominates_unknown(self):
        summary, rows = self.execute([row(A, 'pending')], [row(A)],
                                    ([row(A, 'pending')], [row(A)]))
        self.assertEqual(summary['pending_rows'], 1)
        self.assertEqual(rows[0]['right_status'], 'unknown')

    def test_unknown_edge_status_is_preserved(self):
        summary, rows = self.execute([row(A)], [row(A, 'unknown_edge')],
                                    ([row(A)], [row(A, 'unknown_edge')]))
        self.assertEqual(summary['unknown_rows'], 1)
        self.assertEqual(rows[0]['kind'], 'unknown_edge')

    def test_duplicate_residual_and_ledger_rejected(self):
        with self.assertRaisesRegex(ValueError, 'duplicate residual'):
            self.execute([row(A), row(A)], [])
        with self.assertRaisesRegex(ValueError, 'duplicate ledger'):
            self.execute([row(A)], [row(A)], ([row(A), row(A)], [row(A)]))

    def test_missing_unknown_ledger_row_rejected(self):
        with self.assertRaisesRegex(ValueError, 'unknown residual identity missing'):
            self.execute([row(B)], [], ([row(A, 'translated_cycle_candidate')], [row(A, 'translated_cycle_candidate')]))

    def test_unknown_ledger_kind_cannot_drop_a_residual(self):
        with self.assertRaises(ValueError):
            self.execute([], [row(A)], ([row(A, 'unkown')], [row(A)]))

    def test_missing_unknown_residual_row_rejected(self):
        with self.assertRaisesRegex(ValueError, 'absent or inconsistent'):
            self.execute([], [], ([row(A)], [row(A)]))

    def test_malformed_rows_and_headers_rejected(self):
        for text in ['kind\tmachine\tptr\nunknown\tINVALID\t1\n',
                     'kind\tmachine\tptr\nunknown\t' + A + '\t0\n',
                     'kind\tmachine\tptr\nunknown\t' + A + '\t1\textra\n',
                     'kind\tmachine\tptr\tptr\nunknown\t' + A + '\t1\t1\n']:
            path = self.root / 'bad.tsv'
            path.write_text(text)
            with self.assertRaises(ValueError):
                tool.read_residual(path, 100)

    def test_row_cap_enforced(self):
        path = self.write('capped.tsv', [row(A), row(B)])
        with self.assertRaisesRegex(ValueError, 'row cap'):
            tool.read_residual(path, 1)


if __name__ == '__main__':
    unittest.main()
