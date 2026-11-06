#!/usr/bin/env python3
"""Boundary tests of the untrusted nomination boundary, without Coq."""
import csv
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import probe_control_ranks as probe

COUNTER = '0RB---_0LC0RB_1LD1RD_1RB0LD'
EMPTY = '------_------_------_------'
LOOP = '0RA0RA_0RB0RB_0RC0RC_0RD0RD'
BAD_RANK = '0RA0RB_0RA0RB_------_------'


class ProbeTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)

    def tearDown(self):
        self.temp.cleanup()

    def write(self, machines):
        p = self.root / 'input.tsv'
        with p.open('w') as f:
            w = csv.writer(f, delimiter='\t')
            w.writerow(['kind', 'machine', 'ptr'])
            for machine in machines:
                w.writerow(['unknown', machine, '4'])
        return p

    def test_counter_has_early_valid_bounded_certificate(self):
        table = probe.parse(COUNTER)
        status, cert, _ = probe.nominate(table, 16)
        self.assertEqual(status, 'nominated')
        self.assertEqual(cert['anchor'], 1)
        self.assertEqual(cert['states'], (1, 2, 3))
        self.assertLessEqual(cert['width_upper'], 225592668)
        for q, rank in cert['cert'].items():
            for s in cert['states']:
                for h in (0, 1):
                    w, d, target = table[2 * s + h]
                    if s != q and target != q:
                        self.assertLess(rank['scale'] * probe.delta(rank['measure'], w, d, h)
                                        + rank['phi'][target], rank['phi'][s])

    def test_no_closed_tail_and_no_rank_are_distinct(self):
        self.assertEqual(probe.nominate(probe.parse(EMPTY), 2)[0], 'no_closed_control_tail')
        self.assertEqual(probe.nominate(probe.parse(BAD_RANK), 2)[0], 'target_no_decreasing_rank')

    def test_anchor_and_width_failures_retained(self):
        self.assertEqual(probe.nominate(probe.parse(COUNTER), 0)[0], 'anchor_not_reached')
        self.assertEqual(probe.nominate(probe.parse(LOOP), 0, width_limit=0)[0], 'width_gate')

    def test_positive_cycle_has_no_bellman_potential(self):
        self.assertIsNone(probe.potentials((0, 1), [(0, 1, 1), (1, 0, 0)]))
        self.assertEqual(probe.potentials((), []), {})

    def test_malformed_pointer_machine_and_width(self):
        p = self.root / 'bad.tsv'
        for text in [f'kind\tmachine\tptr\nunknown\t{COUNTER}\t0\n',
                     'kind\tmachine\tptr\nunknown\tINVALID\t4\n',
                     f'kind\tmachine\tptr\nunknown\t{COUNTER}\t4\textra\n',
                     f'kind\tmachine\tptr\nunknown\t{COUNTER}\n',
                     f'kind\tmachine\tptr\t\"optional\ncolumn\"\nunknown\t{COUNTER}\t4\tvalue\n',
                     f'kind\tmachine\tptr\tptr\nunknown\t{COUNTER}\t4\t4\n']:
            p.write_text(text)
            with self.assertRaises(ValueError):
                list(probe.validated_rows(p, 100))

    def test_duplicate_and_row_cap_fail_closed(self):
        p = self.write([COUNTER, COUNTER])
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            probe.run(p, self.root / 'output')
        self.assertFalse((self.root / 'output/control-nominations.json').exists())
        p = self.write([COUNTER, EMPTY])
        with self.assertRaisesRegex(ValueError, 'row cap'):
            list(probe.validated_rows(p, 1))

    def test_input_hash_checked_before_publishing(self):
        p = self.write([COUNTER])
        with self.assertRaisesRegex(ValueError, 'SHA256'):
            probe.run(p, self.root / 'output', expected_sha256='0' * 64)
        self.assertFalse((self.root / 'output/manifest.json').exists())

    def test_unterminated_quote_cannot_swallow_following_rows(self):
        path = self.root / 'quoted.tsv'
        path.write_text('kind\tmachine\tptr\tnote\nunknown\t' + COUNTER
                        + '\t4\t"unterminated\nunknown\t' + EMPTY + '\t4\tignored\n')
        with self.assertRaisesRegex(ValueError, 'strict TSV'):
            list(probe.validated_rows(path, 100))
        with self.assertRaises(ValueError):
            probe.run(path, self.root / 'output')
        self.assertFalse((self.root / 'output/manifest.json').exists())

    def test_embedded_newline_rejected_even_in_optional_field(self):
        for value in ['"first\nsecond"', '"first\rsecond"']:
            path = self.root / 'newline.tsv'
            path.write_text('kind\tmachine\tptr\tnote\nunknown\t' + COUNTER
                            + '\t4\t' + value + '\n')
            with self.assertRaisesRegex(ValueError, 'embedded newline'):
                list(probe.validated_rows(path, 100))

    def test_hash_and_parser_use_same_immutable_snapshot(self):
        path = self.write([COUNTER])
        original = path.read_bytes()
        alternative = original.replace(COUNTER.encode(), EMPTY.encode())
        real_rows = probe.validated_rows

        def mutate_during_parse(snapshot, maximum):
            self.assertIsInstance(snapshot, bytes)
            self.assertEqual(snapshot, original)
            path.write_bytes(alternative)
            try:
                yield from real_rows(snapshot, maximum)
            finally:
                path.write_bytes(original)

        with mock.patch.object(probe, 'validated_rows', mutate_during_parse):
            result = probe.run(path, self.root / 'output', anchor_fuel=16)
        self.assertEqual(result['unique_nominee_identities'], 1)
        self.assertEqual(result['input']['sha256'], probe.fingerprint(path)['sha256'])
        self.assertTrue(result['input_hash_and_rows_share_immutable_snapshot'])

    def test_changed_input_at_end_fails_before_publishing(self):
        path = self.write([COUNTER])
        original = path.read_bytes()
        real_rows = probe.validated_rows

        def mutate_during_parse(snapshot, maximum):
            path.write_bytes(original.replace(COUNTER.encode(), EMPTY.encode()))
            yield from real_rows(snapshot, maximum)

        with mock.patch.object(probe, 'validated_rows', mutate_during_parse):
            with self.assertRaisesRegex(ValueError, 'input changed'):
                probe.run(path, self.root / 'output', anchor_fuel=16)
        self.assertFalse((self.root / 'output/control-nominations.json').exists())

    def test_input_byte_cap_is_enforced(self):
        path = self.write([COUNTER])
        with mock.patch.object(probe, 'MAX_INPUT_BYTES', 10):
            with self.assertRaisesRegex(ValueError, 'byte cap'):
                probe.run(path, self.root / 'output')

    def test_all_rows_accounted_and_no_proof_credit(self):
        p = self.write([COUNTER, EMPTY])
        result = probe.run(p, self.root / 'output', anchor_fuel=16)
        self.assertEqual(result['rows_processed'], 2)
        self.assertEqual(result['unique_nominee_identities'], 1)
        self.assertEqual(result['kernel_credit'], 0)
        self.assertFalse(result['coverage_proved'])
        self.assertEqual(result['input']['sha256'], probe.fingerprint(p)['sha256'])
        with (self.root / 'output/outcomes.tsv').open() as f:
            rows = list(csv.DictReader(f, delimiter='\t'))
        self.assertEqual([r['status'] for r in rows], ['nominated', 'no_closed_control_tail'])
        nominations = json.loads((self.root / 'output/control-nominations.json').read_text())
        self.assertEqual(nominations[0]['source_index'], 0)


if __name__ == '__main__':
    unittest.main()
