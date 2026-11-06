import csv
import tempfile
import unittest
from unittest.mock import patch
from pathlib import Path

from reduce_residuals import digest, reduce


class ReductionTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.source = self.root / 'residual.tsv'
        self.index = self.root / 'proof.tsv'
        self.out = self.root / 'remaining.tsv'
        self.machine = '0RB---_0LC---_0LD1RC_1RC1LD'

    def write(self, path, fields, rows):
        with path.open('w') as f:
            writer = csv.writer(f, delimiter='\t', lineterminator='\n')
            writer.writerow(fields)
            writer.writerows(rows)

    def setup_rows(self, kind='unknown'):
        self.write(self.source, ['kind', 'machine', 'ptr'], [[kind, self.machine, '4']])
        self.write(self.index, ['machine', 'ptr', 'theorem'], [[self.machine, '4', 'Proof.all_completions']])

    def run_reduce(self):
        return reduce(self.source, digest(self.source), [self.index], self.out)

    def test_exact_family_removed(self):
        self.setup_rows()
        result = self.run_reduce()
        self.assertEqual((result['removed'], result['remaining']), (1, 0))

    def test_pending_is_retained(self):
        self.setup_rows('pending')
        result = self.run_reduce()
        self.assertEqual((result['removed'], result['pending_retained']), (0, 1))

    def test_other_pointer_does_not_match(self):
        self.setup_rows()
        self.write(self.index, ['machine', 'ptr', 'theorem'], [[self.machine, '3', 'Proof.all_completions']])
        with self.assertRaisesRegex(ValueError, 'absent'):
            self.run_reduce()
        self.assertFalse(self.out.exists())

    def test_source_hash_failure_preserves_output(self):
        self.setup_rows()
        self.out.write_text('keep me')
        with self.assertRaisesRegex(ValueError, 'SHA256'):
            reduce(self.source, '0'*64, [self.index], self.out)
        self.assertEqual(self.out.read_text(), 'keep me')

    def test_duplicate_source_rejected(self):
        self.setup_rows()
        with self.source.open('a') as f:
            f.write(f'unknown\t{self.machine}\t4\n')
        with self.assertRaisesRegex(ValueError, 'Duplicate residual'):
            self.run_reduce()

    def test_overlapping_proofs_count_once(self):
        self.setup_rows()
        with self.index.open('a') as f:
            f.write(f'{self.machine}\t4\tAnother.proof\n')
        self.assertEqual(self.run_reduce()['removed'], 1)

    def test_typo_kind_rejected(self):
        self.setup_rows('unkown')
        with self.assertRaisesRegex(ValueError, 'kind'):
            self.run_reduce()

    def test_duplicate_index_rejected(self):
        self.setup_rows()
        with self.index.open('a') as f:
            f.write(f'{self.machine}\t4\tProof.all_completions\n')
        with self.assertRaisesRegex(ValueError, 'Duplicate proof'):
            self.run_reduce()

    def test_missing_and_ragged_columns_rejected(self):
        self.setup_rows()
        self.index.write_text('machine\tptr\ttheorem\n'+self.machine+'\t4\n')
        with self.assertRaisesRegex(ValueError, 'Ragged'):
            self.run_reduce()

    def test_source_hash_and_rows_share_one_snapshot(self):
        self.setup_rows()
        expected = digest(self.source)
        read = Path.read_bytes
        def mutate_after_read(path):
            data = read(path)
            if path == self.source:
                with path.open('a') as f:
                    f.write(f'unknown\t{self.machine}\t3\n')
            return data
        with patch.object(Path, 'read_bytes', mutate_after_read):
            result = reduce(self.source, expected, [self.index], self.out)
        self.assertEqual((result['source_rows'], result['remaining']), (1, 0))
        self.assertEqual(result['source_sha256'], expected)

    def test_index_hash_and_rows_share_one_snapshot(self):
        self.setup_rows()
        index_hash = digest(self.index)
        read = Path.read_bytes
        def mutate_after_read(path):
            data = read(path)
            if path == self.index:
                path.write_text('replaced concurrently')
            return data
        with patch.object(Path, 'read_bytes', mutate_after_read):
            result = self.run_reduce()
        self.assertEqual(result['removed'], 1)
        self.assertEqual(result['proof_indexes'][0]['sha256'], index_hash)

    def test_unterminated_quote_cannot_hide_an_unknown(self):
        self.setup_rows()
        self.source.write_text('kind\tmachine\tptr\tnote\n'
            f'unknown\t{self.machine}\t4\t"unterminated\n'
            f'unknown\t{self.machine}\t3\tsecond\n')
        with self.assertRaisesRegex(ValueError, 'Malformed TSV'):
            self.run_reduce()
        self.assertFalse(self.out.exists())

    def test_multiline_provenance_rejected(self):
        self.setup_rows()
        self.write(self.source, ['kind', 'machine', 'ptr', 'note'],
                   [['unknown', self.machine, '4', 'first\nsecond']])
        with self.assertRaisesRegex(ValueError, 'Multiline'):
            self.run_reduce()


if __name__ == '__main__':
    unittest.main()
