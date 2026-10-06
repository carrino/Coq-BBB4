#!/usr/bin/env python3
"""Regression and corruption checks for preserving the RepWL stage inventory."""
import csv
from pathlib import Path
import tempfile
import unittest

import gen_provtr_rw as gen

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent


class StageSplitTests(unittest.TestCase):
    def setUp(self):
        self.rows = gen.read_manifest(HERE / 'provtr_rw_stages.tsv')

    def test_every_original_check_preserved(self):
        generated = gen.render_parts(self.rows)
        found = []
        for path, text in sorted(generated.items()):
            if not path.startswith('RWParts/'):
                continue
            for match in gen.ROW_RE.finditer(text):
                spec, *params = match.groups()[:6]
                definition, stage, index = match.groups()[6:9]
                self.assertEqual(tuple(params), match.groups()[9:])
                self.assertEqual(definition, gen.tm_lambda(f'tm_rw{stage}_{index}', spec))
                found.append(dict(zip(gen.FIELDS,
                    [int(stage), int(index), spec, *map(int, params)])))
        self.assertEqual(found, self.rows)
        self.assertEqual(len(found), 1462)

    def test_heavy_checks_are_independent(self):
        for n in sorted(set(r['stage'] for r in self.rows)):
            rows = [r for r in self.rows if r['stage'] == n]
            parts = gen.split_rows(rows, 10, 100000, 9)
            self.assertEqual([r for p in parts for r in p], rows)
            for part in parts:
                self.assertLessEqual(len(part), 10)
                if any(r['fuel'] >= 100000 or r['L'] >= 9 for r in part):
                    self.assertEqual(len(part), 1)

    def test_manifest_rejects_missing_reordered_and_duplicate_rows(self):
        corruptions = [self.rows[1:], self.rows[1:2]+self.rows[:1]+self.rows[2:]]
        duplicate = [dict(r) for r in self.rows]
        duplicate[1]['spec'] = duplicate[0]['spec']
        corruptions.append(duplicate)
        for rows in corruptions:
            with tempfile.TemporaryDirectory() as tmp:
                path = Path(tmp) / 'bad.tsv'
                with path.open('w') as out:
                    writer = csv.DictWriter(out, gen.FIELDS, delimiter='\t')
                    writer.writeheader()
                    writer.writerows(rows)
                with self.assertRaises(ValueError):
                    gen.read_manifest(path)

    def test_replay_detects_corrupt_proof_parameter(self):
        with tempfile.TemporaryDirectory() as tmp:
            manifest = HERE / 'provtr_rw_stages.tsv'
            gen.split_stages(manifest, tmp, 10, 100000, 9, False, None)
            part = next((Path(tmp)/'RWParts').glob('*.v'))
            part.write_text(part.read_text().replace('rw_tier_tr_sound _ ',
                                                    'rw_tier_tr_sound _ 999 ', 1))
            with self.assertRaises(ValueError):
                gen.split_stages(manifest, tmp, 10, 100000, 9, True, None)


if __name__ == '__main__':
    unittest.main()
