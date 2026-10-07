#!/usr/bin/env python3
"""Regression and corruption checks for preserving the RepWL stage inventory."""
import csv
from pathlib import Path
import tempfile
import unittest

import gen_provtr_rw as gen
import rw_stored

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

    def test_stored_certificate_keeps_machine_and_checks_parameters(self):
        import json
        row = dict(stage=0, index=0, spec='0RB0RB_0LC0LC_0RD0RD_0LA0LA',
                   L=1, T=2, t=0, fuel=128, M=8)
        data = rw_stored.search(row)
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp)/'RW_00_0000.json'
            path.write_text(json.dumps(data))
            certs = gen.read_stored_certificates([row], tmp)
            files = gen.render_parts([row], certificates=certs)
            part = files['RWParts/ProvTr_RW_00_P000.v']
            self.assertIn(gen.tm_lambda('tm_rw00_0000', row['spec']), part)
            self.assertIn('rw_check_stored_tr_sound _ 1 2 0 8 ', part)
            self.assertIn('RWCerts/DataTr_RW_00_0000.v', files)
            data['t'] = 1
            path.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, 'parameters differ'):
                gen.read_stored_certificates([row], tmp)

    def test_stored_selection_preserves_wrappers_and_every_machine(self):
        certs = gen.read_stored_certificates(self.rows)
        before = gen.render_parts(self.rows)
        after = gen.render_parts(self.rows, certificates=certs)
        for path, text in before.items():
            if not path.startswith('RWParts/'):
                self.assertEqual(after[path], text)
                continue
            for match in gen.ROW_RE.finditer(text):
                self.assertIn(match[7], after[path])
                stage, index = int(match[8]), int(match[9])
                if (stage,index) not in certs:
                    self.assertIn(match[0], after[path])
                else:
                    data = certs[stage,index]
                    args = ' '.join(str(data[k]) for k in ['L','T','t','M'])
                    self.assertIn(f'rw_check_stored_tr_sound _ {args} ', after[path])


if __name__ == '__main__':
    unittest.main()
