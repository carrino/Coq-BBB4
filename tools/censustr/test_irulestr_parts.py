#!/usr/bin/env python3
"""Guard instruction certificate coverage and the state-proof dependency cut."""
from pathlib import Path
import re
import tempfile
import unittest

import gen_irulestr_parts as gen


class IRulesPartsTests(unittest.TestCase):
    def test_complete_inventory_and_public_theorems(self):
        rows = gen.read_rows()
        outputs = gen.render()
        wrapper = outputs[gen.MACHINES / 'IRulesTr_Batch_01.v']
        expected = [f'irtr_{s}_never_quasihalts_tr' for s in rows]
        self.assertEqual(re.findall(r'^Theorem (\w+)', wrapper, re.M), expected)
        part_theorems = []
        for path, source in outputs.items():
            if path.parent.name == 'IRulesTrParts':
                part_theorems.extend(re.findall(r'^Theorem (\w+)', source, re.M))
                self.assertLessEqual(source.count('irules_check_neverqhtr_sound'), gen.CHUNK)
            self.assertNotRegex(source, r'Require[^.]*IRules_Batch_')
        self.assertEqual(part_theorems, expected)

    def test_data_are_verbatim_and_every_proof_rechecks(self):
        sources = gen.definitions()
        self.assertEqual(len(sources), 250)
        outputs = gen.render()
        for i, sid in enumerate(gen.read_rows()):
            part = gen.MACHINES / 'IRulesTrParts' / f'IRulesTrPart_{i // gen.CHUNK:02d}.v'
            self.assertIn(sources[sid], outputs[part])
            self.assertIn(f'irules_check_neverqhtr_sound tm_{sid} cert_{sid} 300000%nat', outputs[part])

    def test_missing_source_is_rejected(self):
        sources = gen.definitions()
        del sources[gen.read_rows()[0]]
        with self.assertRaises(KeyError):
            gen.render(sources=sources)

    def test_duplicate_and_missing_rows_are_rejected(self):
        rows = gen.read_rows()
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'rows.txt'
            for bad in [rows[:-1], rows[:-1] + rows[:1]]:
                path.write_text('\n'.join(bad))
                with self.assertRaises(ValueError):
                    gen.read_rows(path)

    def test_census_uses_only_instruction_proofs(self):
        source = (gen.REPO / 'theories/CensusTr/RunTr.v').read_text()
        self.assertNotIn('IRules_Batch_', source)
        self.assertIn('Require Import IRulesTr_Batch_01.', source)
        self.assertIn('exact prov_tr_all.', source)


if __name__ == '__main__':
    unittest.main()
