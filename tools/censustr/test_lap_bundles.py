#!/usr/bin/env python3
"""Import-scope and replay checks for instruction lap bundles."""
from pathlib import Path
import tempfile
import unittest

import gen_lap_bundles as gen


class LapBundleTests(unittest.TestCase):
    def test_import_adapters_are_reversible_and_idempotent(self):
        source = ('From BBB4.Machines.CountersTr Require Import LAPT_a LAPT_b.\n'
                  'From BBB4.Machines.CountersTr Require LAPQ_c.\n'
                  'Definition keep := LAPT_a.theorem.\n')
        mapping = {'LAPT_a':'BundleLAPT_000', 'LAPT_b':'BundleLAPT_000',
                   'LAPQ_c':'BundleLAPQ_000'}
        actual = gen.rewrite_imports(source,mapping)
        self.assertEqual(gen.original_imports(actual),source)
        self.assertEqual(gen.rewrite_imports(actual,mapping),actual)
        self.assertEqual(actual.count('Require Import BundleLAPT_000.'),1)
        self.assertNotIn('Module LAPT_',actual)
        self.assertIn('Import LAPT_a.',actual)
        self.assertNotIn('Import LAPQ_c.',actual)
        self.assertEqual(gen.staged_boards(actual),set(mapping))

    def test_unbundled_imports_stay_available(self):
        source = 'From BBB4.Machines.CountersTr Require Import Legacy LAPT_a.\n'
        actual = gen.rewrite_imports(source,{'LAPT_a':'BundleLAPT_000'})
        self.assertIn('From BBB4.Machines.CountersTr Require Import Legacy.',actual)
        self.assertEqual(gen.original_imports(actual),source)

    def test_local_notations_are_isolated_and_import_order_kept(self):
        with tempfile.TemporaryDirectory() as tmp:
            paths = [Path(tmp)/'LAPT_a.v',Path(tmp)/'LAPT_b.v']
            for path in paths:
                path.write_text('From Coq Require Import Arith List.\n'
                                'Local Notation x := 0.\n'
                                'From Coq Require Import Bool.\n'
                                'Lemma example : x = 0. Proof. reflexivity. Qed.\n')
            actual = gen.render_bundle(paths)
            self.assertEqual(actual.count('From Coq Require Arith List.'),1)
            self.assertIn('Module LAPT_a.\nImport Arith List.\nLocal Notation x := 0.\nImport Bool.',actual)
            self.assertIn('End LAPT_a.\n\nModule LAPT_b.',actual)
            self.assertEqual(actual.count('Proof. reflexivity. Qed.'),2)

    def test_check_refuses_corrupted_bundle(self):
        with tempfile.TemporaryDirectory() as tmp:
            boards = Path(tmp)/'boards'
            stages = Path(tmp)/'stages'
            boards.mkdir(); stages.mkdir()
            (boards/'LAPT_a.v').write_text('From Coq Require Import Arith.\nLemma ok : 0=0. Proof. reflexivity. Qed.\n')
            gen.generate(boards,stages,project=None)
            path = boards/'Bundles/BundleLAPT_000.v'
            path.write_text(path.read_text().replace('0=0','0=1'))
            with self.assertRaisesRegex(ValueError,'stale generated files'):
                gen.generate(boards,stages,check=True,project=None)


if __name__ == '__main__':
    unittest.main()
