#!/usr/bin/env python3
"""Tiny synthetic Python tests; these do not compile or prove Coq sources."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest

import gen_ladder_bundles as generator


class LadderBundleTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        self.boards = self.repo / generator.BOARD_DIRECTORY
        self.consumers = self.repo / generator.CONSUMER_DIRECTORY
        self.boards.mkdir(parents=True)
        self.consumers.mkdir(parents=True)
        self.originals = {}
        for name in ['LDRT_a', 'LDRT_b', 'LDRT_c', 'LDRQ_d']:
            source = ('From Coq Require Import List.\n'
                      'Local Notation hidden := (nil nat).\n'
                      f'Definition tm_{name} := hidden.\n'
                      f'Lemma proof_{name} : True. Proof. exact I. Qed.\n')
            (self.boards / (name + '.v')).write_text(source)
            self.originals[name] = source
        self.consumer('CBT_A_00', 'LDRT_a LDRT_b LDRQ_d')
        self.consumer('CBT_B_00', 'LDRT_c LDRQ_d')
        (self.repo / '_CoqProject').write_text('-Q theories BBB4\n')

    def consumer(self, name, boards, imported=False):
        source = ('From BBB4.Machines.LadderTr Require ' + ('Import ' if imported else '') +
                  boards + '.\nDefinition unchanged := 42.\n')
        (self.consumers / (name + '.v')).write_text(source)
        return source

    def generate(self, **kwargs):
        with contextlib.redirect_stdout(io.StringIO()):
            return generator.generate(self.repo, **kwargs)

    def snapshot(self):
        return {str(p.relative_to(self.repo)): (p.read_bytes(), p.stat().st_mtime_ns)
                for p in self.repo.rglob('*') if p.is_file()}

    def test_membership_union_and_determinism(self):
        groups, mapping, consumers, cohorts = generator.grouping(self.repo, 1)
        self.assertEqual(len(groups), 4)
        self.assertEqual(len(cohorts), 3)
        self.assertEqual(generator.grouping(self.repo, 1), (groups, mapping, consumers, cohorts))
        for path, names in consumers.items():
            actual = {p.stem for name in {mapping[x] for x in names} for p in groups[name]}
            self.assertEqual(actual, names)

    def test_exact_body_and_originals_preserved(self):
        self.generate()
        for name, source in self.originals.items():
            self.assertEqual((self.boards / (name + '.v')).read_text(), source)
        mapping = generator.read_bundle_map(self.repo)
        for name, source in self.originals.items():
            bundle = (self.boards / 'Bundles' / (mapping[name] + '.v')).read_text()
            body = source.replace('From Coq Require Import List.', 'Import List.')
            self.assertIn(f'Module {name}.\n{body}\nEnd {name}.\n', bundle)

    def test_replay_check_is_readonly_and_idempotent(self):
        self.generate()
        before = self.snapshot()
        self.generate()
        self.generate(check=True)
        self.assertEqual(self.snapshot(), before)

    def test_check_detects_missing_output_without_writing(self):
        before = self.snapshot()
        with self.assertRaisesRegex(ValueError, 'stale generated'):
            self.generate(check=True)
        self.assertEqual(self.snapshot(), before)

    def test_check_detects_changed_canonical_without_writing(self):
        self.generate()
        path = self.boards / 'LDRT_a.v'
        path.write_text(path.read_text() + '(* edit *)\n')
        before = self.snapshot()
        with self.assertRaisesRegex(ValueError, 'stale generated'):
            self.generate(check=True)
        self.assertEqual(self.snapshot(), before)

    def test_consumer_reversible_mixed_import_and_duplicate(self):
        source = self.consumer('CBT_A_00', 'LDRT_a LDRT_b OTHER_x', imported=True)
        source += 'From BBB4.Machines.LadderTr Require LDRT_a.\n'
        mapping = {'LDRT_a': 'BundleLDRT_0123456789ab_000',
                   'LDRT_b': 'BundleLDRT_0123456789ab_000'}
        rewritten = generator.rewrite_imports(source, mapping)
        self.assertEqual(generator.original_imports(rewritten), source)
        self.assertEqual(generator.rewrite_imports(rewritten, mapping), rewritten)
        self.assertEqual(rewritten.count('Require Import BundleLDRT_0123456789ab_000.'), 1)
        self.assertIn('From BBB4.Machines.LadderTr Require Import OTHER_x.', rewritten)
        self.assertIn('Import LDRT_a.', rewritten)
        self.assertIn('Import LDRT_b.', rewritten)

    def test_invalid_chunks(self):
        for value in [0, -1, 33, '32', True, 1.5]:
            with self.subTest(value=value), self.assertRaises(ValueError):
                generator.grouping(self.repo, value)

    def test_missing_and_unused_boards_rejected(self):
        self.consumer('CBT_C_00', 'LDRT_missing')
        with self.assertRaisesRegex(ValueError, 'missing canonical'):
            generator.grouping(self.repo)
        (self.consumers / 'CBT_C_00.v').unlink()
        (self.boards / 'LDRT_unused.v').write_text(self.originals['LDRT_a'])
        with self.assertRaisesRegex(ValueError, 'no supported consumer'):
            generator.grouping(self.repo)

    def test_stale_bundle_and_project_rejected(self):
        self.generate()
        stale = self.boards / 'Bundles/BundleLDRT_000000000000_999.v'
        stale.write_text('stale\n')
        with self.assertRaisesRegex(ValueError, 'unexpected old ladder bundles'):
            self.generate()
        stale.unlink()
        with (self.repo / '_CoqProject').open('a') as stream:
            stream.write('theories/Machines/LadderTr/Bundles/BundleLDRT_000000000000_999.v\n')
        with self.assertRaisesRegex(ValueError, 'unexpected old ladder bundle entries'):
            self.generate()

    def test_invalid_inventory(self):
        self.generate()
        path = self.boards / 'Bundles/boards.tsv'
        valid = path.read_text()
        for bad in [valid + valid.splitlines()[0] + '\n', 'LDRT_a\tbad\n', 'LDRT_a\n', '']:
            path.write_text(bad)
            with self.assertRaises(ValueError):
                generator.read_bundle_map(self.repo)

    def test_unsupported_import_and_adapter_rejected(self):
        for source in ['From BBB4.Machines.LadderTr Require Export LDRT_a.\n',
                       '(* LADDER BUNDLE IMPORT: broken *)\n']:
            with self.assertRaises(ValueError):
                generator.imported_boards(source)

    def test_unreviewed_scope_and_require_rejected(self):
        path = self.boards / 'LDRT_a.v'
        for command in ['Set Implicit Arguments.\n', 'Module Surprise.\n', 'Require Import Bool.\n']:
            path.write_text(self.originals['LDRT_a'] + command)
            with self.assertRaises(ValueError):
                generator.render_bundle([path])

    def test_missing_mapping_and_crlf_rejected(self):
        with self.assertRaisesRegex(ValueError, 'missing bundle mapping'):
            generator.rewrite_imports('From BBB4.Machines.LadderTr Require LDRT_a.\n', {})
        path = self.boards / 'LDRT_a.v'
        path.write_bytes(self.originals['LDRT_a'].replace('\n', '\r\n').encode())
        with self.assertRaisesRegex(ValueError, 'noncanonical source bytes'):
            generator.render_bundle([path])


if __name__ == '__main__':
    unittest.main()
