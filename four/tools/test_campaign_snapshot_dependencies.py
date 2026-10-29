"""Receipt compatibility controls; every compiler and kernel process is mocked."""
import contextlib
import copy
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

import check_campaign_next as original
import check_campaign_next_audit as adapter
import kernel_audit_cache_v3 as kernel
import replay_burn6_ci as replay
from campaign_snapshot_dependencies import snapshot_dependencies


class LocalProjection(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name) / 'repo'
        self.root = self.repo / 'four'
        self.paths = [(self.root / 'theories', 'Local'),
                      (self.repo / 'SmallBB', 'SmallBB'),
                      (self.root / 'build/campaign', 'Campaign')]

    def snapshot(self, embedded):
        coq = ((self.repo / '_opam') if embedded else
               (Path(self.temp.name) / 'external-opam')) / 'lib/coq/theories'
        return {'runtime': {'version': 'fixed'}, 'plugins': {}, 'graph': {
            'Campaign.Inventory': self.node(self.paths[2][0] / 'Inventory.v',
                                           ['Local.Nested.Sound', 'Coq.Lists.List']),
            'Local.Nested.Sound': self.node(self.paths[0][0] / 'Nested/Sound.v',
                                            ['SmallBB.Sound', 'Coq.Init.Prelude']),
            'SmallBB.Sound': self.node(self.paths[1][0] / 'Sound.v', []),
            'Coq.Lists.List': self.node(coq / 'Lists/List.v', ['Coq.Init.Prelude']),
            'Coq.Init.Prelude': self.node(coq / 'Init/Prelude.v', []),
            'Local.Unused': self.node(self.paths[0][0] / 'Unused.v', [])}}

    @staticmethod
    def node(source, dependencies):
        return {'source': str(source), 'source_sha256': source.stem + '-hash',
                'object': str(source.with_suffix('.vo')), 'object_sha256': 'object-hash',
                'dependencies': dependencies}

    def project(self, current):
        return snapshot_dependencies(current, 'Campaign.Inventory', self.paths, self.root)

    def test_embedded_and_external_opam_have_same_exact_local_closure(self):
        expected = {'build/campaign/Inventory.v': 'Inventory-hash',
                    'theories/Nested/Sound.v': 'Sound-hash', '../SmallBB/Sound.v': 'Sound-hash'}
        for embedded in (False, True):
            with self.subTest(embedded=embedded):
                current = self.snapshot(embedded)
                before = copy.deepcopy(current)
                self.assertEqual(self.project(current), expected)
                self.assertEqual(current, before)

    def test_broad_physical_mapping_does_not_admit_wrong_logical_library(self):
        self.paths.append((self.repo, 'Checkout'))
        self.assertNotIn('../_opam/lib/coq/theories/Lists/List.v',
                         self.project(self.snapshot(True)))

    def test_explicit_local_coq_namespace_is_retained(self):
        current = self.snapshot(True)
        source = self.root / 'local-coq/Sound.v'
        self.paths.append((source.parent, 'Coq.Custom'))
        current['graph']['Coq.Custom.Sound'] = self.node(source, [])
        current['graph']['Local.Nested.Sound']['dependencies'].append('Coq.Custom.Sound')
        self.assertEqual(self.project(current)['local-coq/Sound.v'], 'Sound-hash')

    def test_unmapped_compilation_root_is_rejected(self):
        current = self.snapshot(True)
        self.paths.pop()
        with self.assertRaisesRegex(ValueError, 'explicit local logical loadpath'):
            self.project(current)

    def test_mapping_outside_checkout_is_rejected(self):
        self.paths.append((Path(self.temp.name) / 'external', 'External'))
        with self.assertRaises(ValueError):
            self.project(self.snapshot(True))

    def test_local_source_changes_remain_visible(self):
        current = self.snapshot(True)
        before = self.project(current)
        current['graph']['SmallBB.Sound']['source_sha256'] = 'changed-source'
        self.assertNotEqual(self.project(current), before)

    def test_added_transitive_local_dependency_remains_visible(self):
        current = self.snapshot(True)
        before = self.project(current)
        current['graph']['SmallBB.Sound']['dependencies'].append('Local.Unused')
        self.assertNotEqual(self.project(current), before)

    def test_runtime_source_object_and_executable_changes_still_invalidate_kernel_reuse(self):
        baseline = self.snapshot(True)
        for field in ('source_sha256', 'object_sha256', 'runtime'):
            with self.subTest(field=field):
                current = copy.deepcopy(baseline)
                if field == 'runtime':
                    current['runtime']['version'] = 'changed'
                else:
                    current['graph']['Coq.Init.Prelude'][field] = 'changed'
                self.assertEqual(self.project(current), self.project(baseline))
                self.assertNotIn('Campaign.Inventory',
                                 kernel._covered(current, [{'snapshot': baseline}]))


class AuditReached(Exception):
    pass


class OriginalCheckerIntegration(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / 'repo/four'
        self.output = self.root / 'build/campaign'
        self.output.mkdir(parents=True)
        self.dependency = self.root / 'theories/Sound.v'
        self.dependency.parent.mkdir()
        self.dependency.write_text('synthetic local theorem source\n')
        self.manifest = self.root / 'manifest.json'
        self.manifest.write_text('{}')
        self.report = self.root / 'summary.json'
        self.compiler = 'synthetic Coq version\n'
        self.inventory_source = 'synthetic inventory source\n'
        self.aggregate_source = 'synthetic aggregate source\n'
        self.board = {'id': 'Inventory', 'rows': 1}
        self.paths = {'theories': 'Local'}
        self.inputs = {'manifest.json': original.sha(self.manifest)}
        self.compiled = {'runtime': {'version': 'fixed'}, 'plugins': {}, 'graph': {}}
        self.add_node('Local.Sound', self.dependency, ['Coq.Init.Prelude'])
        coq = self.root.parent / '_opam/lib/coq/theories/Init/Prelude.v'
        coq.parent.mkdir(parents=True)
        coq.write_text('synthetic runtime source\n')
        self.add_node('Coq.Init.Prelude', coq, [])
        for stem, source, deps in (
                ('Inventory', self.inventory_source, ['Local.Sound']),
                ('Campaign', self.aggregate_source, ['Test.Inventory'])):
            path = self.output / (stem + '.v')
            path.write_text(source)
            path.with_suffix('.vo').write_bytes(b'synthetic object ' + stem.encode())
            self.add_node('Test.' + stem, path, deps)
        for stem in ('Inventory', 'Campaign'):
            path = self.output / (stem + '.v')
            sources = [self.dependency, path]
            if stem == 'Campaign':
                sources.append(self.output / 'Inventory.v')
            receipt = {'source': original.sha(path), 'dependencies': self.local_hashes(sources),
                       'coq_version': self.compiler, 'vo_sha256': original.sha(path.with_suffix('.vo'))}
            path.with_suffix('.checked.json').write_text(json.dumps(receipt))

    def add_node(self, name, source, deps):
        self.compiled['graph'][name] = {
            'source': str(source), 'source_sha256': original.sha(source),
            'object': str(source.with_suffix('.vo')), 'object_sha256': 'synthetic-object-hash',
            'dependencies': deps}

    def local_hashes(self, sources):
        import os
        return {os.path.relpath(path, self.root): original.sha(path) for path in sources}

    def execute(self, use_adapter=True, reaches_audit=True):
        generated = [self.output / 'Inventory.v', self.output / 'Campaign.v']
        dependencies = self.local_hashes([self.dependency, *generated])
        self.report.write_text(json.dumps({'inputs': self.inputs,
                                         'source_sha256': dependencies, 'coq_version': self.compiler}))
        arguments = ['check_campaign_next_audit.py', '--audit-only', '--resume',
                     '--manifest', str(self.manifest), '--report', str(self.report),
                     '--output-dir', str(self.output), '--namespace', 'Test']
        loader = lambda *_: ({}, [self.board], dict(self.paths), dict(self.inputs))
        with contextlib.ExitStack() as stack:
            stack.enter_context(patch.object(original, 'ROOT', self.root))
            stack.enter_context(patch.object(original, 'load_manifest', side_effect=loader))
            stack.enter_context(patch.object(original, 'inventory_source', return_value=self.inventory_source))
            stack.enter_context(patch.object(original, 'aggregate_source', return_value=self.aggregate_source))
            stack.enter_context(patch.object(original, 'dependency_hashes', return_value=dependencies))
            stack.enter_context(patch.object(original, 'snapshot', return_value=self.compiled))
            stack.enter_context(patch.object(original, 'relevant_caches', return_value=[]))
            stack.enter_context(patch.object(original.resource, 'setrlimit'))
            stack.enter_context(patch.object(original.subprocess, 'check_output', return_value=self.compiler))
            run = stack.enter_context(patch.object(original.subprocess, 'run',
                                                  side_effect=AssertionError('A Coq process was started')))
            audit = stack.enter_context(patch.object(original, 'audit', side_effect=AuditReached))
            stack.enter_context(patch.object(sys, 'argv', arguments))
            stack.enter_context(contextlib.redirect_stdout(io.StringIO()))
            previous = original.snapshot_dependencies
            expected = AuditReached if reaches_audit else ValueError
            try:
                with self.assertRaises(expected):
                    (adapter.main if use_adapter else original.main)()
            finally:
                self.assertIs(original.snapshot_dependencies, previous)
            run.assert_not_called()
            return audit

    def test_original_checker_reproduces_embedded_opam_failure(self):
        # The frozen helper's ROOT is a separate module global.
        with patch('check_campaign_v2.ROOT', self.root):
            audit = self.execute(use_adapter=False, reaches_audit=False)
        audit.assert_not_called()

    def test_original_checker_external_opam_control_reaches_kernel_audit(self):
        source = Path(self.temp.name) / 'external-opam/Prelude.v'
        source.parent.mkdir()
        source.write_text('synthetic runtime source\n')
        self.compiled['graph']['Coq.Init.Prelude']['source'] = str(source)
        with patch('check_campaign_v2.ROOT', self.root):
            audit = self.execute(use_adapter=False)
        audit.assert_called_once()

    def test_adapter_reuses_exact_receipts_and_reaches_original_kernel_audit(self):
        audit = self.execute()
        audit.assert_called_once()
        self.assertEqual(audit.call_args.args[0], ['Test.Campaign'])
        self.assertEqual(len(self.compiled['graph']), 4)

    def test_changed_local_source_is_rejected_by_original_checker(self):
        self.dependency.write_text('changed local source\n')
        self.compiled['graph']['Local.Sound']['source_sha256'] = original.sha(self.dependency)
        with self.assertRaisesRegex(ValueError, 'Exact compilation receipt unavailable'):
            self.execute()

    def test_changed_object_is_rejected_by_original_checker(self):
        (self.output / 'Inventory.vo').write_bytes(b'changed object')
        with self.assertRaisesRegex(ValueError, 'Exact compilation receipt unavailable'):
            self.execute()

    def test_changed_generated_source_is_rejected_by_original_checker(self):
        self.inventory_source = 'changed generated inventory source\n'
        with self.assertRaisesRegex(ValueError, 'Exact compilation receipt unavailable'):
            self.execute()

    def test_added_local_dependency_is_rejected_by_original_checker(self):
        extra = self.dependency.with_name('NewDependency.v')
        extra.write_text('synthetic additional local dependency\n')
        self.add_node('Local.NewDependency', extra, [])
        self.compiled['graph']['Local.Sound']['dependencies'].append('Local.NewDependency')
        with self.assertRaisesRegex(ValueError, 'Exact compilation receipt unavailable'):
            self.execute()

    def test_changed_compiler_is_rejected_by_original_checker(self):
        self.compiler = 'changed compiler version\n'
        with self.assertRaisesRegex(ValueError, 'Exact compilation receipt unavailable'):
            self.execute()

    def test_adapter_requires_audit_only(self):
        with patch.object(sys, 'argv', ['check_campaign_next_audit.py']), \
                contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            adapter.main()


class CompatibilityToolPins(unittest.TestCase):
    def test_every_new_orchestration_tool_is_pinned_and_mutation_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            tools = repo / 'four/tools'
            tools.mkdir(parents=True)
            names = ('replay_burn6_ci.py', 'check_campaign_next_audit.py',
                     'campaign_snapshot_dependencies.py')
            for name in names:
                (tools / name).write_text('synthetic ' + name)
            report = repo / 'summary.json'
            report.write_text(json.dumps({'inputs': {}, 'source_sha256': {}}))
            plan = repo / 'plan.json'
            plan.write_text('{}')
            pins = replay.pinned_inputs(repo, report, plan)
            replay.recheck_pins(pins)
            for name in names:
                with self.subTest(tool=name):
                    path = tools / name
                    previous = path.read_text()
                    path.write_text('changed ' + name)
                    with self.assertRaisesRegex(ValueError, 'frozen campaign input'):
                        replay.recheck_pins(pins)
                    path.write_text(previous)


if __name__ == '__main__':
    unittest.main(verbosity=2)
