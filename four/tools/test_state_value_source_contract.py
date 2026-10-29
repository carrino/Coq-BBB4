"""Source-only regressions. These tests never invoke Coq or native compilers."""
import copy
import hashlib
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

from proof24_common import (CORE_PINS, FE, Graph, TARGET, canonical, parse_assumptions,
                            receipt_key, receipt_valid, selected_statement_check, sha,
                            statement_check, write_json)
from proof24_resources import MIB, memory_snapshot, phase_limits
from build_state_value import check_dependencies

REPO = Path(__file__).resolve().parents[2]
REVIEW = Path(os.environ.get('STATE24_NEGATIVE_REVIEW', ''))


class Assumptions(unittest.TestCase):
    def test_standard_fe_and_closed(self):
        self.assertEqual(parse_assumptions('Closed under the global context\n'), [])
        self.assertEqual(parse_assumptions('Axioms:\n' + FE + '\n  : forall A, A = A\n'), [FE])

    def test_unicode_counterfeit_and_primitives_rejected(self):
        for output in ['Axioms:\nValue.α : Prop\n' + FE + '\n  : Prop\n',
                       'Axioms:\nValue.' + FE + '\n  : Prop\n',
                       'Axioms:\nPrimInt63.int : Set\n',
                       'Axioms:\nPArray.array : Set\n',
                       'Axioms:\nValue.α Value.β : Prop\n' + FE + '\n  : Prop\n',
                       'Axioms:\n', 'No assumption result']:
            with self.subTest(output=output), self.assertRaises(ValueError):
                parse_assumptions(output)

    def test_existing_actual_coq_fixture_logs_still_rejected(self):
        if not REVIEW.is_file():
            self.skipTest('Optional prior actual Coq fixture evidence is not installed')
        evidence = json.loads(REVIEW.read_text())
        seen = set()
        for row in evidence['actual_coq_negative_fixtures']:
            output = row['compile_log_tail']
            if 'Axioms:' in output:
                with self.subTest(name=row['fixture']), self.assertRaises(ValueError):
                    parse_assumptions(output)
                seen.add(row['fixture'])
        self.assertTrue({'counterfeit_fe', 'axiom', 'unicode_with_fe'} <= seen)

    def test_exact_statement_source(self):
        text = statement_check('BBB24.Value.BBB24_state_value', 'BBB24.Value')
        self.assertIn('From BBB24 Require Value.', text)
        self.assertNotIn('Require Import Value', text)
        self.assertIn(f'scoreN = {TARGET}%N', text)
        self.assertIn(f'score = N.to_nat {TARGET}%N', text)
        self.assertIn('(BBB24.Value.BBB24_state_value : BBB24.ValueSpec.BBB24_state_statement)', text)


class SourceGraph(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='proof24-contract-')
        self.base = Path(self.temp.name)
        self.tree = self.base / 'tree with spaces'
        for folder in ('four/theories', 'small/theories', 'four/build/final'):
            (self.tree / folder).mkdir(parents=True, exist_ok=True)
        for source in CORE_PINS:
            shutil.copyfile(REPO / source, self.tree / source)
        final = 'four/build/final/Final.v'
        (self.tree / final).write_text('(* Source-only fixture, deliberately no theorem. *)\n')
        order = list(CORE_PINS) + [final]
        self.spec = {'sources': {s: {'sha256': sha(self.tree / s)} for s in order},
            'compile_order': order, 'local_dependencies': {s: [] for s in order},
            'load_paths': [{'path': 'four/theories', 'namespace': 'BBB24'},
                           {'path': 'small/theories', 'namespace': 'SmallBB'},
                           {'path': 'four/build/final', 'namespace': 'BBB24FixtureFinal'}],
            'roots': [final],
            'pending_value_alias': {'qualified_final_theorem': 'BBB24FixtureFinal.Final.BBB24_state_value'}}
        self.spec['local_dependencies'][final] = list(CORE_PINS)
        self.path = self.base / 'manifest.json'

    def tearDown(self):
        self.temp.cleanup()

    def graph(self, spec=None):
        write_json(self.path, self.spec if spec is None else spec)
        return Graph(self.tree, self.path, sha(self.path))

    def test_valid_relative_graph_under_root_with_spaces(self):
        graph = self.graph()
        graph.verify_sources()
        graph.verify_no_unselected()
        graph.verify_empty_objects()
        self.assertEqual(graph.module['four/build/final/Final.v'], 'BBB24FixtureFinal.Final')

    def test_extra_selected_root_is_inside_full_recursive_report(self):
        extra = 'four/build/final/Exports.v'
        (self.tree / extra).write_text('(* Typed source-only fixture; no proof. *)\n')
        self.spec['sources'][extra] = {'sha256': sha(self.tree / extra)}
        self.spec['compile_order'].append(extra)
        self.spec['local_dependencies'][extra] = []
        self.spec['roots'].append(extra)
        graph = self.graph()
        text = selected_statement_check(graph, graph.final_constant, 'BBB24FixtureFinal.Final')
        self.assertIn('Require BBB24FixtureFinal.Exports.', text)
        self.assertNotIn('Require Import BBB24FixtureFinal.Exports', text)

    def test_model_namespace_shadowing_and_path_escape(self):
        for ns, path in [('Coq', 'four/build/final'),
                         ('BBB24.Claim', 'four/build/final'),
                         ('BBB24Other', '../outside'),
                         ('BBB24Other', '/outside'),
                         ('BBB24ValueReport', 'four/build/final'),
                         ('BBB24Other', 'four/build/state-value-report'),
                         ('BBB24Other', 'four/theories/nested')]:
            spec = copy.deepcopy(self.spec)
            spec['load_paths'][2] = {'path': path, 'namespace': ns}
            with self.subTest(namespace=ns, path=path), self.assertRaises(ValueError):
                self.graph(spec)

    def test_wrong_model_pin_missing_source_order_and_unselected(self):
        spec = copy.deepcopy(self.spec)
        spec['sources']['four/theories/Spec.v']['sha256'] = '0' * 64
        with self.assertRaises(ValueError):
            self.graph(spec)
        spec = copy.deepcopy(self.spec)
        spec['compile_order'].reverse()
        with self.assertRaises(ValueError):
            self.graph(spec)
        graph = self.graph()
        (self.tree / 'four/theories/Shadow.v').write_text('(* no theorem *)')
        with self.assertRaises(ValueError):
            graph.verify_no_unselected()

    def test_symlink_and_bare_object_rejected(self):
        graph = self.graph()
        obj = self.tree / 'four/theories/Spec.vo'
        obj.write_bytes(b'not a Coq object; freshness fixture only')
        with self.assertRaises(ValueError):
            graph.verify_empty_objects()
        obj.unlink()
        source = self.tree / 'four/build/final/Final.v'
        other = self.base / 'outside.v'
        other.write_text(source.read_text())
        source.unlink()
        source.symlink_to(other)
        with self.assertRaises(ValueError):
            graph.verify_sources()

    def test_resume_depends_on_object_runtime_dependencies_and_source(self):
        graph = self.graph()
        source = 'four/build/final/Final.v'
        dependencies = {s: {'object_sha256': 'a', 'inputs': {}} for s in CORE_PINS}
        key = receipt_key(graph, source, 'runtime-a', dependencies)
        obj, receipt = self.base / 'fixture.vo', self.base / 'receipt.json'
        obj.write_bytes(b'not a Coq object; receipt unit test only')
        write_json(receipt, {'inputs': key, 'object_sha256': sha(obj),
                            'object_bytes': obj.stat().st_size, 'compile_exit_code': 0})
        self.assertTrue(receipt_valid(receipt, key, obj))
        self.assertFalse(receipt_valid(receipt, receipt_key(graph, source, 'runtime-b', dependencies), obj))
        changed = copy.deepcopy(dependencies)
        changed['four/theories/Spec.v']['object_sha256'] = 'b'
        self.assertFalse(receipt_valid(receipt, receipt_key(graph, source, 'runtime-a', changed), obj))
        (self.tree / source).write_text('changed source\n')
        self.assertFalse(receipt_valid(receipt, receipt_key(graph, source, 'runtime-a', dependencies), obj))
        obj.write_bytes(b'changed object')
        self.assertFalse(receipt_valid(receipt, key, obj))

    def test_fresh_coqdep_receipt_requires_exact_graph_and_no_warnings(self):
        graph = self.graph()
        state = self.base / 'state'
        state.mkdir()
        runtime = {'binaries': {'coqdep': {'path': '/never-executed/coqdep'}}}
        lines = []
        for source in graph.order:
            obj = source[:-2] + '.vo'
            deps = ' '.join(d[:-2] + '.vo' for d in graph.deps[source])
            lines.append(f'{obj}: {source} {deps}')
        exact = '\n'.join(lines)
        def fake_execute(command, cwd, env, log, limits, timeout):
            Path(log).write_text(exact)
            return {'exit_code': 0}
        with patch('build_state_value.run_capped', side_effect=fake_execute):
            check_dependencies(graph, runtime, state, {}, 10)
        self.assertEqual(json.loads((state / 'dependency-check.json').read_text())['status'],
                         'fresh coqdep graph matched')
        exact += '\nWarning: missing library\n'
        with patch('build_state_value.run_capped', side_effect=fake_execute), self.assertRaises(ValueError):
            check_dependencies(graph, runtime, state, {}, 10)
        exact = '\n'.join(lines[:-1] + [lines[-1].split(':', 1)[0] + ':'])
        with patch('build_state_value.run_capped', side_effect=fake_execute), self.assertRaises(ValueError):
            check_dependencies(graph, runtime, state, {}, 10)


    def test_coqdep_project_is_rooted_at_tree_and_removed_after_success(self):
        graph = self.graph()
        state = self.base / 'state with spaces'
        state.mkdir()
        runtime = {'binaries': {'coqdep': {'path': '/never-executed/coqdep'}}}
        projects = []
        def inspect(command, cwd, env, log, limits, timeout):
            self.assertEqual(cwd, graph.tree)
            self.assertEqual(command[:2], ['/never-executed/coqdep', '-f'])
            self.assertEqual(len(command), 3)
            self.assertEqual(Path(command[2]).name, command[2])
            project = cwd / command[2]
            projects.append(project)
            self.assertEqual(project.parent, graph.tree)
            self.assertEqual(project.read_text(), (state / '_CoqProject.selected').read_text())
            lines = project.read_text().splitlines()
            self.assertEqual(lines[:len(graph.paths)],
                             [f"-Q {r['path']} {r['namespace']}" for r in graph.paths])
            self.assertEqual(lines[len(graph.paths):], graph.order)
            for source in lines[len(graph.paths):]:
                self.assertTrue((project.parent / source).is_file())
            Path(log).write_text('\n'.join(
                f"{source[:-2]}.vo: {source} " + ' '.join(d[:-2] + '.vo' for d in graph.deps[source])
                for source in graph.order))
        with patch('build_state_value.run_capped', side_effect=inspect):
            check_dependencies(graph, runtime, state, {}, 10)
        self.assertEqual(len(projects), 1)
        self.assertFalse(projects[0].exists())
        self.assertTrue((state / '_CoqProject.selected').is_file())
        self.assertTrue((state / 'dependency-check.json').is_file())

    def test_coqdep_root_project_removed_when_child_fails(self):
        graph = self.graph()
        state = self.base / 'state with spaces'
        state.mkdir()
        projects = []
        def fail(command, cwd, env, log, limits, timeout):
            projects.append(cwd / command[2])
            self.assertTrue(projects[0].is_file())
            Path(log).write_text('diagnostic child failed before graph output\n')
            raise RuntimeError('deliberate dependency child failure')
        runtime = {'binaries': {'coqdep': {'path': '/never-executed/coqdep'}}}
        with patch('build_state_value.run_capped', side_effect=fail):
            with self.assertRaisesRegex(RuntimeError, 'deliberate dependency child failure'):
                check_dependencies(graph, runtime, state, {}, 10)
        self.assertFalse(projects[0].exists())
        self.assertTrue((state / '_CoqProject.selected').is_file())
        self.assertTrue((state / 'coqdep.log').is_file())
        self.assertFalse((state / 'dependency-check.json').exists())

    def test_coqdep_still_rejects_unselected_sources_dependencies_and_coverage(self):
        graph = self.graph()
        runtime = {'binaries': {'coqdep': {'path': '/never-executed/coqdep'}}}
        lines = [f"{s[:-2]}.vo: {s} " + ' '.join(d[:-2] + '.vo' for d in graph.deps[s])
                 for s in graph.order]
        cases = {'source': '\n'.join(lines + ['outside.vo: outside.v']),
                 'dependency': '\n'.join(lines[:-1] + [lines[-1] + ' outside.vo']),
                 'coverage': '\n'.join(lines[:-1]),
                 'warning': '\n'.join(lines) + '\n*** Warning: missing library\n',
                 'error': '\n'.join(lines) + '\n*** Error: failure\n'}
        for name, output in cases.items():
            with self.subTest(name=name):
                state = self.base / ('state-' + name)
                state.mkdir()
                def emit(command, cwd, env, log, limits, timeout):
                    Path(log).write_text(output)
                with patch('build_state_value.run_capped', side_effect=emit):
                    with self.assertRaises(ValueError):
                        check_dependencies(graph, runtime, state, {}, 10)
                self.assertFalse((state / 'dependency-check.json').exists())
                self.assertFalse(list(graph.tree.glob('_CoqProject.selected.*')))


class Resources(unittest.TestCase):
    def test_cache_adjustment_excludes_shmem_dirty_and_writeback_and_bounds_host(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            (root / 'memory.max').write_text(str(16 * 1024 * MIB))
            (root / 'memory.current').write_text(str(15 * 1024 * MIB))
            (root / 'memory.stat').write_text('\n'.join(f'{k} {int(v * 1024 * MIB)}' for k, v in
                {'file': 14, 'shmem': 1, 'inactive_file': 6, 'active_file': 7,
                 'file_dirty': 0.25, 'file_writeback': 0.25}.items()))
            host = {'MemTotal': 64 * 1024 * MIB, 'MemAvailable': 12 * 1024 * MIB,
                    'MemFree': 1 * 1024 * MIB}
            with patch('proof24_resources.meminfo', return_value=host), patch('proof24_resources.cgroups', return_value=[root]):
                snap = memory_snapshot()
            self.assertEqual(snap['effective_limit_bytes'], 16 * 1024 * MIB)
            self.assertEqual(snap['cgroups'][0]['clean_file_cache_bytes'], int(12.5 * 1024 * MIB))
            self.assertEqual(snap['available_bytes'], 12 * 1024 * MIB)
            # A tmpfs-heavy group cannot pretend its shmem is reclaimable cache.
            (root / 'memory.stat').write_text('\n'.join(f'{k} {v * 1024 * MIB}' for k, v in
                {'file': 14, 'shmem': 14, 'inactive_file': 7, 'active_file': 7}.items()))
            with patch('proof24_resources.meminfo', return_value=host), patch('proof24_resources.cgroups', return_value=[root]):
                snap = memory_snapshot()
            self.assertEqual(snap['cgroups'][0]['clean_file_cache_bytes'], 0)
            self.assertEqual(snap['available_bytes'], 1 * 1024 * MIB)
            with self.assertRaises(ValueError):
                phase_limits('ordinary', 8, snap)

    def test_32gib_ordinary8_provider2_assembly1(self):
        snapshot = {'usable_bytes': 28 * 1024 * MIB}
        with patch('proof24_resources.os.cpu_count', return_value=8):
            self.assertEqual(phase_limits('ordinary', 8, snapshot)['workers'], 8)
            self.assertEqual(phase_limits('provider', 8, snapshot)['workers'], 2)
            self.assertEqual(phase_limits('assembly', 8, snapshot)['workers'], 1)

    def test_cgroup16_headroom_caps_and_refuses_oversubscription(self):
        with patch('proof24_resources.os.cpu_count', return_value=192):
            self.assertEqual(phase_limits('ordinary', 8, {'usable_bytes': 13 * 1024 * MIB})['workers'], 7)
            with self.assertRaises(ValueError):
                phase_limits('assembly', 8, {'usable_bytes': 10 * 1024 * MIB})

    def test_explicit_separate_as_rss_profile_for_measured_old_closure(self):
        snapshot = {'usable_bytes': 13 * 1024 * MIB, 'effective_limit_bytes': 16 * 1024 * MIB,
                    'reserve_bytes': 1536 * MIB}
        profiles = {'assembly': {'workers': 1, 'address_space_mib': 14336, 'rss_guard_mib': 12544}}
        limits = phase_limits('assembly', 8, snapshot, profiles)
        self.assertEqual(limits['address_space_bytes'], 14 * 1024 * MIB)
        self.assertEqual(limits['rss_guard_bytes'], 12544 * MIB)


if __name__ == '__main__':
    # Fail immediately if source-only checks accidentally try any external tool.
    with patch('subprocess.Popen', side_effect=AssertionError('External process forbidden in source-only tests')):
        unittest.main()
