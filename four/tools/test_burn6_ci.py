"""Fast synthetic receipt/dispatch controls. These do not run Coq or prove BBB."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(os.environ.get('BURN6_CI_TEST_REPO',
                                       Path(__file__).resolve().parents[2])) / 'four/tools'))
import kernel_audit_cache_v3 as kernel
import replay_burn6_ci as replay


class ReceiptControls(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(dir='/tmp')
        self.root = Path(self.temp.name)
        self.build = self.root / 'four/build'
        self.build.mkdir(parents=True)
        self.base = {'runtime': {'version': 'test-runtime', 'executables': {}, 'plugins': {}},
                     'plugins': {}, 'graph': {}}
        for name, deps in [('Coq.Init.Prelude', []),
                           ('Base.Sound', ['Coq.Init.Prelude']),
                           ('Burn.Inventory0', ['Base.Sound']),
                           ('Burn.Inventory1', ['Base.Sound']),
                           ('Burn.Campaign', ['Burn.Inventory0', 'Burn.Inventory1'])]:
            source = self.build / (name.replace('.', '_') + '.v')
            source.write_text('synthetic ' + name)
            source.with_suffix('.vo').write_bytes(b'not a Coq object: ' + name.encode())
            self.base['graph'][name] = {'source': str(source),
                                       'source_sha256': kernel.digest(source),
                                       'object': str(source.with_suffix('.vo')),
                                       'object_sha256': kernel.digest(source.with_suffix('.vo')),
                                       'dependencies': deps}
        self.forbidden = {'Burn.Inventory0', 'Burn.Inventory1', 'Burn.Campaign'}
        self.prereqs = {'Coq.Init.Prelude', 'Base.Sound'}
        self.receipt = self.make_receipt('prerequisite', self.prereqs)

    def tearDown(self):
        self.temp.cleanup()

    def make_receipt(self, name, names, *, directory=None, parents=(), reused=()):
        directory = self.build if directory is None else directory
        directory.mkdir(parents=True, exist_ok=True)
        path = directory / (name + '.json')
        log = path.with_suffix('.log')
        checked = sorted(set(names) - set(reused))
        log.write_text(''.join('Checking library: ' + n + '\n' for n in checked)
                       + ''.join('Admitting library: ' + n + '\n' for n in sorted(reused))
                       + 'Modules were successfully checked\n')
        snap = copy.deepcopy(self.base)
        snap['graph'] = {n: snap['graph'][n] for n in names}
        data = {'schema': 1, 'result': 'passed',
                'kind': 'incremental' if parents else 'recursive',
                'parents': [{'path': str(p), 'sha256': kernel.digest(p)} for p in parents],
                'snapshot': snap, 'roots': sorted(names), 'checked_modules': checked,
                'reused_modules': sorted(reused), 'command': ['coqchk', *sorted(names)],
                'log': str(log), 'log_sha256': kernel.digest(log)}
        path.write_text(json.dumps(data))
        return path

    def validate(self, current=None, baseline=()):
        return replay.validate_current_receipts(kernel, self.build, set(baseline),
                                                self.base if current is None else current,
                                                self.forbidden, self.forbidden)

    def mutate_receipt(self, path, change):
        data = json.loads(path.read_text())
        change(data)
        path.write_text(json.dumps(data))

    def test_valid_current_run_coverage(self):
        self.assertEqual(self.validate(), [self.receipt])

    def test_changed_source_rejected(self):
        current = copy.deepcopy(self.base)
        current['graph']['Base.Sound']['source_sha256'] = 'different'
        with self.assertRaisesRegex(ValueError, 'do not cover'):
            self.validate(current)

    def test_changed_object_rejected(self):
        current = copy.deepcopy(self.base)
        current['graph']['Base.Sound']['object_sha256'] = 'different'
        with self.assertRaisesRegex(ValueError, 'do not cover'):
            self.validate(current)

    def test_changed_dependency_edge_rejected(self):
        current = copy.deepcopy(self.base)
        current['graph']['Base.Sound']['dependencies'] = []
        with self.assertRaisesRegex(ValueError, 'do not cover'):
            self.validate(current)

    def test_changed_runtime_rejected(self):
        current = copy.deepcopy(self.base)
        current['runtime']['version'] = 'different'
        with self.assertRaisesRegex(ValueError, 'do not cover'):
            self.validate(current)

    def test_changed_runtime_executable_rejected(self):
        current = copy.deepcopy(self.base)
        current['runtime']['executables']['coqchk'] = {'sha256': 'different'}
        with self.assertRaisesRegex(ValueError, 'do not cover'):
            self.validate(current)

    def test_changed_plugin_rejected(self):
        self.base['plugins']['p.cmxs'] = 'old'
        self.mutate_receipt(self.receipt, lambda d: d['snapshot']['plugins'].update({'p.cmxs': 'new'}))
        with self.assertRaisesRegex(ValueError, 'do not cover'):
            self.validate()

    def test_changed_receipt_log_rejected(self):
        self.receipt.with_suffix('.log').write_text('changed')
        with self.assertRaisesRegex(ValueError, 'log changed'):
            self.validate()

    def test_changed_parent_receipt_rejected(self):
        child = self.make_receipt('child', self.prereqs, parents=[self.receipt], reused=self.prereqs)
        self.mutate_receipt(self.receipt, lambda d: d.update({'extra': 'mutation'}))
        with self.assertRaisesRegex(ValueError, 'Parent receipt changed'):
            self.validate()

    def test_missing_checked_module_rejected(self):
        self.mutate_receipt(self.receipt, lambda d: d.update({'checked_modules': ['Base.Sound']}))
        with self.assertRaisesRegex(ValueError, 'disagrees with log'):
            self.validate()

    def test_missing_transitive_prerequisite_rejected(self):
        current = copy.deepcopy(self.base)
        current['graph']['New.Dependency'] = copy.deepcopy(current['graph']['Base.Sound'])
        current['graph']['Base.Sound']['dependencies'].append('New.Dependency')
        with self.assertRaisesRegex(ValueError, 'do not cover'):
            self.validate(current)

    def test_preexisting_receipt_excluded(self):
        with self.assertRaisesRegex(ValueError, 'do not cover'):
            self.validate(baseline={self.receipt})

    def test_explicit_partial_coverage_keeps_known_modules(self):
        current = copy.deepcopy(self.base)
        current['graph']['Base.Sound']['object_sha256'] = 'different'
        chosen = replay.validate_current_receipts(kernel, self.build, set(), current,
                                                  self.forbidden, self.forbidden,
                                                  require_complete=False)
        self.assertEqual(replay.covered_modules(kernel, current, chosen), {'Coq.Init.Prelude'})

    def test_no_current_receipts_requires_fresh_base_dependency_order(self):
        batch = replay.next_prerequisite_batch(self.base['graph'], self.prereqs, set(), 16)
        self.assertEqual(batch, ['Coq.Init.Prelude', 'Base.Sound'])

    def test_batch_size_bound(self):
        first = replay.next_prerequisite_batch(self.base['graph'], self.prereqs, set(), 1)
        second = replay.next_prerequisite_batch(self.base['graph'], self.prereqs, set(first), 1)
        self.assertEqual(first, ['Coq.Init.Prelude'])
        self.assertEqual(second, ['Base.Sound'])

    def test_batch_all_covered_is_empty(self):
        self.assertEqual(replay.next_prerequisite_batch(self.base['graph'], self.prereqs,
                                                       self.prereqs, 16), [])

    def test_batch_cycle_rejected(self):
        graph = copy.deepcopy(self.base['graph'])
        graph['Coq.Init.Prelude']['dependencies'] = ['Base.Sound']
        with self.assertRaisesRegex(ValueError, 'dependency cycle'):
            replay.next_prerequisite_batch(graph, self.prereqs, set(), 16)

    def test_batch_out_of_scope_dependency_rejected(self):
        with self.assertRaisesRegex(ValueError, 'out-of-scope dependency'):
            replay.next_prerequisite_batch(self.base['graph'], {'Base.Sound'}, set(), 16)

    def test_batch_unknown_scope_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Invalid prerequisite audit scope'):
            replay.next_prerequisite_batch(self.base['graph'], {'Missing.Module'}, set(), 16)

    def test_batch_invalid_size_rejected(self):
        with self.assertRaisesRegex(ValueError, 'batch size'):
            replay.next_prerequisite_batch(self.base['graph'], self.prereqs, set(), 0)

    def test_batch_excludes_campaign_wrappers(self):
        batch = replay.next_prerequisite_batch(self.base['graph'], self.prereqs, set(), 16)
        self.assertFalse(set(batch) & self.forbidden)

    def test_no_hidden_fresh_modules(self):
        with self.assertRaisesRegex(ValueError, 'declared modules'):
            replay.require_fresh_modules({'checked_modules': ['Base.Sound', 'Burn.Inventory0'],
                                          'reused_modules': []}, ['Base.Sound'])

    def test_no_missing_fresh_modules(self):
        with self.assertRaisesRegex(ValueError, 'declared modules'):
            replay.require_fresh_modules({'checked_modules': [], 'reused_modules': ['Base.Sound']},
                                          ['Base.Sound'])

    def test_no_duplicate_fresh_modules(self):
        with self.assertRaisesRegex(ValueError, 'declared modules'):
            replay.require_fresh_modules({'checked_modules': ['Base.Sound', 'Base.Sound'],
                                          'reused_modules': []}, ['Base.Sound'])

    def test_no_reused_fresh_modules(self):
        with self.assertRaisesRegex(ValueError, 'reused instead'):
            replay.require_fresh_modules({'checked_modules': ['Base.Sound'],
                                          'reused_modules': ['Base.Sound']}, ['Base.Sound'])

    def test_fresh_modules_ignores_safe_log_order(self):
        replay.require_fresh_modules({'checked_modules': ['Base.Sound', 'Coq.Init.Prelude'],
                                      'reused_modules': []}, ['Coq.Init.Prelude', 'Base.Sound'])

    def test_campaign_module_cache_rejected(self):
        self.make_receipt('unexpected-campaign', self.prereqs | {'Burn.Inventory0'})
        with self.assertRaisesRegex(ValueError, 'includes a new campaign module'):
            self.validate()

    def test_receipt_ancestry_outside_build_rejected(self):
        external = self.make_receipt('external', self.prereqs, directory=self.root / 'external')
        self.make_receipt('child', self.prereqs, parents=[external], reused=self.prereqs)
        with self.assertRaisesRegex(ValueError, 'escapes the local build'):
            self.validate()

    def test_incremental_without_parent_rejected(self):
        self.mutate_receipt(self.receipt, lambda d: d.update({'kind': 'incremental'}))
        with self.assertRaisesRegex(ValueError, 'lacks recursive ancestry'):
            self.validate()

    def test_receipt_toctou_rejected(self):
        check = kernel.ReceiptValidation()
        check.load(self.receipt)
        self.receipt.write_text(self.receipt.read_text() + ' ')
        with self.assertRaisesRegex(ValueError, 'changed during validation'):
            check.recheck()

    def test_actual_file_hash_changes_remove_coverage(self):
        current = copy.deepcopy(self.base)
        node = current['graph']['Base.Sound']
        Path(node['source']).write_text('changed source on disk')
        node['source_sha256'] = kernel.digest(node['source'])
        with self.assertRaisesRegex(ValueError, 'do not cover'):
            self.validate(current)

    def test_fresh_phase_positive(self):
        replay.require_fresh_phase({'checked_modules': ['Burn.Inventory0'], 'reused_modules': ['Base.Sound']},
                                   'Burn.Inventory0')

    def test_fresh_phase_zero_fresh_rejected(self):
        with self.assertRaisesRegex(ValueError, 'freshly check exactly'):
            replay.require_fresh_phase({'checked_modules': [], 'reused_modules': ['Burn.Inventory0']},
                                       'Burn.Inventory0')

    def test_fresh_phase_extra_fresh_rejected(self):
        with self.assertRaisesRegex(ValueError, 'freshly check exactly'):
            replay.require_fresh_phase({'checked_modules': ['Base.Sound', 'Burn.Inventory0'], 'reused_modules': []},
                                       'Burn.Inventory0')

    def test_fresh_phase_reused_root_rejected(self):
        with self.assertRaisesRegex(ValueError, 'reused instead'):
            replay.require_fresh_phase({'checked_modules': ['Burn.Inventory0'], 'reused_modules': ['Burn.Inventory0']},
                                       'Burn.Inventory0')

    def test_frozen_file_change_rejected(self):
        source = self.root / 'frozen.v'
        source.write_text('frozen')
        pins = {str(source): replay.digest(source)}
        replay.recheck_pins(pins)
        source.write_text('changed')
        with self.assertRaisesRegex(ValueError, 'frozen campaign input'):
            replay.recheck_pins(pins)


if __name__ == '__main__':
    unittest.main(verbosity=2)
