"""Adversarial frozen-replay checks; never compile or kernel-audit proof objects."""
import contextlib
import copy
import io
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import check_burn2_timeout_states as replay


class Burn2TimeoutStateIntegrity(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.reference_path = replay.ROOT/'research/burn2-timeout-state-priority207-report.json'
        cls.reference = json.loads(cls.reference_path.read_text())

    def preflight(self, report=None, inventory_mutation=None):
        report = copy.deepcopy(self.reference if report is None else report)
        with tempfile.TemporaryDirectory(prefix='burn2-timeout-state-integrity-') as temporary:
            root = Path(temporary)
            protected = {name for name in report['source_sha256'] if not name.startswith('build/')}
            protected.update('tools/'+name for name in replay.TOOLS)
            protected.update(['research/burn2-timeout-state-input.json', 'research/next-timeout-input-v1.json',
                              'research/next-burndown-summary.json',
                              'research/next-timeout-burn2-rw128-v1-input.json',
                              'research/next-timeout-burn2-rw128-v1-summary.json',
                              'research/next-timeout-burn2-rw256-offset256-v1-input.json',
                              'research/next-timeout-burn2-rw256-offset256-v1-summary.json'])
            for name in protected:
                path = root/name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.symlink_to(replay.ROOT/name)
            inventory_name = self.reference['board_descriptor']['inventories'][0]['path']
            inventory_path = root/inventory_name
            inventory_path.write_bytes((replay.ROOT/inventory_name).read_bytes())
            if inventory_mutation:
                inventory = replay.load(inventory_path)
                inventory_mutation(inventory)
                replay.compact(inventory_path, inventory)
                report['board_input_sha256'] = replay.sha(inventory_path)
            report_path = root/'research/burn2-timeout-state-priority207-report.json'
            report_path.write_text(json.dumps(report))
            before = {p: (replay.sha(p), p.stat().st_mtime_ns)
                      for p in root.rglob('*') if p.is_file()}
            args = SimpleNamespace(batch='Priority207', start=0, limit=207, timeout=120,
                                   audit_timeout=2400, replay=False, check_only=True, output_dir=None)
            with patch.object(replay, 'ROOT', root), patch.object(replay, 'INPUT', root/'research/burn2-timeout-state-input.json'), \
                    patch.object(replay.timeout_queue, 'INPUT', root/'research/next-timeout-input-v1.json'), \
                    patch.object(replay, 'compile_source') as compile_mock, contextlib.redirect_stdout(io.StringIO()):
                replay.execute(args)
                compile_mock.assert_not_called()
            self.assertFalse((root/'build').exists())
            self.assertEqual(before, {p: (replay.sha(p), p.stat().st_mtime_ns) for p in before})

    def test_changed_priority_selection_rejected(self):
        data = replay.load(replay.INPUT)
        data['rows'][0]['state_already_checked'] = 'yes'
        with tempfile.TemporaryDirectory(prefix='burn2-timeout-selection-') as temporary:
            path = Path(temporary)/'input.json'
            replay.compact(path, data)
            with patch.object(replay, 'INPUT', path):
                with self.assertRaisesRegex(ValueError, 'Priority selection differs'):
                    replay.read_input()

    def test_duplicate_priority_selection_rejected(self):
        data = replay.load(replay.INPUT)
        data['rows'][1] = copy.deepcopy(data['rows'][0])
        with tempfile.TemporaryDirectory(prefix='burn2-timeout-selection-') as temporary:
            path = Path(temporary)/'input.json'
            replay.compact(path, data)
            with patch.object(replay, 'INPUT', path):
                with self.assertRaisesRegex(ValueError, 'Priority selection differs'):
                    replay.read_input()

    def test_fresh_preflight_needs_no_generated_objects_or_search_logs(self):
        self.preflight()

    def test_changed_inventory_pin_rejected(self):
        report = copy.deepcopy(self.reference)
        report['board_input_sha256'] = '0'*64
        with self.assertRaisesRegex(ValueError, 'Frozen pin differs'):
            self.preflight(report)

    def test_changed_inventory_with_updated_pin_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Frozen compact inventory differs'):
            self.preflight(inventory_mutation=lambda d: d['rows'].reverse())

    def test_changed_descriptor_bound_rejected(self):
        report = copy.deepcopy(self.reference)
        report['board_descriptor']['state_bound'] = 4097
        with self.assertRaisesRegex(ValueError, 'descriptor or attempt ledger'):
            self.preflight(report)

    def test_changed_state_count_rejected(self):
        report = copy.deepcopy(self.reference)
        report['new_state_families'] += 1
        with self.assertRaisesRegex(ValueError, 'descriptor or attempt ledger'):
            self.preflight(report)

    def test_changed_source_pin_rejected(self):
        report = copy.deepcopy(self.reference)
        report['source_sha256']['tools/check_closure_wave.py'] = '0'*64
        with self.assertRaisesRegex(ValueError, 'Frozen pin differs'):
            self.preflight(report)

    def test_missing_implementation_pin_rejected(self):
        report = copy.deepcopy(self.reference)
        del report['source_sha256']['tools/check_next_rw.py']
        with self.assertRaisesRegex(ValueError, 'implementation pins are incomplete'):
            self.preflight(report)

    def test_altered_generated_source_hash_rejected(self):
        report = copy.deepcopy(self.reference)
        name = next(iter(report['generated_sha256']))
        report['generated_sha256'][name] = '0'*64
        report['source_sha256'][name] = '0'*64
        with self.assertRaisesRegex(ValueError, 'generated-source inventory differs'):
            self.preflight(report)

    def test_unknown_attempt_status_rejected(self):
        report = copy.deepcopy(self.reference)
        report['attempts'][0]['status'] = 'candidate'
        with self.assertRaises(ValueError):
            self.preflight(report)

    def test_historical_runtime_objects_not_required(self):
        report = copy.deepcopy(self.reference)
        report['object_sha256'] = {'build/nonexistent.vo': '0'*64}
        report['audit_receipt'] = 'build/nonexistent-receipt.json'
        self.preflight(report)


if __name__ == '__main__':
    unittest.main()
