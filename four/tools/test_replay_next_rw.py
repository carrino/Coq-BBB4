"""Read-only integrity tests for frozen direct RW replay; no Coq process runs."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

import replay_next_rw as replay


class PortableRWReplayIntegrity(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.reference = json.loads(replay.DEFAULT_REPORT.read_text())

    def test_preflight_leaves_all_frozen_artifacts_unchanged(self):
        paths = {replay.DEFAULT_REPORT, replay.ROOT / replay.INPUT}
        for key in ('source_sha256', 'object_sha256', 'generated_sha256'):
            paths.update(replay.ROOT / name for name in self.reference[key])
        paths.add(replay.ROOT / self.reference['board_descriptor']['inventories'][0]['path'])
        before = {path: (replay.digest(path), path.stat().st_mtime_ns) for path in paths}
        plan = replay.prepare(replay.DEFAULT_REPORT)
        self.assertEqual(plan['count'], 32)
        self.assertEqual(len(plan['sources']), 33)
        self.assertEqual(before, {path: (replay.digest(path), path.stat().st_mtime_ns) for path in paths})

    def test_input_pin_tamper_rejected(self):
        frozen = copy.deepcopy(self.reference)
        frozen['queue_input_sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'Frozen input/source pin differs'):
            replay.prepare_document(frozen)

    def test_inventory_pin_tamper_rejected(self):
        frozen = copy.deepcopy(self.reference)
        frozen['board_input_sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'Frozen input/source pin differs'):
            replay.prepare_document(frozen)

    def test_implementation_pin_tamper_rejected(self):
        frozen = copy.deepcopy(self.reference)
        frozen['source_sha256']['tools/check_closure_wave.py'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'Frozen input/source pin differs'):
            replay.prepare_document(frozen)

    def test_missing_implementation_pin_rejected(self):
        frozen = copy.deepcopy(self.reference)
        del frozen['source_sha256']['tools/check_next_rw.py']
        with self.assertRaisesRegex(ValueError, 'omit a replay implementation dependency'):
            replay.prepare_document(frozen)

    def test_generated_pin_tamper_rejected(self):
        frozen = copy.deepcopy(self.reference)
        name = next(iter(frozen['generated_sha256']))
        frozen['generated_sha256'][name] = '0' * 64
        frozen['source_sha256'][name] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'Regenerated frozen source pin differs'):
            replay.prepare_document(frozen)

    def test_changed_accepted_order_rejected(self):
        frozen = copy.deepcopy(self.reference)
        frozen['attempts'][0], frozen['attempts'][1] = frozen['attempts'][1], frozen['attempts'][0]
        with self.assertRaisesRegex(ValueError, 'accepted inventory differs from the attempt ledger'):
            replay.prepare_document(frozen)

    def test_supplied_mode_rejected_clearly(self):
        frozen = copy.deepcopy(self.reference)
        frozen['method'] = 'supplied graph and ranking check'
        with self.assertRaisesRegex(ValueError, 'only direct rw_check reports are supported'):
            replay.prepare_document(frozen)

    def test_historical_runtime_is_not_required(self):
        frozen = copy.deepcopy(self.reference)
        frozen['object_sha256'] = {name: '0' * 64 for name in frozen['object_sha256']}
        frozen['audit_receipt'] = 'build/nonexistent-historical-receipt.json'
        frozen['audit_receipt_sha256'] = frozen['audit_log_sha256'] = '0' * 64
        self.assertEqual(replay.prepare_document(frozen)['count'], 32)

    def test_no_generated_objects_receipts_or_search_logs_required(self):
        original = replay.prepare_document(self.reference)
        with tempfile.TemporaryDirectory(prefix='next-rw-preflight-', dir=replay.ROOT / 'build') as temporary:
            root = Path(temporary)
            for name in original['protected']:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.symlink_to(replay.ROOT / name)
            plan = replay.prepare_document(self.reference, root=root)
            self.assertEqual(plan['count'], 32)
            self.assertFalse((root / 'build').exists())


if __name__ == '__main__':
    unittest.main()
