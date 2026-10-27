"""Portable weighted replay integrity checks; no proof artifacts are modified."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

import replay_next_weighted_state as replay


class PortableReplayIntegrity(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.reference = json.loads((replay.ROOT /
            'research/next-weighted-state-pilot-checked.json').read_text())

    def prepare_copy(self, frozen):
        with tempfile.TemporaryDirectory(prefix='next-weighted-state-test-') as directory:
            path = Path(directory) / 'frozen.json'
            path.write_text(json.dumps(frozen))
            return replay.prepare(path)

    def test_input_pin_tamper_rejected(self):
        frozen = copy.deepcopy(self.reference)
        frozen['inputs'][replay.BUNDLE] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'Frozen input/source pin differs'):
            self.prepare_copy(frozen)

    def test_implementation_pin_tamper_rejected(self):
        frozen = copy.deepcopy(self.reference)
        frozen['source_sha256']['tools/check_next_weighted_state.py'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'Frozen input/source pin differs'):
            self.prepare_copy(frozen)

    def test_missing_implementation_pin_rejected(self):
        frozen = copy.deepcopy(self.reference)
        del frozen['source_sha256']['tools/check_next_weighted_state.py']
        with self.assertRaisesRegex(ValueError, 'omit a replay implementation dependency'):
            self.prepare_copy(frozen)

    def test_generated_source_pin_tamper_rejected(self):
        frozen = copy.deepcopy(self.reference)
        frozen['source_sha256']['build/next-weighted-state/pilot/WeightedState0000.v'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'Regenerated frozen source pin differs'):
            self.prepare_copy(frozen)

    def test_inventory_pin_tamper_rejected(self):
        frozen = copy.deepcopy(self.reference)
        frozen['inventory_sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'Frozen accepted IDs differ'):
            self.prepare_copy(frozen)

    def test_historical_runtime_is_not_a_portability_requirement(self):
        frozen = copy.deepcopy(self.reference)
        frozen['object_sha256'] = {name: '0'*64 for name in frozen['object_sha256']}
        frozen['coq_version'] = 'A different historical compiler build'
        frozen['audit_seconds'] = 0
        frozen['compile_seconds'] = {'old timing': 0}
        plan = self.prepare_copy(frozen)
        self.assertEqual(plan['frozen']['selected_rows'], 8)


if __name__ == '__main__':
    unittest.main()
