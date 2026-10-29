"""Frozen replay contract regressions using isolated temporary inputs."""
from copy import deepcopy
import hashlib
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import check_burn2_capacity as replay


class FrozenContractTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.base = self.root / 'build/burn2-capacity'
        self.output = self.root / 'build/isolated'
        for name, value in [('ROOT', self.root), ('BASE', self.base)]:
            context = patch.object(replay, name, value)
            context.start()
            self.addCleanup(context.stop)
        registry = self.root / 'research/registry.json'
        registry.parent.mkdir()
        registry.write_text('{"rows": 1}\n')
        self.registry = registry
        self.inputs = {'research/registry.json': hashlib.sha256(registry.read_bytes()).hexdigest()}
        self.board = {'id': 'sample', 'scope': 'both', 'rows': 1, 'instruction_bound': 4096,
                      'exact_inventory_theorem': 'Sample.inventory_exact',
                      'proof_source': 'build/burn2-capacity/inventory-proof/Sample.v'}
        self.frozen = {'inputs_sha256': self.inputs, 'boards': [self.board]}

    def test_output_location_is_portable(self):
        replay.validate_published_inputs(self.frozen)
        moved = {**self.board, 'proof_source': 'build/isolated/inventory-proof/Sample.v'}
        replay.validate_replayed_contract(self.frozen, [moved], self.inputs, self.output)

    def test_missing_registry_cannot_silently_remove_a_board(self):
        self.registry.unlink()
        with self.assertRaises(FileNotFoundError):
            replay.validate_published_inputs(self.frozen)

    def test_changed_registry_is_rejected(self):
        self.registry.write_text('{"rows": 0}\n')
        with self.assertRaises(ValueError):
            replay.validate_published_inputs(self.frozen)

    def test_changed_or_missing_descriptor_is_rejected(self):
        for field, value in [('rows', 2), ('scope', 'state'), ('instruction_bound', 4097),
                             ('exact_inventory_theorem', 'Other.inventory_exact')]:
            changed = deepcopy(self.board)
            changed[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                replay.validate_replayed_contract(self.frozen, [changed], self.inputs, self.base)
        with self.assertRaises(ValueError):
            replay.validate_replayed_contract(self.frozen, [], self.inputs, self.base)


if __name__ == '__main__':
    unittest.main()
