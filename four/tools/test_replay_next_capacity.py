"""Read-only contract checks and isolated tamper tests; no Coq compilation."""
from copy import deepcopy
import json
from pathlib import Path
import tempfile
import unittest

import replay_next_capacity as replay


class PortableNextCapacityTests(unittest.TestCase):
    def setUp(self):
        self.before = replay.published_snapshot()
        self.exact = json.loads(replay.research('inventory-check.json').read_text())

    def tearDown(self):
        self.assertEqual(self.before, replay.published_snapshot())

    def inputs(self, kind):
        index = 0 if kind == 'capacity' else 1
        return [json.loads(replay.research(kind + '-check.json').read_text()),
                json.loads(replay.research(kind + '-checked-machines.json').read_text()),
                deepcopy(self.exact['boards'][index])]

    def test_frozen_contracts_and_wrapper_bytes(self):
        for kind, name, _, _ in replay.KINDS:
            text = replay.validate_contract(kind, *self.inputs(kind))
            source = replay.ROOT / 'build/next-capacity/inventory-proof' / (name + '.v')
            self.assertEqual(text, source.read_text())

    def test_typed_bounds_and_counts(self):
        for target, key, bad in ((0, 'state_bound', 4096.0),
                                 (0, 'instruction_bound', None),
                                 (0, 'rows', True),
                                 (2, 'rows', True),
                                 (2, 'state_bound', 4096.0),
                                 (2, 'instruction_bound', 4095)):
            args = self.inputs('capacity')
            (args[0]['manifest'] if target == 0 else args[2])[key] = bad
            with self.subTest(target=target, key=key), self.assertRaises(ValueError):
                replay.validate_contract('capacity', *args)

    def test_changed_scope_or_inventory_encoding(self):
        for key, bad in (('scope', 'state'), ('module', 'Unexpected.Inventory')):
            args = self.inputs('capacity')
            args[2][key] = bad
            with self.subTest(key=key), self.assertRaises(ValueError):
                replay.validate_contract('capacity', *args)
        args = self.inputs('capacity')
        args[2]['inventories'][0]['format'] = 'json_rows'
        with self.assertRaises(ValueError):
            replay.validate_contract('capacity', *args)

    def test_changed_inventory_order(self):
        args = self.inputs('portfolio')
        args[1]['rows'].reverse()
        with self.assertRaisesRegex(ValueError, 'Ordered checked inventory'):
            replay.validate_contract('portfolio', *args)

    def test_coordinated_machine_change_fails_frozen_wrapper_hash(self):
        args = self.inputs('capacity')
        changed = '1LB2RA1LA1RB_0RB2LB3LB1RA'
        args[0]['results'][0]['machine'] = changed
        args[1]['rows'][0]['machine'] = changed
        with self.assertRaisesRegex(ValueError, 'Regenerated exact inventory source'):
            replay.validate_contract('capacity', *args)

    def test_unchecked_result_cannot_enter_inventory(self):
        args = self.inputs('portfolio')
        args[0]['results'][0]['status'] = 'timeout'
        with self.assertRaisesRegex(ValueError, 'Unexpected result mapping'):
            replay.validate_contract('portfolio', *args)

    def test_historical_objects_are_not_portable_contract(self):
        args = self.inputs('capacity')
        original = replay.validate_contract('capacity', *args)
        for name in args[0]['artifacts_sha256']:
            if name.endswith(('.vo', '.receipt.json')):
                args[0]['artifacts_sha256'][name] = '0' * 64
        self.assertEqual(original, replay.validate_contract('capacity', *args))

    def test_existing_staged_wrapper_tamper_rejected(self):
        with tempfile.TemporaryDirectory(prefix='next-capacity-tamper-') as directory:
            root = Path(directory)
            replay.load_evidence(root)
            source = root / 'inventory-proof/Capacity.v'
            source.parent.mkdir()
            source.write_text('(* tampered staged wrapper *)\n')
            with self.assertRaisesRegex(ValueError, 'Existing exact inventory source differs'):
                replay.load_evidence(root)


if __name__ == '__main__':
    unittest.main()
