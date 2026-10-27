"""Reject invalid conjugacy selections before expensive proof replay."""
import copy
import json
import unittest

import check_burn2_structural as replay


class SelectionTests(unittest.TestCase):
    def setUp(self):
        self.data = json.loads(replay.INPUT.read_text())

    def test_frozen_selection_and_source_inventory(self):
        ordinary, weighted, machines = replay.selection(self.data)
        self.assertEqual((len(ordinary), len(weighted), len(machines)), (61, 3, 64))
        self.assertEqual(len(self.data['rows']), 67)

    def test_changed_source_pin_rejected(self):
        name = next(iter(self.data['pins']))
        self.data['pins'][name] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'Frozen source input differs'):
            replay.selection(self.data)

    def test_zero_destination_prefix_rejected(self):
        self.assertEqual(self.data['rows'][0][4], 17)
        self.data['rows'][0][4] = 0
        with self.assertRaisesRegex(ValueError, 'Exact boot configurations differ'):
            replay.selection(self.data)

    def test_wrong_table_source_rejected(self):
        self.data['rows'][0][1] = self.data['rows'][1][1]
        with self.assertRaisesRegex(ValueError, 'Source table is not included'):
            replay.selection(self.data)

    def test_changed_prefix_budget_rejected(self):
        self.data['output_bound'] = 4096
        with self.assertRaisesRegex(ValueError, 'Unexpected source/output bound'):
            replay.selection(self.data)

    def test_duplicate_target_rejected(self):
        self.data['rows'].append(copy.deepcopy(self.data['rows'][0]))
        with self.assertRaisesRegex(ValueError, 'Duplicate target'):
            replay.selection(self.data)


if __name__ == '__main__':
    unittest.main()
