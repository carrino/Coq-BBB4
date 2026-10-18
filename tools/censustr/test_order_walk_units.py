#!/usr/bin/env python3
"""Ordering must preserve the pending workload and handle stale hints."""
from collections import Counter
from contextlib import redirect_stdout, redirect_stderr
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import order_walk_units as order


class OrderingTests(unittest.TestCase):
    def test_longest_first_and_deterministic_ties(self):
        paths = ['p/UnitTr_02.v', 'p/UnitTr_00.v', 'p/UnitTr_01.v']
        costs = {'UnitTr_00': 2, 'UnitTr_01': 9, 'UnitTr_02': 9}
        expected = ['p/UnitTr_01.v', 'p/UnitTr_02.v', 'p/UnitTr_00.v']
        self.assertEqual(order.ordered_paths(paths, costs), expected)
        self.assertEqual(order.ordered_paths(reversed(paths), costs), expected)

    def test_only_pending_paths_are_emitted_and_multiplicity_is_preserved(self):
        paths = ['p/UnitTr_00.v', 'p/UnitTr_03.v', 'p/UnitTr_00.v']
        costs = {f'UnitTr_{i:02d}': i for i in range(96)}
        result = order.ordered_paths(paths, costs)
        self.assertEqual(Counter(result), Counter(paths))
        self.assertNotIn('p/UnitTr_01.v', result)

    def test_unknown_paths_are_retained_and_run_first(self):
        paths = ['p/UnitTr_00.v', 'p/UnitTr_03.v', 'p/UnitTr_02.v']
        self.assertEqual(order.ordered_paths(paths, {'UnitTr_00': 100}),
                         ['p/UnitTr_02.v', 'p/UnitTr_03.v', 'p/UnitTr_00.v'])

    def run_cli(self, text, profile=None, units=4):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp)/'costs.json'
            if profile is not None:
                path.write_text(profile)
            output, errors = io.StringIO(), io.StringIO()
            with patch('sys.stdin', io.StringIO(text)), redirect_stdout(output), redirect_stderr(errors):
                order.main(['--units', str(units), '--profile', str(path)])
            return output.getvalue(), errors.getvalue()

    def test_empty_input_emits_nothing(self):
        output, _ = self.run_cli('', json.dumps({'units': 4, 'seconds': {}}))
        self.assertEqual(output, '')

    def test_cli_uses_matching_profile(self):
        output, errors = self.run_cli('p/UnitTr_00.v\np/UnitTr_01.v\n',
            json.dumps({'units': 4, 'seconds': {'UnitTr_00': 1, 'UnitTr_01': 9}}))
        self.assertEqual(output, 'p/UnitTr_01.v\np/UnitTr_00.v\n')
        self.assertEqual(errors, '')

    def test_changed_unit_count_uses_lexical_order(self):
        output, errors = self.run_cli('p/UnitTr_01.v\np/UnitTr_00.v\n',
            json.dumps({'units': 96, 'seconds': {'UnitTr_00': 1, 'UnitTr_01': 9}}))
        self.assertEqual(output, 'p/UnitTr_00.v\np/UnitTr_01.v\n')
        self.assertIn('profile has 96 units, requested 4', errors)

    def test_missing_and_malformed_profiles_preserve_the_workload(self):
        for profile in [None, '{bad', '[]', '{"units": 4, "seconds": []}',
                        '{"units": 4, "seconds": {"UnitTr_00": -1}}',
                        '{"units": 4, "seconds": {"UnitTr_00": NaN}}',
                        '{"units": 4, "seconds": {"UnitTr_09": 1}}']:
            with self.subTest(profile=profile):
                output, errors = self.run_cli('p/UnitTr_01.v\np/UnitTr_00.v\n', profile)
                self.assertEqual(output, 'p/UnitTr_00.v\np/UnitTr_01.v\n')
                self.assertIn('using lexical order', errors)


if __name__ == '__main__':
    unittest.main()
