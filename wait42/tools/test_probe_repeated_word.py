"""Small semantic checks for nomination failures, never proof substitutes."""
import unittest
from probe_repeated_word import probe, coq_tm


class RepeatedWordProbeTests(unittest.TestCase):
    def test_alternating_finite_rank(self):
        self.assertEqual(probe('0RB0RB_0RA0RA_------_------', 1, 0)[0], 'nominated')

    def test_halt_is_not_closed(self):
        self.assertEqual(probe('------_------_------_------', 1, 0)[0], 'open-successor')
        self.assertEqual(probe('------_------_------_------', 1, 1)[0], 'halted-anchor')

    def test_node_cap_is_preserved(self):
        self.assertEqual(probe('0RB0RB_0RA0RA_------_------', 1, 0, cap=1)[0], 'node-cap')

    def test_size_cut_is_preserved(self):
        self.assertEqual(probe('0RB0RB_0RA0RA_------_------', 3, 0, size=0)[0], 'size-cut')

    def test_avoiding_cycle_is_rejected(self):
        self.assertEqual(probe('0RB0RB_0RB0RB_------_------', 1, 0)[0], 'avoiding-cycle')

    def test_export_preserves_holes(self):
        self.assertIn('| StC, S0 => None', coq_tm('0RB0RB_0RA0RA_------_------'))


if __name__ == '__main__':
    unittest.main()
