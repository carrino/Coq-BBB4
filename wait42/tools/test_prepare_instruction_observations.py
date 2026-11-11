import unittest

from prepare_instruction_observations import CUTOFF, nomination, original_visits, transform


class PreparationTests(unittest.TestCase):
    def test_visits_return_to_original_instruction_coordinates(self):
        machine = '1RB0LC_0RD1LA_1LA0RD_0LC1RB'
        perm = (0, 3, 1, 2)
        row = {'machine': transform(machine, perm, True),
               'instruction_first': [100+i for i in range(8)]}
        self.assertEqual(original_visits(machine, row),
                         [100+2*perm[q]+a for q in range(4) for a in range(2)])

    def test_closed_tail_adds_endpoint_step(self):
        machine = '0RB---_1RB0RB_------_------'
        row = {'machine': machine, 'instruction_first': [CUTOFF, None, CUTOFF+1, CUTOFF+2,
                                                        None, None, None, None],
               'instruction_control_closed_at': CUTOFF+2}
        self.assertEqual(nomination(machine, row), (3, 2))

    def test_undefined_observed_slot_is_rejected(self):
        machine = '0RB---_1RB---_------_------'
        row = {'machine': machine, 'instruction_first': [CUTOFF, None, CUTOFF+1, CUTOFF+2,
                                                        None, None, None, None],
               'instruction_control_closed_at': CUTOFF+2}
        with self.assertRaisesRegex(ValueError, 'undefined'):
            nomination(machine, row)

    def test_one_symbol_is_not_a_closed_state_tail(self):
        machine = '0RB---_1RB0RB_------_------'
        row = {'machine': machine, 'instruction_first': [CUTOFF, None, CUTOFF+1, None,
                                                        None, None, None, None],
               'instruction_control_closed_at': CUTOFF+1}
        with self.assertRaisesRegex(ValueError, 'leaves the tail'):
            nomination(machine, row)


if __name__ == '__main__':
    unittest.main()
