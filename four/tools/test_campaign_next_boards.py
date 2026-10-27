"""Boundary tests for the exact-champion exception; no Coq replay required."""
from copy import deepcopy
import unittest

from campaign_next_boards import (CHAMPION, EXACT_INTERFACE, SCORE,
                                  inventory_source, validate_champion)


class ChampionOptInTests(unittest.TestCase):
    def setUp(self):
        self.board = dict(EXACT_INTERFACE, id='ChampionCensusNext', scope='both',
                          machines=[CHAMPION], rows=1, exact_champion=True,
                          state_bound=SCORE, instruction_bound=SCORE,
                          state_bound_term='scoreN', instruction_bound_term='scoreN')

    def reject(self, **changes):
        board = deepcopy(self.board)
        board.update(changes)
        with self.assertRaises(ValueError):
            validate_champion(board)

    def test_exact_named_singleton_is_accepted(self):
        validate_champion(self.board)

    def test_opt_in_is_mandatory(self):
        board = deepcopy(self.board)
        del board['exact_champion']
        with self.assertRaisesRegex(ValueError, 'unexpectedly includes the champion'):
            validate_champion(board)
        self.reject(exact_champion=False)

    def test_opt_in_requires_boolean(self):
        for value in (1, 'true', None):
            with self.subTest(value=value):
                self.reject(exact_champion=value)

    def test_exact_singleton_only(self):
        for machines in ([], [CHAMPION, CHAMPION], ['1RB2LA1RA1LB_0LB2RB3RB1LA']):
            with self.subTest(machines=machines):
                self.reject(machines=machines)
        self.reject(rows=2)

    def test_scope_must_be_both(self):
        self.reject(scope='state', instruction_bound=None)

    def test_reported_binary_bounds_are_exact_integers(self):
        for field in ('state_bound', 'instruction_bound'):
            for value in (SCORE-1, SCORE+1, str(SCORE), float(SCORE), True):
                with self.subTest(field=field, value=value):
                    self.reject(**{field: value})

    def test_bound_terms_are_allowlisted(self):
        for field in ('state_bound_term', 'instruction_bound_term'):
            for value in ('score', 'N.to_nat scoreN', 'scoreN. Axiom bad : False', None):
                with self.subTest(field=field, value=value):
                    self.reject(**{field: value})

    def test_exact_theorem_interface_is_fixed(self):
        for field in EXACT_INTERFACE:
            with self.subTest(field=field):
                self.reject(**{field: 'DifferentModuleOrTheorem'})

    def test_normal_board_cannot_use_symbolic_terms(self):
        self.reject(exact_champion=False, machines=['0LA0LA0LA0LA_0LA0LA0LA0LA'])

    def test_wrapper_binds_numbers_before_symbolic_bounds(self):
        source = inventory_source(self.board)
        self.assertIn(f'Definition recorded_state_bound : N := {SCORE}%N.', source)
        self.assertIn(f'Definition recorded_instruction_bound : N := {SCORE}%N.', source)
        self.assertLess(source.index('recorded_state_bound = scoreN'), source.index('Local Opaque'))
        self.assertLess(source.index('recorded_instruction_bound = scoreN'), source.index('Local Opaque'))
        self.assertIn('Theorem small_sound : BoardSound scoreN scoreN board.', source)
        self.assertIn('rewrite recorded_state_bound_exact, recorded_instruction_bound_exact', source)
        self.assertNotIn(f'BoardSound {SCORE}', source)


if __name__ == '__main__':
    unittest.main()
