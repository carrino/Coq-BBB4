import unittest

import fast_bound_checks as b


class FastBoundTests(unittest.TestCase):
    def test_two_goal_stages_keep_checker_and_parameters(self):
        for stage in ['tcycler_qh_stage', 'tcycler_qh_stage_L', 'qh_plain_stage',
                      'qh_lex_stage', 'rwqh_stage']:
            source = ('Definition certificate := [1;2;3].\n'
                      'Lemma result : original_statement.\n'
                      f'Proof. apply ({stage} tm 7 2 64 32779478). all: {b.CAST}. Qed.\n')
            result = b.rewrite(source)
            expected = b.IMPORT + source.replace('. all: ' + b.CAST,
                '; [' + b.CAST + ' | apply bound_tr_leb; ' + b.CAST + ']')
            self.assertEqual(result, expected)
            self.assertEqual(b.rewrite(result), result)
            self.assertEqual(b.expand(result), source)

    def test_lap_final_bound_only(self):
        source = ('Theorem result : original_statement.\nProof.\n'
                  'apply (lap_qh_stage tm pins Cc 2 31 32779478).\n'
                  '- exact boot.\n- exact lap.\n- exact fires.\n- exact witness.\n'
                  '- ' + b.CAST + '.\nQed.\n')
        result = b.rewrite(source)
        self.assertEqual(result, b.IMPORT + source.replace('- ' + b.CAST,
            '- apply bound_tr_leb; ' + b.CAST))
        self.assertEqual(b.rewrite(result), result)
        self.assertEqual(b.expand(result), source)

    def test_standalone_bound(self):
        source = 'Lemma bnd_m : (22 <=? 32779478) = true.\nProof. ' + b.CAST + '. Qed.\n'
        result = b.rewrite(source)
        self.assertEqual(result, b.IMPORT + source.replace('Proof. ',
                                                         'Proof. apply bound_tr_leb; '))
        self.assertEqual(b.rewrite(result), result)
        self.assertEqual(b.expand(result), source)

    def test_other_bounds_and_checkers_unchanged(self):
        examples = [
            f'Proof. apply (unknown_stage tm 32779478). all: {b.CAST}. Qed.',
            f'Proof. apply (rwqh_stage tm 32779479). all: {b.CAST}. Qed.',
            f'Lemma c : checker tm = true. Proof. {b.CAST}. Qed.',
            f'Lemma bnd : (2 <=? 32779479) = true. Proof. {b.CAST}. Qed.',
        ]
        for source in examples:
            with self.subTest(source=source):
                self.assertEqual(b.rewrite(source), source)


if __name__ == '__main__':
    unittest.main()
