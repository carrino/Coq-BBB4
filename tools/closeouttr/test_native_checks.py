#!/usr/bin/env python3
import unittest
from unittest.mock import patch

from native_checks import proof_evaluator, rewrite


class NativeChecksTests(unittest.TestCase):
    def test_large_compact_certificates_only(self):
        source = ('(* COMPACT CERTIFICATE TABLES v1 *)\n'
                  'Lemma cert : checker data = true.\n'
                  'Proof. vm_compute. reflexivity. Qed.\n')
        self.assertEqual(rewrite(source), source)
        with patch('native_checks.COMPACT_NATIVE_MIN_BYTES', len(source.encode())):
            after = rewrite(source)
            self.assertEqual(after, source.replace('vm_compute', 'native_compute'))
            self.assertEqual(rewrite(after), after)
            unmarked = source.replace('COMPACT CERTIFICATE TABLES v1', 'literal tables')
            self.assertEqual(rewrite(unmarked), unmarked)

    def test_only_search_cast_changes(self):
        for checker in ['rank_tier_tr_sound', 'rw_tier_tr_sound', 'mb_tier_tr_sound']:
            source = ('Definition row := [t1RB;tN].\nLemma cert : coversTr tm.\n'
                      f'Proof. apply coversTr_nqh, ({checker} _ 7 2 0 1234 24). '
                      'vm_cast_no_check (eq_refl true). Qed.\n')
            after = rewrite(source)
            self.assertIn('native_cast_no_check', after)
            self.assertEqual(after.replace('native_cast_no_check', 'vm_cast_no_check'), source)
            self.assertEqual(rewrite(after), after)

    def test_stored_and_other_checks_stay_unchanged(self):
        for proof in ['apply coversTr_nqh, (rw_check_stored_tr_sound _ 7 2 0 24 keys ranks cert). vm_cast_no_check (eq_refl true).',
                      'apply coversTr_nqh, (tri_sound _ 10). vm_cast_no_check (eq_refl true).',
                      'exact existing_proof.']:
            self.assertEqual(proof_evaluator(proof), proof)


if __name__ == '__main__':
    unittest.main()
