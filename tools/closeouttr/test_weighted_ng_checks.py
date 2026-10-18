import unittest
from weighted_ng_checks import rewrite, OLD_IMPORT, NEW_IMPORT, OLD_THEOREM, NEW_THEOREM
from native_checks import rewrite as native_checks
from ng_batch import batch_checker, CHECK

SOURCE = OLD_IMPORT + '\nDefinition row := [None].\nLemma cv : coversTr tm.\nProof. apply coversTr_nqh, (rank_tier_tr_sound _ 6 0 200000 512). vm_cast_no_check (eq_refl true). Qed.\n'

class WeightedNGTests(unittest.TestCase):
    def test_changes_only_import_and_theorem(self):
        changed=rewrite(SOURCE,'CBT_NG_11')
        self.assertEqual(changed.replace(NEW_IMPORT,OLD_IMPORT).replace(NEW_THEOREM,OLD_THEOREM),SOURCE)
    def test_idempotent(self):
        changed=rewrite(SOURCE,'CBT_NG_11')
        self.assertEqual(rewrite(changed,'CBT_NG_11'),changed)
    def test_other_families_unchanged(self):
        for name in ('CBT_RW_11','ProvTr_RK_00','DecideTr','CBT_NG_11_copy'):
            self.assertEqual(rewrite(SOURCE,name),SOURCE)
    def test_unexpected_import_fails(self):
        with self.assertRaises(ValueError):rewrite(SOURCE.replace(OLD_IMPORT,''),'CBT_NG_11')
    def test_qualified_legacy_fails(self):
        with self.assertRaises(ValueError):rewrite(SOURCE.replace(OLD_THEOREM,'DecideTr.'+OLD_THEOREM),'CBT_NG_11')
    def test_no_rank_proof_unchanged(self):
        self.assertEqual(rewrite('Some unrelated source.','CBT_NG_11'),'Some unrelated source.')
    def test_generated_ng_only(self):
        self.assertEqual(batch_checker('rk','NG')[1],NEW_THEOREM)
        self.assertEqual(batch_checker('rk','RK'),CHECK['rk'])
        self.assertEqual(batch_checker('ng','NG'),CHECK['ng'])
    def test_native_route_preserved(self):
        changed=native_checks(rewrite(SOURCE,'CBT_NG_11'))
        self.assertIn('native_cast_no_check (eq_refl true)',changed)
        self.assertEqual(native_checks(rewrite(changed,'CBT_NG_11')),changed)

if __name__=='__main__':unittest.main(verbosity=2)
