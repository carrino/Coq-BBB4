#!/usr/bin/env python3
"""Check that stored-certificate generation preserves the batch interface."""
import unittest

import gen_rw_stored as gen


class StoredCloseoutTests(unittest.TestCase):
    def setUp(self):
        self.name = 'TEST_00_0000'
        self.cert = dict(spec='1RB0LD_1RC1RD_1LA1LD_1LC0RB',
                         L=7, T=2, t=0, fuel=61392, M=24)
        self.source = ('From Coq Require Import List.\nImport ListNotations.\n'
                       f'(* spec {self.cert["spec"]} *)\n'
                       f'Definition r_{self.name} : list (option Trans) := '
                       f'{gen.spec_row(self.cert["spec"])}.\n'
                       f'Lemma cv_{self.name} : coversTr (row_to_tm r_{self.name}).\n'
                       'Proof. apply coversTr_nqh, (rw_tier_tr_sound _ 7 2 0 61392 24). '
                       'vm_cast_no_check (eq_refl true). Qed.\n')

    def test_only_imports_and_checker_change(self):
        certificates = {self.name: self.cert}
        after = gen.rewrite_batch(self.source, certificates)
        self.assertEqual(gen.rewrite_batch(after, certificates), after)
        start, end = after.index(gen.BEGIN), after.index(gen.END) + len(gen.END)
        restored = (after[:start] + after[end:]).replace(
            f'rw_check_stored_tr_sound _ 7 2 0 24 Data_{self.name}.keys '
            f'Data_{self.name}.ranks Data_{self.name}.cert',
            'rw_tier_tr_sound _ 7 2 0 61392 24')
        self.assertEqual(restored, self.source)
        self.assertEqual(gen.original_batch(after, certificates), self.source)
        with self.assertRaisesRegex(ValueError, 'without certificate source'):
            gen.rewrite_batch(after, {})

    def test_wrong_machine_or_parameters_rejected(self):
        for field, value in [('spec', '0RB0LD_1RC1RD_1LA1LD_1LC0RB'), ('L', 8)]:
            with self.subTest(field=field), self.assertRaises(ValueError):
                gen.rewrite_batch(self.source, {self.name: dict(self.cert, **{field: value})})


if __name__ == '__main__':
    unittest.main()
