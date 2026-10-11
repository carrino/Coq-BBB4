#!/usr/bin/env python3
"""Source-reader checks; RunTr's Coq conversion is the semantic gate."""
from pathlib import Path
import tempfile
import unittest

import gen_provtr_data as gen


class ProvenDataTests(unittest.TestCase):
    def test_undefined_slot_boundaries(self):
        specs = ['1RB---_------_------_------',
                 '0RB0LA_0LC0RD_1LA1RD_1RC---',
                 '------_1RB---_---0LA_------']
        for spec in specs:
            for placeholder in ['XXX','___']:
                self.assertEqual(gen.spec_from_name('tm_'+spec.replace('---',placeholder)),spec)
        self.assertIsNone(gen.spec_from_name('tm_not_a_machine'))

    def test_order_duplicates_and_aliases(self):
        a='0RB0LA_0LC0RD_1LA1RD_1RC---'
        b='1RB---_------_------_------'
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            (root/'RunTr.v').write_text(
                'Definition prov_tr : list TM := left ++ [Stage.alias] ++ left.\n'
                'Definition left : list TM := [Stage.a; Stage.b].\n')
            (root/'ProvTr_Stage.v').write_text('')
            (root/'ProvTr_Test.v').write_text(
                gen.tm_lambda('a',a)+'\n'+gen.tm_lambda('b',b)+'\n'
                'Definition alias : TM := a.\n')
            # Qualifiers are actual file/module names, not a name guessed
            # from the definitions' spelling.
            p=root/'RunTr.v';p.write_text(p.read_text().replace('Stage.','ProvTr_Test.'))
            inv=gen.Inventory(root)
            self.assertEqual(inv.resolve('prov_tr'),[a,b,a,a,b])

    def test_comments_and_unsupported_expressions(self):
        self.assertEqual(gen.uncomment('a(* outer (* inner *) end *)b'),'a b')
        with self.assertRaises(ValueError):
            gen.uncomment('(* broken')
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            (root/'RunTr.v').write_text('Definition prov_tr : list TM := (mystery []).\n')
            with self.assertRaisesRegex(ValueError,'unrecognized list expression'):
                gen.Inventory(root).resolve('prov_tr')

    def test_ambiguous_and_cyclic_names_fail(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            (root/'RunTr.v').write_text('Definition prov_tr : list TM := a.\n')
            for name in ['X','Y']:
                (root/f'ProvTr_{name}.v').write_text('Definition a : list TM := [].\n')
            with self.assertRaisesRegex(ValueError,'ambiguous'):
                gen.Inventory(root).resolve('prov_tr')
            (root/'RunTr.v').write_text('Definition prov_tr : list TM := prov_tr.\n')
            with self.assertRaisesRegex(ValueError,'cyclic'):
                gen.Inventory(root).resolve('prov_tr')


if __name__ == '__main__':
    unittest.main()
