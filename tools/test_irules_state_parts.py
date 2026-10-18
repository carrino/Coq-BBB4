#!/usr/bin/env python3
"""Guard state proof coverage, public interfaces, and canonical TR inputs."""
import importlib.util
from pathlib import Path
import re
import unittest

import gen_irules_state_parts as gen


class StatePartsTests(unittest.TestCase):
    def test_complete_inventory_and_public_interfaces(self):
        boards = gen.boards()
        outputs = gen.render(boards)
        self.assertEqual(len(boards), 9)
        part_names = []
        for path, source in outputs.items():
            if path.parent.name == 'IRulesStateParts':
                names = re.findall(r'^Theorem (\w+)', source, re.M)
                self.assertLessEqual(len(names), gen.CHUNK)
                self.assertEqual(source.count('irules_check_neverqh_sound'), len(names))
                self.assertNotRegex(source, r'Require[^.]*IRules_Batch_')
                part_names.extend(names)
            else:
                old = boards[path]
                self.assertEqual(gen.definitions(old), gen.definitions(source))
                self.assertEqual(re.findall(r'^Theorem (\w+)', old, re.M),
                                 re.findall(r'^Theorem (\w+)', source, re.M))
                self.assertNotIn('vm_compute', source[source.index('Definition mk'):])
                for name, _ in gen.definitions(source):
                    self.assertRegex(source,
                        rf'exact IRulesStatePart_\d+_\d+\.ir_{name}_never_quasihalts')
        expected = [f'ir_{name}_never_quasihalts'
                    for source in boards.values() for name, _ in gen.definitions(source)]
        self.assertEqual(part_names, expected)
        self.assertEqual(len(expected), 250)

    def test_idempotent_wrappers(self):
        first = gen.render()
        wrappers = {p: s for p, s in first.items() if p.parent == gen.MACHINES}
        self.assertEqual(gen.render(wrappers), first)

    def test_instruction_generated_outputs_are_unchanged(self):
        path = gen.REPO / 'tools/censustr/gen_irulestr_parts.py'
        spec = importlib.util.spec_from_file_location('irules_tr_generator', path)
        tr = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(tr)
        before = tr.definitions()
        after = {}
        for path, source in gen.render().items():
            if path.parent == gen.MACHINES:
                after.update(gen.definitions(source))
        self.assertEqual(before, after)
        self.assertEqual(tr.render(sources=before), tr.render(sources=after))

    def test_missing_and_duplicate_certificates_are_rejected(self):
        boards = gen.boards()
        with self.assertRaises(ValueError):
            gen.render(dict(list(boards.items())[:-1]))
        paths = list(boards)
        boards[paths[-1]] = boards[paths[0]]
        with self.assertRaises(ValueError):
            gen.render(boards)


if __name__ == '__main__':
    unittest.main()
