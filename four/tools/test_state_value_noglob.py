"""Two source-only controls for the private -noglob delta; never invoke Coq."""
import ast
import copy
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from proof24_common import COMPILER_FLAGS, receipt_key, receipt_valid, sha, write_json
from build_state_value import FLAGS

BASE = Path(__file__).resolve().parent


class NoglobDelta(unittest.TestCase):
    def test_flag_change_invalidates_otherwise_identical_object_receipt(self):
        with tempfile.TemporaryDirectory(prefix='noglob-receipt-', dir=BASE) as folder:
            tree = Path(folder)
            source = 'Fixture.v'
            (tree / source).write_text('(* Source-only receipt fixture; no theorem. *)\n')
            obj = tree / 'Fixture.vo'
            obj.write_bytes(b'NOT A COQ OBJECT: receipt equality fixture only')
            graph = SimpleNamespace(tree=tree, digest='same-reviewed-manifest',
                                    deps={source: []}, paths=[])
            current = receipt_key(graph, source, 'same-runtime', {})
            self.assertEqual(current['compiler_flags'], list(COMPILER_FLAGS))
            self.assertEqual(current['compiler_flags'].count('-noglob'), 1)
            old = copy.deepcopy(current)
            old['compiler_flags'].remove('-noglob')
            receipt = tree / 'receipt.json'
            def save(inputs):
                write_json(receipt, {'inputs': inputs, 'object_sha256': sha(obj),
                    'object_bytes': obj.stat().st_size, 'compile_exit_code': 0})
            save(old)
            self.assertTrue(receipt_valid(receipt, old, obj))
            self.assertFalse(receipt_valid(receipt, current, obj))
            save(current)
            self.assertTrue(receipt_valid(receipt, current, obj))
            self.assertFalse(receipt_valid(receipt, old, obj))

    def test_every_compilation_path_has_noglob_and_selected_flags_match_receipts(self):
        self.assertEqual(FLAGS, list(COMPILER_FLAGS))
        selected = ast.parse((BASE / 'build_state_value.py').read_text())
        selected_calls = []
        for node in ast.walk(selected):
            if isinstance(node, ast.Call):
                for argument in node.args:
                    if isinstance(argument, ast.List):
                        args = argument.elts
                        if args and ast.unparse(args[0]) == "runtime['binaries']['coqc']['path']":
                            selected_calls.append(args)
                            self.assertTrue(any(isinstance(x, ast.Starred) and
                                isinstance(x.value, ast.Name) and x.value.id == 'FLAGS' for x in args))
        # Dependency compile, final/report check compile, and gated Value compile.
        self.assertEqual(len(selected_calls), 3)
        legacy = ast.parse((BASE / 'report_state_value.py').read_text())
        legacy_calls = []
        for node in ast.walk(legacy):
            if isinstance(node, ast.Call) and node.args and isinstance(node.args[0], ast.List):
                args = node.args[0].elts
                if args and isinstance(args[0], ast.Constant) and args[0].value == 'coqc':
                    flags = [x.value for x in args if isinstance(x, ast.Constant)]
                    legacy_calls.append(flags)
                    self.assertEqual(flags.count('-noglob'), 1)
        # Fresh pinned model modules and the legacy report-root compile.
        self.assertEqual(len(legacy_calls), 2)


if __name__ == '__main__':
    with patch('subprocess.Popen', side_effect=AssertionError('External process forbidden')):
        unittest.main()
