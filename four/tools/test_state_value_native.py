"""Native census policy, receipt invalidation, and a real Coq smoke test."""
import ast
import copy
from pathlib import Path
import shutil
import subprocess
import tempfile
from types import SimpleNamespace
import unittest

from proof24_common import (COMPILER_FLAGS, receipt_key, receipt_valid,
    require_native_compiler, sha, write_json)


class NativePolicyTests(unittest.TestCase):
    def test_preparation_plan_uses_the_selected_compiler_policy(self):
        source = Path(__file__).resolve().parent / 'state_value/prepare_global_sources.py'
        prefixes = []
        for node in ast.walk(ast.parse(source.read_text())):
            if isinstance(node, ast.Dict):
                for key, value in zip(node.keys, node.values):
                    if isinstance(key, ast.Constant) and key.value == 'module_command_prefix':
                        prefixes.append(ast.literal_eval(value))
        self.assertEqual(prefixes, [['coqc', *COMPILER_FLAGS]])

    def test_native_capability_is_required(self):
        for setting in ('yes', 'ondemand'):
            require_native_compiler({'config': 'COQLIB=/some/path\n'
                                     'COQ_NATIVE_COMPILER_DEFAULT=' + setting})
        for config in ('', 'COQ_NATIVE_COMPILER_DEFAULT=no',
                       'COQ_NATIVE_COMPILER_DEFAULT=unknown'):
            with self.subTest(config=config), self.assertRaisesRegex(
                    ValueError, 'requires native-capable Coq'):
                require_native_compiler({'config': config})

    def test_vm_only_receipt_is_not_reused(self):
        with tempfile.TemporaryDirectory() as folder:
            tree = Path(folder)
            (tree / 'Source.v').write_text('(* Receipt comparison fixture. *)\n')
            obj = tree / 'Source.vo'
            obj.write_bytes(b'not a Coq object; receipt comparison fixture')
            graph = SimpleNamespace(tree=tree, digest='fixed-manifest',
                                    deps={'Source.v': []}, paths=[])
            current = receipt_key(graph, 'Source.v', 'fixed-runtime', {})
            old = copy.deepcopy(current)
            old['compiler_flags'] = ['-q', '-noglob', '-w',
                                     '-abstract-large-number', '-native-compiler', 'no']
            receipt = tree / 'receipt.json'
            write_json(receipt, {'inputs': old, 'object_sha256': sha(obj),
                'object_bytes': obj.stat().st_size, 'compile_exit_code': 0})
            self.assertTrue(receipt_valid(receipt, old, obj))
            self.assertFalse(receipt_valid(receipt, current, obj))

    def test_native_compute_and_fallback_rejection(self):
        coqc = shutil.which('coqc')
        if coqc is None:
            self.skipTest('native-capable coqc is required for the real smoke test')
        config = subprocess.run([coqc, '-config'], check=True, text=True,
                                capture_output=True, timeout=30).stdout
        try:
            require_native_compiler({'config': config})
        except ValueError:
            self.skipTest('installed coqc has no native compiler')
        with tempfile.TemporaryDirectory() as folder:
            tree = Path(folder)
            (tree / 'NativeProbe.v').write_text(
                'Example native_sum : Nat.add 1000 7 = 1007.\n'
                'Proof. native_compute. reflexivity. Qed.\n'
                'Print Assumptions native_sum.\n')
            success = subprocess.run([coqc, *COMPILER_FLAGS, 'NativeProbe.v'],
                cwd=tree, text=True, capture_output=True, timeout=60)
            self.assertEqual(success.returncode, 0, success.stdout + success.stderr)
            self.assertIn('Closed under the global context', success.stdout)
            self.assertNotIn('falling back', success.stdout + success.stderr)
            fallback = subprocess.run([coqc, '-q', '-noglob', '-w',
                '+native-compiler-disabled', '-native-compiler', 'no', 'NativeProbe.v'],
                cwd=tree, text=True, capture_output=True, timeout=30)
            self.assertNotEqual(fallback.returncode, 0)
            self.assertIn('Error:', fallback.stdout + fallback.stderr)
            self.assertIn('falling back to', fallback.stdout + fallback.stderr)


if __name__ == '__main__':
    unittest.main()
