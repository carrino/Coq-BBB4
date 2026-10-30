"""Historical renderer syntax stays equivalent without invalid-escape warnings."""
import ast
import importlib.util
from pathlib import Path
import unittest
import warnings

TOOLS = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    'state_value_escape_preparer', TOOLS / 'state_value/prepare_global_sources.py')
preparer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(preparer)


class RendererEscapeTests(unittest.TestCase):
    def test_historical_programs_keep_identical_syntax_trees(self):
        for relative in sorted(preparer.LEGACY_ESCAPE_RENDERERS):
            with self.subTest(renderer=relative):
                path = TOOLS / Path(relative).name
                original = path.read_bytes()
                with warnings.catch_warnings(record=True) as previous:
                    warnings.simplefilter('always')
                    before = ast.parse(original, filename=str(path))
                self.assertTrue(previous)
                fixed = preparer.renderer_python_source(relative, original)
                with warnings.catch_warnings():
                    warnings.simplefilter('error', SyntaxWarning)
                    after = ast.parse(fixed, filename=str(path))
                    compile(fixed, str(path), 'exec')
                self.assertEqual(ast.dump(before), ast.dump(after))
                self.assertEqual(path.read_bytes(), original)

    def test_unrelated_sources_are_untouched(self):
        source = b'value = "\\/"\n'
        self.assertEqual(preparer.renderer_python_source('unrelated.py', source), source)

    def test_other_warnings_are_not_suppressed(self):
        source = b'value = "\\q"\n'
        fixed = preparer.renderer_python_source(
            'four/tools/check_weighted_closeout.py', source)
        with warnings.catch_warnings():
            warnings.simplefilter('error')
            with self.assertRaises((SyntaxError, SyntaxWarning, DeprecationWarning)):
                compile(fixed, 'other-warning.py', 'exec')

    def test_current_renderer_has_no_invalid_escapes(self):
        path = TOOLS / 'state_value/late_renderers.py'
        with warnings.catch_warnings():
            warnings.simplefilter('error', SyntaxWarning)
            compile(path.read_bytes(), str(path), 'exec')


if __name__ == '__main__':
    unittest.main()
