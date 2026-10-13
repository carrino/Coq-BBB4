#!/usr/bin/env python3
"""Exercise the CI recipe's target forwarding and fail-closed sequencing."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

REPO = Path(__file__).resolve().parents[1]


class NativeBuildTests(unittest.TestCase):
    def run_recipe(self, targets, fail=False):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            recorder = root / 'make'
            recorder.write_text('''#!/usr/bin/env python3
import json, os, sys
with open(os.environ['CALLS'], 'a') as f:
    f.write(json.dumps(sys.argv[1:]) + '\\n')
if os.environ.get('FAIL_COMPUTE') and 'COQEXTRAFLAGS=-native-compiler yes' in sys.argv:
    sys.exit(7)
''')
            recorder.chmod(0o755)
            calls = root / 'calls.jsonl'
            env = dict(os.environ, PATH=str(root) + os.pathsep + os.environ['PATH'], CALLS=str(calls))
            if fail:
                env['FAIL_COMPUTE'] = '1'
            result = subprocess.run(['bash', 'tools/ci_native_build.sh', *targets],
                                    cwd=REPO, env=env, capture_output=True, text=True)
            return result, [json.loads(x) for x in calls.read_text().splitlines()] if calls.exists() else []

    def test_all_targets_forwarded_after_native_dependencies(self):
        targets = ['TIMED=1', 'theories/A.vo', 'theories/B.vo']
        result, calls = self.run_recipe(targets)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(calls), 2)
        self.assertIn('COQEXTRAFLAGS=-native-compiler yes', calls[0])
        self.assertIn('COQEXTRAFLAGS=-native-compiler ondemand', calls[1])
        self.assertEqual(calls[1][-len(targets):], targets)

    def test_failed_dependency_build_stops_proof_build(self):
        result, calls = self.run_recipe(['theories/A.vo'], fail=True)
        self.assertEqual(result.returncode, 7)
        self.assertEqual(len(calls), 1)

    def test_no_targets_does_not_build(self):
        result, calls = self.run_recipe([])
        self.assertEqual(result.returncode, 0)
        self.assertEqual(calls, [])


if __name__ == '__main__':
    unittest.main()
