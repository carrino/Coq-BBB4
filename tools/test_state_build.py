#!/usr/bin/env python3
"""Check the state build's native boundary and prerequisite failure handling."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

REPO = Path(__file__).resolve().parents[1]


class StateBuildTests(unittest.TestCase):
    def run_build(self, compute='yes', proof=None, fail=False):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / '_CoqProject').touch()
            (root / 'Makefile.coq').touch()
            (root / 'tools').mkdir()
            shutil.copy(REPO / 'tools/ensure_native.py', root / 'tools/ensure_native.py')
            recorder = root / 'record_make'
            recorder.write_text('''#!/usr/bin/env python3
import json, os, sys
from pathlib import Path
with Path('calls.jsonl').open('a') as f:
    f.write(json.dumps(sys.argv[1:]) + '\\n')
if os.environ.get('FAIL_COMPUTE') and sys.argv[-1].endswith('Run_Compute_Split.vo'):
    raise SystemExit(9)
''')
            recorder.chmod(0o755)
            command = [shutil.which('make'), '-f', str(REPO / 'Makefile'),
                       'state-build', 'MAKE=' + str(recorder), 'BUILD_JOBS=3',
                       'STATE_COMPUTE_NATIVE=' + compute, 'WALK_CORES=1',
                       'COQEXTRAFLAGS=-w -abstract-large-number']
            if proof is not None:
                command.append('STATE_PROOF_NATIVE=' + proof)
            env = dict(os.environ)
            if fail:
                env['FAIL_COMPUTE'] = '1'
            result = subprocess.run(command, cwd=root, env=env,
                                    capture_output=True, text=True, timeout=30)
            calls = [json.loads(s) for s in (root / 'calls.jsonl').read_text().splitlines()]
            return result, calls

    def test_compute_first_then_all_proofs(self):
        result, calls = self.run_build()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(calls), 2)
        self.assertEqual(calls[0][-1], 'theories/Census/Run_Compute_Split.vo')
        self.assertIn('theories/Checkers/TCyclerNFast.vo', calls[0])
        self.assertIn('COQEXTRAFLAGS=-w -abstract-large-number -native-compiler yes', calls[0])
        self.assertIn('COQEXTRAFLAGS=-w -abstract-large-number -native-compiler ondemand', calls[1])
        for target in ['theories/Census/Run.vo', 'theories/Closeout/Closeout.vo',
                       'theories/Machines/Counters/Champion_1RB1LD_1RC1RB_1LC1LA_0RC0RD.vo']:
            self.assertIn(target, calls[1])
        for call in calls:
            self.assertIn('-j3', call)

    def test_vm_only_toolchain_and_eager_override(self):
        for compute, proof in [('no', 'no'), ('yes', 'yes')]:
            result, calls = self.run_build(compute, proof)
            self.assertEqual(result.returncode, 0, result.stderr)
            for call in calls:
                self.assertIn('COQEXTRAFLAGS=-w -abstract-large-number -native-compiler ' + compute, call)

    def test_failed_computation_build_stops_proof_build(self):
        result, calls = self.run_build(fail=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(len(calls), 1)


if __name__ == '__main__':
    unittest.main()
