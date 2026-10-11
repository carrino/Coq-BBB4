#!/usr/bin/env python3
"""Exercise the real walk recipe's freshness and failure handling.

A temporary tree and recording compiler isolate build scheduling from the
expensive Coq computation. No fixture objects enter the proof workspace.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

REPO = Path(__file__).resolve().parents[2]


class WalkRecipeTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='censustr-make-')
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.compute = self.root / 'theories/CensusTr/Compute'
        self.compute.mkdir(parents=True)
        self.bin = self.root / 'bin'
        self.bin.mkdir()
        (self.root / '_CoqProject').write_text('')
        (self.root / 'Makefile.coq').write_text('# scheduling fixture\n')
        self.write('RunTr_WalkCompute.vo', 30)
        self.write('RunTr_Split.vo', 80)
        for unit in ['00', '01']:
            self.write(f'Compute/UnitTr_{unit}.v', 10)
            self.write(f'Compute/UnitTr_{unit}.vo', 40)
        self.write('Compute/Census_TheoremTr.v', 10)
        coqc = self.bin / 'coqc'
        coqc.write_text('''#!/usr/bin/env python3
import os,sys
from pathlib import Path
p=Path(sys.argv[-1])
with open('compiler_calls.txt','a') as f:f.write(p.stem+'\\n')
if os.environ.get('FAIL_UNIT')==p.stem:raise SystemExit(9)
p.with_suffix('.vo').write_text('test fixture only')
''')
        coqc.chmod(0o755)
        self.submake = self.bin / 'record_make'
        self.submake.write_text('''#!/usr/bin/env python3
import json,sys
from pathlib import Path
Path('prerequisite_args.json').write_text(json.dumps(sys.argv[1:]))
''')
        self.submake.chmod(0o755)

    def write(self, relative, timestamp):
        path = self.root / 'theories/CensusTr' / relative
        path.write_text('test fixture only\n')
        os.utime(path, (timestamp, timestamp))

    def run_recipe(self, fail=None):
        env = dict(os.environ, PATH=str(self.bin) + os.pathsep + os.environ['PATH'])
        if fail:
            env['FAIL_UNIT'] = fail
        result = subprocess.run(
            [shutil.which('make'), '-f', str(REPO / 'Makefile'), 'census-tr-walk',
             'WALK_JOBS=1', 'WALK_CORES=1', 'BUILD_JOBS=1',
             'CENSUS_TR_PREREQ_JOBS=3', 'MAKE=' + str(self.submake)],
            cwd=self.root, env=env, capture_output=True, text=True, timeout=30)
        path = self.root / 'compiler_calls.txt'
        calls = path.read_text().splitlines() if path.exists() else []
        return result, calls

    def test_proof_only_changes_keep_units_and_use_batch_job_budget(self):
        result, calls = self.run_recipe()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(calls, ['Census_TheoremTr'])
        self.assertIn('-j3', json.loads((self.root / 'prerequisite_args.json').read_text()))

    def test_rebuild_changed_unit_source(self):
        self.write('Compute/UnitTr_00.v', 50)
        result, calls = self.run_recipe()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(calls, ['UnitTr_00', 'Census_TheoremTr'])

    def test_rebuild_changed_computation(self):
        self.write('RunTr_WalkCompute.vo', 50)
        result, calls = self.run_recipe()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(calls, ['UnitTr_00', 'UnitTr_01', 'Census_TheoremTr'])

    def test_failed_recompile_is_fatal_even_when_old_object_exists(self):
        self.write('Compute/UnitTr_00.v', 50)
        result, calls = self.run_recipe(fail='UnitTr_00')
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(calls, ['UnitTr_00'], result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
