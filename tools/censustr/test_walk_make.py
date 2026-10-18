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
        (self.root / 'tools').mkdir()
        shutil.copy(REPO / 'tools/time_command.py', self.root / 'tools/time_command.py')
        shutil.copy(REPO / 'tools/ensure_native.py', self.root / 'tools/ensure_native.py')
        (self.root / 'tools/censustr').mkdir()
        shutil.copy(REPO / 'tools/censustr/order_walk_units.py',
                    self.root / 'tools/censustr/order_walk_units.py')
        (self.root / 'tools/censustr/walk_costs.json').write_text(json.dumps({
            'units': 96, 'seconds': {'UnitTr_00': 1, 'UnitTr_01': 9}}))
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
with Path('prerequisite_args.jsonl').open('a') as f:
    f.write(json.dumps(sys.argv[1:])+'\\n')
''')
        self.submake.chmod(0o755)

    def write(self, relative, timestamp):
        path = self.root / 'theories/CensusTr' / relative
        path.write_text('test fixture only\n')
        os.utime(path, (timestamp, timestamp))

    def run_recipe(self, fail=None, native=None, units=96):
        env = dict(os.environ, PATH=str(self.bin) + os.pathsep + os.environ['PATH'])
        if fail:
            env['FAIL_UNIT'] = fail
        result = subprocess.run(
            [shutil.which('make'), '-f', str(REPO / 'Makefile'), 'census-tr-walk',
             'WALK_JOBS=1', 'WALK_CORES=1', 'BUILD_JOBS=1',
             'CENSUS_TR_UNITS=' + str(units),
             *([] if native is None else ['TR_PROOF_NATIVE=' + native]),
             'CENSUS_TR_PREREQ_JOBS=3', 'MAKE=' + str(self.submake)],
            cwd=self.root, env=env, capture_output=True, text=True, timeout=30)
        path = self.root / 'compiler_calls.txt'
        calls = path.read_text().splitlines() if path.exists() else []
        return result, calls

    def test_proof_only_changes_keep_units_and_use_batch_job_budget(self):
        result, calls = self.run_recipe()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(calls, ['Census_TheoremTr'])
        builds = [json.loads(line) for line in
                  (self.root / 'prerequisite_args.jsonl').read_text().splitlines()]
        self.assertEqual(len(builds), 2)
        for build in builds:
            self.assertIn('-j3', build)
        self.assertIn('theories/CensusTr/RunTr_WalkCompute.vo', builds[0])
        self.assertIn('theories/CensusTr/RepWLMBTr.vo', builds[0])
        self.assertIn('theories/Checkers/IRules/MetaTr.vo', builds[0])
        self.assertIn('COQEXTRAFLAGS= -native-compiler yes', builds[0])
        self.assertEqual(builds[1][-1], 'theories/CensusTr/RunTr_Split.vo')
        self.assertIn('COQEXTRAFLAGS= -native-compiler ondemand', builds[1])
        phases = [json.loads(line) for line in
                  (self.root / 'census_probes/proof-tr-times.jsonl').read_text().splitlines()]
        self.assertEqual([p['phase'] for p in phases],
                         ['computation-dependencies', 'proof-prerequisites',
                          'census-units', 'census-assembly'])
        self.assertTrue(all(p['exit_code'] == 0 for p in phases))

    def test_eager_native_override(self):
        result, _ = self.run_recipe(native='yes')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        builds = [json.loads(line) for line in
                  (self.root / 'prerequisite_args.jsonl').read_text().splitlines()]
        for build in builds:
            self.assertIn('COQEXTRAFLAGS= -native-compiler yes', build)

    def test_rebuild_changed_unit_source(self):
        self.write('Compute/UnitTr_00.v', 50)
        result, calls = self.run_recipe()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(calls, ['UnitTr_00', 'Census_TheoremTr'])

    def test_rebuild_changed_computation(self):
        self.write('RunTr_WalkCompute.vo', 50)
        result, calls = self.run_recipe()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(calls, ['UnitTr_01', 'UnitTr_00', 'Census_TheoremTr'])

    def test_different_unit_count_falls_back_without_dropping_units(self):
        self.write('RunTr_WalkCompute.vo', 50)
        result, calls = self.run_recipe(units=2)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(calls, ['UnitTr_00', 'UnitTr_01', 'Census_TheoremTr'])
        self.assertIn('using lexical order', result.stderr)

    def test_sorter_failure_stops_before_assembly_even_with_old_objects(self):
        (self.root / 'tools/censustr/order_walk_units.py').write_text('raise SystemExit(23)\n')
        result, calls = self.run_recipe()
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertEqual(calls, [])
        self.assertIn('Error 23', result.stderr)

    def test_failed_recompile_is_fatal_even_when_old_object_exists(self):
        self.write('Compute/UnitTr_00.v', 50)
        result, calls = self.run_recipe(fail='UnitTr_00')
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(calls, ['UnitTr_00'], result.stdout + result.stderr)
        phases = [json.loads(line) for line in
                  (self.root / 'census_probes/proof-tr-times.jsonl').read_text().splitlines()]
        self.assertEqual(phases[-1]['phase'], 'census-units')
        self.assertNotEqual(phases[-1]['exit_code'], 0)


if __name__ == '__main__':
    unittest.main()
