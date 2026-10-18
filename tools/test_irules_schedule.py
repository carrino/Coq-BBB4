#!/usr/bin/env python3
"""Check memory-limited state parts in make's actual dependency graph."""
from pathlib import Path
import os
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class IRulesScheduleTests(unittest.TestCase):
    def test_memory_columns(self):
        names = [str(p.relative_to(ROOT).with_suffix('.vo'))
                 for p in sorted((ROOT / 'theories/Machines/IRulesStateParts').glob('*.v'))]
        self.assertEqual(len(names), 34)
        for jobs in (1, 2, 3, 4, 8, 34, 40):
            with self.subTest(jobs=jobs), tempfile.TemporaryDirectory() as tmp:
                makefile = Path(tmp) / 'Makefile'
                makefile.write_text(
                    'all: ' + ' '.join(names) + '\n' +
                    f'include {ROOT / "Makefile.coq.local"}\n' +
                    '\n'.join(f'{n}:\n\t@true' for n in names) + '\n')
                result = subprocess.run(
                    ['make', '-np', '-f', str(makefile), f'IRULES_JOBS={jobs}'],
                    cwd=ROOT, capture_output=True, text=True, check=True)
                edges = {name: set() for name in names}
                for line in result.stdout.splitlines():
                    head, _, tail = line.partition(':')
                    if head in edges:
                        edges[head].update(n for n in tail.split() if n in edges)
                        self.assertTrue(not tail.strip() or tail.lstrip().startswith('|'))
                for i, name in enumerate(names):
                    self.assertEqual(edges[name], {names[i - jobs]} if i >= jobs else set())
                    for dep in edges[name]:
                        self.assertLess(names.index(dep), i)
                # The exact predecessor relation gives disjoint ascending
                # chains, hence exactly this concurrency limit.
                self.assertEqual(sum(not deps for deps in edges.values()), min(jobs, len(names)))

    def test_invalid_limit_stops_before_build_recipe(self):
        for jobs in ('0', 'bad'):
            with self.subTest(jobs=jobs), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                marker = root / 'build-recipe-ran'
                makefile = root / 'Makefile'
                makefile.write_text(
                    f'all:\n\t@touch "{marker}"\n'
                    f'include {ROOT / "Makefile.coq.local"}\n')
                result = subprocess.run(
                    ['make', '-f', str(makefile), f'IRULES_JOBS={jobs}'],
                    cwd=ROOT, capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn('Cannot generate IRules state schedule', result.stderr)
                self.assertFalse(marker.exists(), 'make reached a build recipe')

    def test_generator_failure_after_partial_output_stops_build(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'tools').mkdir()
            (root / 'tools/gen_irules_state_parts.py').write_text(
                "import sys\nsys.stdout.write('target.vo=predecessor.vo')\nraise SystemExit(9)\n")
            (root / 'Makefile').write_text(
                'all:\n\t@touch build-recipe-ran\n'
                f'include {ROOT / "Makefile.coq.local"}\n')
            result = subprocess.run(
                ['make', 'IRULES_JOBS=2'], cwd=root, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('Cannot generate IRules state schedule', result.stderr)
            self.assertFalse((root / 'build-recipe-ran').exists())

    def test_default_resources_and_schedule_are_each_computed_once(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'tools').mkdir()
            for name, marker, output in [
                    ('proof_resources.py', 'resource-calls', '2'),
                    ('gen_irules_state_parts.py', 'schedule-calls', '')]:
                (root / 'tools' / name).write_text(
                    f"with open('{marker}', 'a') as f: f.write('called\\n')\n"
                    f'print({output!r})\n')
            (root / 'Makefile').write_text(
                'all:\n\t@echo $(IRULES_JOBS) $(IRULES_JOBS) '
                '$(IRULES_STATE_SCHEDULE) $(IRULES_STATE_SCHEDULE)\n'
                f'include {ROOT / "Makefile.coq.local"}\n')
            env = dict(os.environ)
            for name in ('IRULES_JOBS', 'MAKEFLAGS', 'MFLAGS'):
                env.pop(name, None)
            result = subprocess.run(['make'], cwd=root, env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout.strip(), '2 2')
            for marker in ('resource-calls', 'schedule-calls'):
                self.assertEqual((root / marker).read_text(), 'called\n')


if __name__ == '__main__':
    unittest.main()
