"""Synthetic instruction replay trust tests; successful stubs give no Coq credit."""
import json
from pathlib import Path
import shutil
import unittest
from unittest.mock import patch

import test_replay_observations as state_tests
import replay_instruction_observations as instruction

RUNNER = Path(__file__).with_name('replay_instruction_observations.py').resolve()


class ReplayInstructionObservationTests(unittest.TestCase):
    # Reuse only the synthetic fixture, leaving the state suite unchanged.
    records = state_tests.ReplayObservationTests.records
    row = state_tests.ReplayObservationTests.row
    write_spec = state_tests.ReplayObservationTests.write_spec
    run_job = state_tests.ReplayObservationTests.run_job
    assert_failed = state_tests.ReplayObservationTests.assert_failed

    def setUp(self):
        state_tests.ReplayObservationTests.setUp(self)
        self.runner = RUNNER
        checker = self.repo / 'wait42/theories/FiniteInstructionObservation.v'
        checker.write_text('(* synthetic instruction checker identity *)\n')
        checker.with_suffix('.vo').write_bytes(b'synthetic instruction checker artifact')
        # Exercise the HEADER probe's transitive import, rather than pretending
        # the instruction checker is an unconditional engine dependency.
        tool = self.tools / 'coqdep'
        tool.write_text(tool.read_text().replace(
            "if name == 'coqdep': sys.exit(0)",
            """if name == 'coqdep':
 for arg in args:
  if arg.endswith('DependencyProbe.v'):
   probe = Path(arg)
   if 'FiniteInstructionObservation' in probe.read_text():
    checker = Path.cwd() / 'wait42/theories/FiniteInstructionObservation.vo'
    print(str(probe.with_suffix('.vo')) + ': ' + str(checker))
 sys.exit(0)"""))

    def command(self, *extra):
        command = state_tests.ReplayObservationTests.command(self, *extra)
        command[1] = str(self.runner)
        return command

    def refresh_spec(self, count):
        state_tests.ReplayObservationTests.refresh_spec(self, count)
        spec = json.loads(self.spec.read_text())
        spec.update(beep_mode='instruction',
                    tail_invariant='total-state-mask-with-both-symbols-observed')
        self.spec.write_text(json.dumps(spec))

    def successful_run(self, *extra, **kwargs):
        result = self.run_job(*extra, **kwargs)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result

    def test_missing_or_wrong_semantics_fail_before_tools_and_output(self):
        for key, values in [('beep_mode', [None, 'state', True]),
                            ('tail_invariant', [None, 'instruction-mask', True])]:
            for value in values:
                with self.subTest(key=key, value=value):
                    self.write_spec([self.row()])
                    spec = json.loads(self.spec.read_text())
                    if value is None:
                        del spec[key]
                    else:
                        spec[key] = value
                    self.spec.write_text(json.dumps(spec))
                    self.assert_failed(self.run_job())
                    self.assertEqual(self.records(), [])
                    self.assertFalse(self.output.exists())

    def test_mask_is_four_state_bits_and_width_still_bounded(self):
        for field, value in [('tail_mask', '16'), ('tail_mask', '255'), ('width', '3')]:
            with self.subTest(field=field, value=value):
                self.write_spec([dict(self.row(), **{field: value})])
                self.assert_failed(self.run_job())
                self.assertEqual(self.records(), [])
                self.assertFalse(self.output.exists())

    def test_success_has_instruction_theorem_namespace_and_recursive_audit(self):
        self.write_spec([dict(self.row(), tail_mask='5')])
        self.successful_run('--memory-gib', '2')
        source = (self.output / 'Part000000.v').read_text()
        self.assertIn('FiniteInstructionObservation', source)
        self.assertIn('instruction_observation_batch_check cases', source)
        self.assertIn('instruction_observation_batch_completion cases', source)
        self.assertIn('WindowBoundTr tm', source)
        self.assertIn('(mask true false true false)', source)
        self.assertIn('Print Assumptions all_completions.', source)
        audits = [r for r in self.records() if r['tool'] == 'coqchk']
        self.assertEqual(len(audits), 1)
        argv = audits[0]['argv']
        self.assertEqual(argv[-1], 'BBBWait42InstructionObservation.Part000000')
        self.assertEqual(argv[argv.index('-bytecode-compiler') + 1], 'yes')
        self.assertFalse(any(a.startswith(('-norec', '-admit', '-unsafe')) for a in argv))
        self.assertLessEqual(audits[0]['memory'], 2 * 1024**3)
        manifest = json.loads((self.output / 'manifest.json').read_text())
        dependencies = manifest['bound']['dependencies']
        for path in (RUNNER, self.repo / 'wait42/theories/FiniteInstructionObservation.v',
                     self.repo / 'wait42/theories/FiniteInstructionObservation.vo'):
            self.assertIn(str(path), dependencies)
        self.assertFalse(manifest['coverage_proved'])

    def test_valid_resume_reuses_only_checked_instruction_receipts(self):
        self.write_spec([self.row()])
        self.successful_run()
        count = len(self.records())
        self.successful_run('--resume')
        self.assertEqual(len(self.records()), count)

    def test_instruction_checker_source_and_artifact_changes_reject_resume(self):
        for suffix in ('.v', '.vo'):
            with self.subTest(suffix=suffix):
                self.output = self.root / ('changed-' + suffix[1:])
                self.write_spec([self.row()])
                self.successful_run()
                count = len(self.records())
                checker = self.repo / ('wait42/theories/FiniteInstructionObservation' + suffix)
                original = checker.read_bytes()
                checker.write_bytes(original + b'\nchanged\n')
                self.assert_failed(self.run_job('--resume'))
                self.assertEqual(len(self.records()), count)
                checker.write_bytes(original)

    def test_adapter_source_changes_reject_resume(self):
        copied = self.root / 'copied-tools'
        copied.mkdir()
        for name in ('replay_observations.py', RUNNER.name):
            shutil.copyfile(RUNNER.with_name(name), copied / name)
        self.runner = copied / RUNNER.name
        self.write_spec([self.row()])
        self.successful_run()
        count = len(self.records())
        self.runner.write_bytes(self.runner.read_bytes() + b'\n# adapter identity changed\n')
        result = self.run_job('--resume')
        self.assert_failed(result)
        self.assertIn('resume identity mismatch', result.stderr)
        self.assertEqual(len(self.records()), count)

    def test_state_receipts_cannot_be_relabelled_as_instruction_receipts(self):
        # Both modes intentionally receive the exact same spec and TSV bytes.
        self.write_spec([self.row()])
        self.runner = RUNNER.with_name('replay_observations.py')
        self.successful_run()
        source = (self.output / 'Part000000.v').read_bytes()
        receipt = (self.output / 'Part000000.receipt.json').read_bytes()
        count = len(self.records())
        self.runner = RUNNER
        result = self.run_job('--resume')
        self.assert_failed(result)
        self.assertIn('resume identity mismatch', result.stderr)
        self.assertEqual(len(self.records()), count)
        self.assertEqual((self.output / 'Part000000.v').read_bytes(), source)
        self.assertEqual((self.output / 'Part000000.receipt.json').read_bytes(), receipt)

    def test_bad_axioms_audits_and_mutated_artifacts_receive_no_credit(self):
        for mode in ('axiom', 'fail_audit', 'missing_markers', 'mutate_source', 'mutate_vo'):
            with self.subTest(mode=mode):
                self.output = self.root / mode
                self.write_spec([self.row()])
                self.assert_failed(self.run_job(mode=mode))
                progress = json.loads((self.output / 'progress.json').read_text())
                self.assertEqual(progress['checked_families'], 0)
                self.assertFalse(progress['coverage_proved'])
                for receipt in self.output.glob('Part*.receipt.json'):
                    self.assertNotEqual(json.loads(receipt.read_text())['status'], 'checked')

    def test_adapter_restores_supervisor_and_selects_separate_default_spec(self):
        supervisor = instruction.supervisor
        keys = ('HEADER', 'NAMESPACE', 'render_part', 'load_input', 'dependency_closure')
        original = tuple(getattr(supervisor, key) for key in keys)
        captured = []
        def fake_main(argv):
            captured.append(argv)
            self.assertEqual(supervisor.NAMESPACE, instruction.NAMESPACE)
            self.assertIs(supervisor.render_part, instruction.render_part)
            raise ValueError('synthetic supervisor failure')
        with patch.object(supervisor, 'main', fake_main):
            with self.assertRaisesRegex(ValueError, 'synthetic supervisor failure'):
                instruction.main(['--output', 'out'])
        self.assertEqual(tuple(getattr(supervisor, key) for key in keys), original)
        self.assertEqual(captured[0][:2], ['--spec', str(supervisor.ROOT / 'wait42/research/instruction-observations.json')])
        self.assertIn('FiniteObservation.', supervisor.HEADER)
        self.assertEqual(supervisor.NAMESPACE, 'BBBWait42Observation')


if __name__ == '__main__':
    unittest.main()
