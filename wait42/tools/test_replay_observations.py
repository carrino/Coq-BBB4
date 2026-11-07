"""Exercise the replay trust boundary with synthetic tools, never claiming Coq credit."""
import csv
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest

RUNNER = Path(__file__).with_name('replay_observations.py').resolve()
STUB = r'''#!/usr/bin/env python3
import fcntl, hashlib, json, os
from pathlib import Path
import resource, subprocess, sys, time
name = Path(sys.argv[0]).name
args = sys.argv[1:]
if any(a in ('--version', '-v') for a in args):
 print('The Coq Proof Assistant, version synthetic-test-1'); sys.exit(0)
if '-where' in args:
 print(os.environ['OBS_STUB_COQLIB']); sys.exit(0)
if name == 'coqdep': sys.exit(0)
with open(os.environ['OBS_STUB_LOG'], 'a') as log:
 fcntl.flock(log, fcntl.LOCK_EX)
 log.write(json.dumps({'tool': name, 'argv': args, 'pid': os.getpid(),
                       'memory': resource.getrlimit(resource.RLIMIT_AS)[0]})+'\n')
mode = os.environ.get('OBS_STUB_MODE', '')
if name == 'coqchk':
 if mode == 'mutate_vo':
  artifact = Path(os.environ['OBS_STUB_OUTPUT']) / (args[-1].split('.')[-1] + '.vo')
  artifact.write_bytes(artifact.read_bytes() + b'changed during audit')
 if mode == 'fail_audit': sys.exit(17)
 print('Modules were successfully checked'); sys.exit(0)
if mode in ('sleep_spawn', 'sleep'):
 if mode == 'sleep_spawn':
  child = subprocess.Popen([sys.executable, '-c', 'import time;time.sleep(90)'])
  Path(os.environ['OBS_STUB_CHILD']).write_text(str(child.pid))
 time.sleep(90)
if mode == 'fail_compile': sys.exit(19)
for src in [Path(a) for a in args if a.endswith('.v')]:
 if mode != 'missing_vo': src.with_suffix('.vo').write_bytes(hashlib.sha256(src.read_bytes()).digest())
if mode == 'missing_markers': sys.exit(0)
if mode == 'duplicate_markers': print('OBSERVATION_ASSUMPTIONS_BEGIN')
if mode == 'mutate_source':
 for src in [Path(a) for a in args if a.endswith('.v')]: src.write_bytes(src.read_bytes() + b'\n(* changed after compilation *)\n')
print('OBSERVATION_ASSUMPTIONS_BEGIN')
if mode == 'axiom': print('Axioms:\nevil : False')
elif mode == 'funext': print('Axioms:\nFunctionalExtensionality.functional_extensionality_dep\n  : forall A : Type, A -> A')
else: print('Closed under the global context')
print('OBSERVATION_ASSUMPTIONS_END')
'''


class ReplayObservationTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.tools = self.root / 'bin'
        self.tools.mkdir()
        for name in ('coqc', 'coqchk', 'coqdep'):
            path = self.tools / name
            path.write_text(STUB)
            path.chmod(0o755)
        self.coqlib = self.root / 'coqlib'
        (self.coqlib / 'theories').mkdir(parents=True)
        self.repo = self.root / 'repo'
        generic = self.repo / 'wait42/theories/FiniteObservation.v'
        generic.parent.mkdir(parents=True)
        generic.write_text('(* synthetic checker identity *)\n')
        generic.with_suffix('.vo').write_bytes(b'synthetic checker artifact')
        self.source = self.root / 'input.tsv'
        self.spec = self.root / 'spec.json'
        self.output = self.root / 'out'
        self.log = self.root / 'tools.jsonl'
        self.child = self.root / 'child.pid'
        self.env = dict(os.environ, OBS_STUB_LOG=str(self.log),
                        OBS_STUB_CHILD=str(self.child), OBS_STUB_COQLIB=str(self.coqlib))

    def records(self):
        if not self.log.exists(): return []
        return [json.loads(line) for line in self.log.read_text().splitlines()]

    def command(self, *extra):
        return [sys.executable, str(RUNNER), '--spec', str(self.spec),
                '--output', str(self.output), '--coqc', str(self.tools / 'coqc'),
                '--coqchk', str(self.tools / 'coqchk'), '--coqdep', str(self.tools / 'coqdep'),
                '--coqlib', str(self.coqlib), '--repo-root', str(self.repo), *extra]

    def run_job(self, *extra, mode='', timeout=20):
        return subprocess.run(self.command(*extra), env=dict(self.env, OBS_STUB_MODE=mode, OBS_STUB_OUTPUT=str(self.output)),
                              capture_output=True, text=True, timeout=timeout, check=False)

    def wait_for(self, predicate, process, timeout=8):
        end = time.monotonic() + timeout
        while time.monotonic() < end:
            if predicate(): return
            if process.poll() is not None:
                stdout, stderr = process.communicate()
                self.fail(f'runner exited before ready: {process.returncode}\n{stdout}\n{stderr}')
            time.sleep(.02)
        self.fail('runner did not become ready')

    def assert_dead(self, pid):
        end = time.monotonic() + 3
        while time.monotonic() < end:
            stat = Path(f'/proc/{pid}/stat')
            if not stat.exists() or stat.read_text().split()[2] == 'Z': return
            time.sleep(.02)
        self.fail(f'child process {pid} survived runner cleanup')

    def row(self, index=0):
        writes = [(index >> i) & 1 for i in range(8)]
        transitions = [f'{writes[i]}R{"ABCD"[(i // 2 + 1) % 4]}' for i in range(8)]
        machine = '_'.join(''.join(transitions[i:i+2]) for i in range(0, 8, 2))
        return dict(source_index=str(index), machine=machine, ptr='4', width='2', tail_mask='0')

    def write_spec(self, rows):
        with self.source.open('w') as stream:
            writer = csv.DictWriter(stream, ['source_index', 'machine', 'ptr', 'width', 'tail_mask'],
                                    delimiter='\t', lineterminator='\n')
            writer.writeheader()
            writer.writerows(rows)
        self.refresh_spec(len(rows))

    def refresh_spec(self, count):
        data = dict(schema_version=1, input=self.source.name,
                    input_sha256=hashlib.sha256(self.source.read_bytes()).hexdigest(),
                    rows=count, cutoff=0, upper_width=2, default_batch_size=2)
        self.spec.write_text(json.dumps(data))

    def assert_failed(self, result):
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_malformed_and_duplicate_source_fail_before_tools(self):
        for mutation in ('machine', 'ptr', 'width', 'tail_mask', 'duplicate', 'duplicate_index', 'ragged'):
            with self.subTest(mutation=mutation):
                row = self.row()
                rows = [row]
                if mutation == 'duplicate': rows.append(dict(row, source_index='1'))
                elif mutation == 'duplicate_index': rows.append(dict(self.row(1), source_index='0'))
                elif mutation != 'ragged':
                    row[mutation] = {'machine': '0RB---_INJECT', 'ptr': '5', 'width': '-1', 'tail_mask': '16'}[mutation]
                self.write_spec(rows)
                if mutation == 'ragged':
                    self.source.write_text(self.source.read_text() + 'broken\trow\n')
                    self.refresh_spec(len(rows)+1)
                result = self.run_job()
                self.assert_failed(result)
                self.assertEqual(self.records(), [], result.stdout + result.stderr)

    def test_missing_and_duplicate_columns_fail_before_tools(self):
        for header in ('source_index\tmachine\tptr\twidth',
                       'source_index\tmachine\tptr\twidth\ttail_mask\tptr'):
            with self.subTest(header=header):
                self.write_spec([self.row()])
                values = ['0', '0RB0RB_0RC0RC_0RD0RD_0RA0RA', '4', '2', '0', '4']
                self.source.write_text(header + '\n' + '\t'.join(values[:len(header.split('\t'))]) + '\n')
                self.refresh_spec(1)
                self.assert_failed(self.run_job())
                self.assertEqual(self.records(), [])

    def test_nonfinite_resource_budgets_are_rejected_before_tools(self):
        self.write_spec([self.row()])
        for flag in ('--timeout', '--max-hours', '--memory-gib'):
            for value in ('nan', 'inf'):
                with self.subTest(flag=flag, value=value):
                    self.assert_failed(self.run_job(flag, value))
                    self.assertEqual(self.records(), [])

    def test_source_hash_tamper_fails_before_tools(self):
        self.write_spec([self.row()])
        self.source.write_text(self.source.read_text() + '\n')
        self.assert_failed(self.run_job())
        self.assertEqual(self.records(), [])

    def test_success_uses_recursive_bytecode_audit_and_memory_cap(self):
        self.write_spec([self.row(0), self.row(1), self.row(2)])
        result = self.run_job('--jobs', '2', '--batch-size', '2', '--memory-gib', '2')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        audits = [r for r in self.records() if r['tool'] == 'coqchk']
        self.assertEqual(len(audits), 2)
        progress = json.loads((self.output / 'progress.json').read_text())
        self.assertEqual(progress['checked_families'], 3)
        self.assertEqual(progress['checked_batches'], 2)
        self.assertEqual(progress['failed_batches'], 0)
        self.assertFalse(progress['coverage_proved'])
        for record in audits:
            argv = record['argv']
            self.assertIn('-bytecode-compiler', argv)
            self.assertEqual(argv[argv.index('-bytecode-compiler') + 1], 'yes')
            self.assertFalse(any(arg.startswith(('-norec', '-admit', '-unsafe')) for arg in argv))
            self.assertGreater(record['memory'], 0)
            self.assertLessEqual(record['memory'], 2 * 1024**3)

    def test_inherited_funext_is_allowed(self):
        self.write_spec([self.row()])
        result = self.run_job(mode='funext')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        progress = json.loads((self.output / 'progress.json').read_text())
        self.assertEqual(progress['checked_families'], 1)

    def test_eight_workers_count_only_audited_families(self):
        self.write_spec([self.row(i) for i in range(8)])
        result = self.run_job('--jobs', '8', '--batch-size', '1')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        progress = json.loads((self.output / 'progress.json').read_text())
        self.assertEqual(progress['checked_families'], 8)
        self.assertEqual(progress['checked_batches'], 8)
        self.assertEqual(progress['failed_batches'], 0)
        self.assertFalse(progress['coverage_proved'])
        self.assertEqual(len([r for r in self.records() if r['tool'] == 'coqchk']), 8)

    def test_bounded_run_leaves_remaining_families_pending(self):
        self.write_spec([self.row(i) for i in range(5)])
        result = self.run_job('--jobs', '1', '--batch-size', '2', '--max-batches', '1')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        progress = json.loads((self.output / 'progress.json').read_text())
        self.assertEqual(progress['checked_families'], 2)
        self.assertEqual(progress['pending_batches'], 2)
        self.assertFalse(progress['coverage_proved'])

    def test_valid_resume_does_not_replay(self):
        self.write_spec([self.row()])
        first = self.run_job()
        self.assertEqual(first.returncode, 0, first.stdout + first.stderr)
        count = len(self.records())
        second = self.run_job('--resume')
        self.assertEqual(second.returncode, 0, second.stdout + second.stderr)
        self.assertEqual(len(self.records()), count)

    def test_resume_changed_identity_fails(self):
        self.write_spec([self.row()])
        first = self.run_job()
        self.assertEqual(first.returncode, 0, first.stdout + first.stderr)
        count = len(self.records())
        self.write_spec([self.row(1)])
        self.assert_failed(self.run_job('--resume'))
        self.assertEqual(len(self.records()), count)

    def test_resume_changed_cutoff_or_batch_partition_fails(self):
        for change in ('cutoff', 'partition'):
            with self.subTest(change=change):
                self.output = self.root / change
                self.write_spec([self.row(0), self.row(1)])
                first = self.run_job('--batch-size', '2')
                self.assertEqual(first.returncode, 0, first.stdout + first.stderr)
                count = len(self.records())
                args = ['--resume', '--batch-size', '2']
                if change == 'cutoff':
                    spec = json.loads(self.spec.read_text())
                    spec['cutoff'] = 1
                    self.spec.write_text(json.dumps(spec))
                else:
                    args[-1] = '1'
                self.assert_failed(self.run_job(*args))
                self.assertEqual(len(self.records()), count)

    def test_resume_changed_checker_or_tool_fails(self):
        for target in ('checker_source', 'checker_vo', 'tool'):
            with self.subTest(target=target):
                self.output = self.root / target
                self.write_spec([self.row()])
                first = self.run_job()
                self.assertEqual(first.returncode, 0, first.stdout + first.stderr)
                count = len(self.records())
                path = {'checker_source': self.repo / 'wait42/theories/FiniteObservation.v',
                        'checker_vo': self.repo / 'wait42/theories/FiniteObservation.vo',
                        'tool': self.tools / 'coqc'}[target]
                original = path.read_bytes()
                path.write_bytes(original + b'\n# changed identity\n')
                self.assert_failed(self.run_job('--resume'))
                self.assertEqual(len(self.records()), count)
                path.write_bytes(original)

    def test_resume_unchecked_audit_claim_fails(self):
        for tamper in ('audit_command', 'audit_status', 'compile_status'):
            with self.subTest(tamper=tamper):
                self.output = self.root / tamper
                self.write_spec([self.row()])
                first = self.run_job()
                self.assertEqual(first.returncode, 0, first.stdout + first.stderr)
                count = len(self.records())
                path = next(self.output.glob('Part*.receipt.json'))
                receipt = json.loads(path.read_text())
                if tamper == 'audit_command':
                    receipt['audit']['command'].append('-norec')
                else:
                    receipt['audit' if tamper == 'audit_status' else 'compile']['status'] = 'timeout'
                path.write_text(json.dumps(receipt))
                self.assert_failed(self.run_job('--resume'))
                self.assertEqual(len(self.records()), count)

    def test_resume_changed_receipt_identity_fails(self):
        self.write_spec([self.row()])
        first = self.run_job()
        self.assertEqual(first.returncode, 0, first.stdout + first.stderr)
        count = len(self.records())
        path = next(self.output.glob('Part*.receipt.json'))
        receipt = json.loads(path.read_text())
        receipt['identity'] = 'tampered identity'
        path.write_text(json.dumps(receipt))
        self.assert_failed(self.run_job('--resume'))
        self.assertEqual(len(self.records()), count)

    def test_resume_changed_artifact_fails(self):
        self.write_spec([self.row()])
        first = self.run_job()
        self.assertEqual(first.returncode, 0, first.stdout + first.stderr)
        count = len(self.records())
        artifact = next(self.output.glob('Part*.vo'))
        artifact.write_bytes(b'tampered')
        self.assert_failed(self.run_job('--resume'))
        self.assertEqual(len(self.records()), count)

    def test_failures_never_receive_success_receipt(self):
        for mode in ('fail_compile', 'fail_audit', 'axiom', 'missing_markers', 'duplicate_markers', 'missing_vo', 'mutate_source', 'mutate_vo'):
            with self.subTest(mode=mode):
                self.output = self.root / mode
                self.write_spec([self.row()])
                result = self.run_job(mode=mode)
                self.assert_failed(result)
                receipts = [json.loads(p.read_text()) for p in self.output.glob('Part*.receipt.json')]
                progress = json.loads((self.output / 'progress.json').read_text())
                self.assertEqual(progress['checked_families'], 0)
                self.assertFalse(any(r.get('status') in ('passed', 'success', 'proved', 'checked') for r in receipts))

    def test_failed_audit_resume_reproves_and_preserves_attempt(self):
        self.write_spec([self.row()])
        self.assert_failed(self.run_job(mode='fail_audit'))
        result = self.run_job('--resume')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(sum(r['tool'] == 'coqc' for r in self.records()), 2)
        self.assertEqual(sum(r['tool'] == 'coqchk' for r in self.records()), 2)
        progress = json.loads((self.output / 'progress.json').read_text())
        self.assertEqual(progress['checked_families'], 1)
        archived = list((self.output / 'attempts').glob('*/Part*.receipt.json'))
        self.assertEqual(len(archived), 1)
        self.assertEqual(json.loads(archived[0].read_text())['status'], 'failed')

    def test_timeout_kills_spawned_descendants(self):
        self.write_spec([self.row()])
        result = self.run_job('--timeout', '0.5', mode='sleep_spawn', timeout=12)
        self.assert_failed(result)
        self.assertTrue(self.child.exists(), result.stdout + result.stderr)
        self.assert_dead(int(self.child.read_text()))
        self.assertEqual(json.loads((self.output / 'progress.json').read_text())['checked_families'], 0)

    def test_output_lock_rejects_concurrent_writer_and_sigint_cleans_children(self):
        self.write_spec([self.row()])
        first = subprocess.Popen(self.command('--timeout', '30'),
                                 env=dict(self.env, OBS_STUB_MODE='sleep_spawn'),
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        self.addCleanup(lambda: first.kill() if first.poll() is None else None)
        self.wait_for(self.child.exists, first)
        child_pid = int(self.child.read_text())
        count = len(self.records())
        second = self.run_job('--resume')
        self.assert_failed(second)
        self.assertEqual(len(self.records()), count)
        first.send_signal(signal.SIGINT)
        first.communicate(timeout=10)
        self.assertNotEqual(first.returncode, 0)
        self.assert_dead(child_pid)
        self.assertEqual(json.loads((self.output / 'progress.json').read_text())['checked_families'], 0)



if __name__ == '__main__': unittest.main()
