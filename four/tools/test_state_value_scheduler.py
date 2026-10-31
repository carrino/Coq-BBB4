"""Memory-bounded provider concurrency and exact predecessor resume controls."""
import copy
from contextlib import redirect_stdout
import io
import json
from pathlib import Path
import tempfile
import threading
import unittest
from types import SimpleNamespace
from unittest.mock import patch

import build_state_value as build
import proof24_resources as resources
from proof24_common import PHASES, canonical, sha, write_json
from proof24_resources import phase_limits

GIB = 1024**3
SNAPSHOT = {'effective_limit_bytes': 32*GIB, 'reserve_bytes': 4*GIB,
            'available_bytes': 30*GIB, 'usable_bytes': 26*GIB}
PROFILES = {name: dict(row) for name, row in PHASES.items()}
PROFILES['provider'].update(address_space_mib=8192, rss_guard_mib=7168)


def graph_fixture(tree, count=8, phase='provider'):
    tree.mkdir()
    sources = [f'Row{i}.v' for i in range(count)]
    for source in sources:
        (tree/source).write_text('(* Unit-only fake compiler fixture; no theorem credit. *)\n')
    return SimpleNamespace(tree=tree, order=sources,
        sources={s: {'sha256': sha(tree/s)} for s in sources},
        deps={s: [] for s in sources}, module={s: s[:-2] for s in sources},
        phase={s: phase for s in sources}, paths=[], flags=[], profiles=copy.deepcopy(PROFILES),
        digest='fixed-source-manifest')


class SchedulerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.graph = graph_fixture(self.root/'tree')
        self.state = self.root/'state'; self.state.mkdir()
        self.runtime = {'binaries': {'coqc': {'path': '/fake-compiler-unit-only'}}}
        self.limits = patch.object(build, 'phase_limits', side_effect=lambda phase, jobs, profiles:
            phase_limits(phase, jobs, snapshot=SNAPSHOT, profiles=profiles))
        self.limits.start()
        self.cpu = patch.object(resources.os, 'cpu_count', return_value=8); self.cpu.start()
        self.disk = patch.object(build, 'check_disk'); self.disk.start()
        self.output = redirect_stdout(io.StringIO()); self.output.__enter__()

    def tearDown(self):
        self.output.__exit__(None,None,None)
        self.disk.stop(); self.limits.stop(); self.cpu.stop(); self.temp.cleanup()

    def run_graph(self, compiler, light=True):
        with patch.object(build, 'run_capped', side_effect=compiler):
            return build.compile_graph(self.graph, self.state, self.runtime, {}, 8, 10, 1, light)

    def compiler(self, command, cwd, env, log, limits, timeout, owner):
        source = command[-1]
        Path(log).write_text('Unit-only fake compiler success.\n')
        (cwd/Path(source).with_suffix('.vo')).write_bytes(b'UNIT ONLY: not a Coq object')
        return {'exit_code': 0, 'command': command, 'sampled_maximum_owned_process_rss_bytes': 1}

    def test_32gib_budgets_allow_eight_light_and_two_full_workers(self):
        light = phase_limits('ordinary',8,snapshot=SNAPSHOT,profiles=PROFILES)
        heavy = phase_limits('provider',8,snapshot=SNAPSHOT,profiles=PROFILES)
        self.assertEqual(light['workers'],8); self.assertEqual(heavy['workers'],2)
        for limits in (light,heavy):
            self.assertLessEqual(limits['workers']*limits['rss_guard_bytes'],SNAPSHOT['usable_bytes'])
        self.assertEqual(light['address_space_bytes'],2*GIB)
        self.assertEqual(heavy['address_space_bytes'],8*GIB)

    def test_all_eight_light_tasks_can_run_together(self):
        barrier = threading.Barrier(8, timeout=5)
        seen=[]
        def compiler(*args):
            seen.append(args[4]['address_space_bytes'])
            barrier.wait()
            return self.compiler(*args)
        rows,counts = self.run_graph(compiler)
        self.assertEqual(seen,[2*GIB]*8)
        self.assertEqual(counts['fresh_compiled'],8)
        self.assertEqual(counts['provider_memory_retries'],0)
        self.assertEqual({r['resource_profile'] for r in rows.values()},{'provider-light'})
        build.verify_receipts(self.graph,self.state,canonical(self.runtime))

    def test_only_memory_limited_file_retries_after_light_batch(self):
        barrier=threading.Barrier(8,timeout=5); active=set(); lock=threading.Lock(); seen=[]
        def compiler(*args):
            command,cwd,env,log,limits,timeout,owner=args
            source=command[-1]; light=limits['address_space_bytes']==2*GIB
            if light:
                with lock: active.add(source)
                barrier.wait()
                with lock: active.remove(source)
                if source=='Row0.v':
                    (cwd/'Row0.vo').write_bytes(b'FAILED PARTIAL OUTPUT')
                    Path(log).write_text('Fatal error: out of memory\n')
                    raise RuntimeError('Command failed, exit 250: '+str(log))
            else:
                self.assertFalse(active)
                self.assertEqual(source,'Row0.v')
                self.assertFalse((cwd/'Row0.vo').exists())
                seen.append(source)
            return self.compiler(*args)
        rows,counts=self.run_graph(compiler)
        self.assertEqual(seen,['Row0.v']); self.assertEqual(counts['provider_memory_retries'],1)
        self.assertEqual(rows['Row0.v']['resource_profile'],'provider')
        self.assertEqual(rows['Row0.v']['resource_limits']['address_space_bytes'],8*GIB)
        self.assertIn('light_memory_retry',rows['Row0.v'])
        self.assertTrue((self.state/'compile/Row0.light.log').is_file())
        build.verify_receipts(self.graph,self.state,canonical(self.runtime))

    def test_statement_error_never_retries_and_cancels_owners(self):
        barrier=threading.Barrier(8,timeout=5); owners=[]; seen=[]
        def compiler(*args):
            command,cwd,env,log,limits,timeout,owner=args
            owners.append(owner); seen.append(limits['address_space_bytes']); barrier.wait()
            if command[-1]=='Row0.v':
                Path(log).write_text('Error: statement is false\n')
                raise RuntimeError('Command failed, exit 1: '+str(log))
            return self.compiler(*args)
        with self.assertRaisesRegex(RuntimeError,'exit 1'):
            self.run_graph(compiler)
        self.assertEqual(seen,[2*GIB]*8)
        self.assertTrue(all(o.cancelled.is_set() for o in owners))
        self.assertFalse((self.state/'receipts/Row0.json').exists())

    def test_other_failures_are_not_memory_retries(self):
        log=self.root/'failure.log'; log.write_text('Error: false statement\n')
        for message in ['Command timed out: x','Disk headroom fell below 1 GiB: x',
                        'Machine RAM headroom fell below safety reserve: x',
                        'Command failed, exit 1: x']:
            self.assertFalse(build.memory_limited_failure(RuntimeError(message),log))
        self.assertTrue(build.memory_limited_failure(
            RuntimeError('Child session exceeded RSS guard: x'),log))
        for message in ('Fatal error: exception Out_of_memory', 'Error: Out of memory.'):
            log.write_text(message+'\n')
            self.assertTrue(build.memory_limited_failure(RuntimeError('Command failed, exit 2: x'),log))

    def test_default_mode_keeps_full_provider_cap(self):
        seen=[]
        def compiler(*args):
            seen.append((args[4]['workers'],args[4]['address_space_bytes']))
            return self.compiler(*args)
        _,counts=self.run_graph(compiler,light=False)
        self.assertEqual(seen,[(2,8*GIB)]*8)
        self.assertEqual(counts['provider_light_attempts'],0)

    def test_existing_receipts_are_reused_and_changed_objects_rebuilt(self):
        rows,_=self.run_graph(self.compiler,light=False)
        with patch.object(build,'run_capped',side_effect=AssertionError('Must reuse exact receipts')):
            resumed,counts=build.compile_graph(self.graph,self.state,self.runtime,{},8,10,1,True)
        self.assertEqual(resumed,rows);self.assertEqual(counts['exact_receipts_resumed'],8)
        (self.graph.tree/'Row2.vo').write_bytes(b'CORRUPTED OBJECT')
        _,counts=self.run_graph(self.compiler)
        self.assertEqual(counts['fresh_compiled'],1)
        self.assertEqual(counts['exact_receipts_resumed'],7)

    def test_checks_and_assembly_keep_their_original_limits(self):
        for phase in ('checks','assembly'):
            with self.subTest(phase=phase):
                self.graph.phase={s:phase for s in self.graph.order}
                for p in (self.state/'receipts').glob('*.json'): p.unlink()
                seen=[]
                def compiler(*args):
                    seen.append((args[4]['workers'],args[4]['address_space_bytes']))
                    return self.compiler(*args)
                self.run_graph(compiler)
                expected=phase_limits(phase,8,snapshot=SNAPSHOT,profiles=PROFILES)
                self.assertEqual(seen,[(expected['workers'],expected['address_space_bytes'])]*8)


class ResumeUpgradeTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.state=Path(self.temp.name)
        self.old={'manifest_sha256':'same-sources','runtime_sha256':'same-runtime',
                  'tree':'same-tree','implementation':copy.deepcopy(build.SCHEDULER_PREDECESSOR)}
        self.new=copy.deepcopy(self.old);self.new['implementation']['build_state_value.py']='reviewed-new-scheduler'
        self.initial=self.state/'build-identity.json'

    def tearDown(self):self.temp.cleanup()

    def test_exact_predecessor_upgrade_keeps_receipts_and_requires_final_audits(self):
        write_json(self.initial,self.old)
        receipt=self.state/'existing-receipt.json';receipt.write_text('untouched')
        with redirect_stdout(io.StringIO()):build.resume_identity(self.state,self.new,True)
        self.assertEqual(json.loads(self.initial.read_text()),self.new)
        self.assertEqual(receipt.read_text(),'untouched')
        record=json.loads((self.state/'scheduler-upgrade.json').read_text())
        self.assertTrue(record['fresh_object_receipt_validation_required'])
        self.assertTrue(record['fresh_final_recursive_audits_required'])
        build.resume_identity(self.state,self.new,False)

    def test_every_other_identity_change_is_rejected_without_mutation(self):
        cases=[]
        for key in ('manifest_sha256','runtime_sha256','tree'):
            changed=copy.deepcopy(self.old);changed[key]='changed';cases.append(changed)
        for name in self.old['implementation']:
            changed=copy.deepcopy(self.old);changed['implementation'][name]='unknown';cases.append(changed)
        changed=copy.deepcopy(self.old);changed['extra']='unreviewed';cases.append(changed)
        for previous in cases:
            with self.subTest(previous=previous):
                write_json(self.initial,previous)
                with self.assertRaisesRegex(ValueError,'Resume identity differs'):
                    build.resume_identity(self.state,self.new,True)
                self.assertEqual(json.loads(self.initial.read_text()),previous)
                self.assertFalse((self.state/'scheduler-upgrade.json').exists())
        write_json(self.initial,self.old)
        with self.assertRaises(ValueError):build.resume_identity(self.state,self.new,False)
        for name in ('proof24_common.py','proof24_resources.py','report_state_value.py'):
            changed=copy.deepcopy(self.new);changed['implementation'][name]='new-execution-or-verifier'
            with self.assertRaises(ValueError):build.resume_identity(self.state,changed,True)
        self.assertEqual(json.loads(self.initial.read_text()),self.old)


if __name__=='__main__':unittest.main()
