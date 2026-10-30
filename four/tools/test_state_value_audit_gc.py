"""Audit-only heap policy, failure records, and exact predecessor compatibility."""
import copy
from contextlib import redirect_stdout
import io
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import build_state_value as build


class AuditGCTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.root=Path(self.temp.name)
        self.tree=self.root/'tree';self.tree.mkdir()
        self.state=self.root/'state';self.state.mkdir()
        self.graph=SimpleNamespace(tree=self.tree,flags=[],profiles={})
        self.runtime={'binaries':{'coqc':{'path':'/unit-only/coqc'},'coqchk':{'path':'/unit-only/coqchk'}}}
        self.limits={'address_space_bytes':27*1024**3,'rss_guard_bytes':25*1024**3}
        self.source='(* Unit-only checker invocation fixture; no theorem credit. *)\n'
        self.output=redirect_stdout(io.StringIO());self.output.__enter__()

    def tearDown(self):
        self.output.__exit__(None,None,None);self.temp.cleanup()

    def invoke(self,env,checker):
        with patch.object(build,'phase_limits',return_value=self.limits), \
             patch.object(build,'selected_statement_check',return_value=self.source) as statement, \
             patch.object(build,'run_capped',side_effect=checker):
            result=build.checked_root(self.graph,self.state,self.runtime,env,
                'Example.Final.value','Example.Final','CheckFinal',120)
        statement.assert_called_once_with(self.graph,'Example.Final.value','Example.Final')
        return result

    def compiler(self,command,cwd,env,log,limits,timeout):
        self.assertEqual(command[0],'/unit-only/coqc')
        Path(log).write_text('Closed under the global context\n')
        (cwd/command[-1]).with_suffix('.vo').write_bytes(b'UNIT ONLY: not a Coq object')
        return {'exit_code':0,'command':command}

    def test_default_environment_is_copied_and_only_audit_gc_is_set(self):
        original={'PATH':'/same/path','SENTINEL':'unchanged'}
        audit=build.audit_environment(original)
        self.assertEqual(audit,{**original,'OCAMLRUNPARAM':'o=40,O=60'})
        self.assertEqual(original,{'PATH':'/same/path','SENTINEL':'unchanged'})

    def test_explicit_profiles_are_preserved_and_audit_override_wins(self):
        for value in ('o=80,O=150',''):
            with self.subTest(value=value):
                original={'OCAMLRUNPARAM':value}
                self.assertEqual(build.audit_environment(original)['OCAMLRUNPARAM'],value)
                override={**original,'STATE24_COQCHK_OCAMLRUNPARAM':'o=20,O=60'}
                self.assertEqual(build.audit_environment(override)['OCAMLRUNPARAM'],'o=20,O=60')
                self.assertEqual(original,{'OCAMLRUNPARAM':value})

    def test_full_recursive_checker_and_all_limits_remain_unchanged(self):
        calls=[];env={'PATH':'same'}
        def checker(command,cwd,environment,log,limits,timeout):
            calls.append((command,environment,limits,timeout))
            if command[0].endswith('coqc'):
                self.assertEqual(environment,env)
                return self.compiler(command,cwd,environment,log,limits,timeout)
            self.assertEqual(environment,{**env,'OCAMLRUNPARAM':'o=40,O=60'})
            self.assertEqual(command[:4],['/unit-only/coqchk','-silent','-bytecode-compiler','yes'])
            self.assertEqual(command[-1],'BBB24ValueReport.CheckFinal')
            self.assertNotIn('-admit',command);self.assertNotIn('-norec',command)
            self.assertEqual(limits,self.limits);self.assertEqual(timeout,120)
            Path(log).write_text('Unit-only simulated audit success\n')
            return {'exit_code':0,'command':command}
        result=self.invoke(env,checker)
        self.assertEqual(len(calls),2);self.assertEqual(env,{'PATH':'same'})
        self.assertEqual(result['mode'],'full-recursive');self.assertEqual(result['assumptions'],[])
        self.assertEqual(result['audit_execution']['ocamlrunparam'],'o=40,O=60')
        policy=json.loads((self.state/'CheckFinal-audit-policy.json').read_text())
        self.assertEqual(policy['rss_guard_bytes'],25*1024**3)
        self.assertIn('no proof credit',policy['status'])

    def test_audit_failure_is_recorded_and_propagated_without_success_gate(self):
        def checker(command,cwd,env,log,limits,timeout):
            if command[0].endswith('coqc'):return self.compiler(command,cwd,env,log,limits,timeout)
            Path(log).write_text('command supervisor was cancelled\n')
            raise RuntimeError('Child session exceeded RSS guard: '+str(log))
        with self.assertRaisesRegex(RuntimeError,'RSS guard'):self.invoke({},checker)
        failure=json.loads((self.state/'CheckFinal-audit-failure.json').read_text())
        self.assertEqual(failure['status'],'audit failed; no proof credit')
        self.assertEqual(failure['ocamlrunparam'],'o=40,O=60')
        self.assertIn('RSS guard',failure['error'])
        self.assertFalse((self.state/'final-gate.json').exists())
        self.assertFalse((self.tree/'four/theories/Value.v').exists())

    def test_compile_failure_prevents_audit_and_policy_success(self):
        calls=[]
        def checker(command,*args):
            calls.append(command);raise RuntimeError('Exact statement mismatch')
        with self.assertRaisesRegex(RuntimeError,'statement mismatch'):self.invoke({},checker)
        self.assertEqual(len(calls),1);self.assertTrue(calls[0][0].endswith('coqc'))
        self.assertFalse((self.state/'CheckFinal-audit-policy.json').exists())

    def test_retry_archives_old_failure_record(self):
        (self.state/'CheckFinal-audit-failure.json').write_text('{"old_failure": true}\n')
        def checker(command,cwd,env,log,limits,timeout):
            if command[0].endswith('coqc'):return self.compiler(command,cwd,env,log,limits,timeout)
            Path(log).write_text('Unit-only simulated audit success\n');return {'exit_code':0}
        self.invoke({},checker)
        self.assertFalse((self.state/'CheckFinal-audit-failure.json').exists())
        self.assertEqual(len(list((self.state/'prior-results').glob('CheckFinal-audit-failure.json.*'))),1)

    def test_trace_option_changes_only_checker_verbosity(self):
        def checker(command,cwd,env,log,limits,timeout):
            if command[0].endswith('coqc'):return self.compiler(command,cwd,env,log,limits,timeout)
            self.assertNotIn('-silent',command)
            self.assertEqual(command[:3],['/unit-only/coqchk','-bytecode-compiler','yes'])
            self.assertNotIn('-admit',command);self.assertNotIn('-norec',command)
            Path(log).write_text('Checking library: Example.Final\n')
            return {'exit_code':0}
        result=self.invoke({'STATE24_COQCHK_TRACE':'1'},checker)
        self.assertTrue(result['audit_execution']['trace_enabled'])

    def test_exact_provider_scheduler_receipts_can_migrate(self):
        previous={'manifest_sha256':'same sources','runtime_sha256':'same runtime','tree':'same tree',
                  'implementation':copy.deepcopy(build.AUDIT_PREDECESSOR)}
        current=copy.deepcopy(previous);current['implementation']['build_state_value.py']='new audit policy'
        (self.state/'build-identity.json').write_text(json.dumps(previous))
        build.resume_identity(self.state,current,True)
        self.assertEqual(json.loads((self.state/'build-identity.json').read_text()),current)
        for key in ('manifest_sha256','runtime_sha256','tree'):
            changed=copy.deepcopy(previous);changed[key]='changed'
            (self.state/'build-identity.json').write_text(json.dumps(changed))
            with self.assertRaises(ValueError):build.resume_identity(self.state,current,True)


if __name__=='__main__':unittest.main()
