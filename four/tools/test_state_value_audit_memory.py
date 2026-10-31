"""Audit-only RSS overrides must remain bounded and preserve source receipts."""
import copy
from contextlib import redirect_stdout
import io
import json
from pathlib import Path
from types import SimpleNamespace
import tempfile
import unittest
from unittest.mock import patch

import build_state_value as build

GIB = 1024 ** 3


def snapshot(total=48, available=46):
    reserve = max(1536 * 1024 ** 2, int(total * GIB) // 10)
    return {'effective_limit_bytes': int(total * GIB), 'available_bytes': int(available * GIB),
            'reserve_bytes': reserve, 'usable_bytes': max(0, int(available * GIB) - reserve)}


class AuditMemoryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(); self.root = Path(self.temp.name)
        self.tree = self.root / 'tree'; self.tree.mkdir()
        self.state = self.root / 'state'; self.state.mkdir()
        profiles = copy.deepcopy(build.PHASES)
        profiles['assembly'].update(address_space_mib=27*1024, rss_guard_mib=25*1024)
        self.graph = SimpleNamespace(tree=self.tree, flags=[], profiles=profiles)

    def tearDown(self):
        self.temp.cleanup()

    def test_no_override_preserves_exact_default_limits(self):
        original = {'workers': 1, 'address_space_bytes': 27*GIB, 'rss_guard_bytes': 25*GIB}
        self.assertIs(build.audit_limits(self.graph, {}, original), original)

    def test_forty_gib_fits_48_gib_with_both_guards_and_reserve(self):
        before = copy.deepcopy(self.graph.profiles)
        with patch('proof24_resources.memory_snapshot', return_value=snapshot()):
            limits = build.audit_limits(self.graph, {'STATE24_AUDIT_RSS_GIB': '40'})
        self.assertEqual(limits['workers'], 1)
        self.assertEqual(limits['rss_guard_bytes'], 40*GIB)
        self.assertEqual(limits['address_space_bytes'], 42*GIB)
        self.assertEqual(self.graph.profiles, before)

    def test_same_budget_is_rejected_on_32_gib_or_with_low_available_ram(self):
        for snap in (snapshot(32, 31), snapshot(48, 43), snapshot(16, 15)):
            with self.subTest(snapshot=snap), patch('proof24_resources.memory_snapshot', return_value=snap):
                with self.assertRaisesRegex(ValueError, 'Insufficient current RAM'):
                    build.audit_limits(self.graph, {'STATE24_AUDIT_RSS_GIB': '40'})

    def test_only_positive_integer_gib_values_are_accepted(self):
        for value in ('', '0', '-1', '1.5', '40GiB', '01', '+40', ' 40', '40 '):
            with self.subTest(value=value), self.assertRaisesRegex(ValueError, 'positive integer'):
                build.audit_limits(self.graph, {'STATE24_AUDIT_RSS_GIB': value})

    def test_default_sized_explicit_override_still_fits_32_gib(self):
        with patch('proof24_resources.memory_snapshot', return_value=snapshot(32, 31)):
            limits = build.audit_limits(self.graph, {'STATE24_AUDIT_RSS_GIB': '25'})
        self.assertEqual(limits['rss_guard_bytes'], 25*GIB)
        self.assertEqual(limits['address_space_bytes'], 27*GIB)

    def test_source_compile_budget_stays_original_and_full_audit_uses_override(self):
        calls=[]
        runtime={'binaries': {'coqc': {'path': '/unit-only/coqc'}, 'coqchk': {'path': '/unit-only/coqchk'}}}
        env={'STATE24_AUDIT_RSS_GIB': '40', 'STATE24_COQCHK_TRACE': '1'}
        def checker(command, cwd, environment, log, limits, timeout):
            calls.append((command, limits))
            if command[0].endswith('coqc'):
                self.assertEqual(limits['rss_guard_bytes'], 25*GIB)
                Path(log).write_text('Closed under the global context\n')
                (cwd/command[-1]).with_suffix('.vo').write_bytes(b'UNIT ONLY; not a Coq object')
            else:
                self.assertEqual(limits['rss_guard_bytes'], 40*GIB)
                self.assertEqual(limits['address_space_bytes'], 42*GIB)
                self.assertNotIn('-admit', command); self.assertNotIn('-norec', command)
                self.assertNotIn('-silent', command)
                self.assertEqual(environment['OCAMLRUNPARAM'], 'o=40,O=60')
                Path(log).write_text('Unit-only simulated complete recursive audit\n')
            return {'exit_code': 0, 'command': command}
        with patch('proof24_resources.memory_snapshot', return_value=snapshot()), \
             patch.object(build, 'selected_statement_check', return_value='(* Unit-only statement fixture *)\n'), \
             patch.object(build, 'run_capped', side_effect=checker), redirect_stdout(io.StringIO()):
            result=build.checked_root(self.graph,self.state,runtime,env,
                                      'Example.Final.value','Example.Final','CheckFinal',120)
        self.assertEqual(len(calls), 2); self.assertEqual(result['mode'], 'full-recursive')
        policy=json.loads((self.state/'CheckFinal-audit-policy.json').read_text())
        self.assertEqual(policy['requested_rss_gib'], '40')
        self.assertEqual(policy['rss_guard_bytes'], 40*GIB)
        self.assertNotIn('OCAMLRUNPARAM', env)

    def test_impossible_budget_rejects_before_statement_compile_or_audit(self):
        with patch('proof24_resources.memory_snapshot', return_value=snapshot(32, 31)), \
             patch.object(build, 'selected_statement_check', return_value='(* Unit-only fixture *)\n'), \
             patch.object(build, 'run_capped') as run:
            with self.assertRaisesRegex(ValueError, 'Insufficient current RAM'):
                build.checked_root(self.graph,self.state,{}, {'STATE24_AUDIT_RSS_GIB': '40'},
                                   'Example.Final.value','Example.Final','CheckFinal',120)
        run.assert_not_called()
        self.assertFalse((self.state/'CheckFinal-audit-policy.json').exists())

    def test_exact_prior_gc_driver_can_resume_but_changed_runtime_or_unknown_driver_cannot(self):
        previous={'manifest_sha256':'same', 'runtime_sha256':'same', 'tree':'same',
                  'implementation':copy.deepcopy(build.MEMORY_PREDECESSOR)}
        current=copy.deepcopy(previous);current['implementation']['build_state_value.py']='new audit-memory policy'
        (self.state/'build-identity.json').write_text(json.dumps(previous))
        with redirect_stdout(io.StringIO()):build.resume_identity(self.state,current,True)
        self.assertEqual(json.loads((self.state/'build-identity.json').read_text()),current)
        for key in ('manifest_sha256','runtime_sha256','tree'):
            changed=copy.deepcopy(previous);changed[key]='changed'
            (self.state/'build-identity.json').write_text(json.dumps(changed))
            with self.assertRaises(ValueError):build.resume_identity(self.state,current,True)
        unknown=copy.deepcopy(previous);unknown['implementation']['build_state_value.py']='unknown'
        (self.state/'build-identity.json').write_text(json.dumps(unknown))
        with self.assertRaises(ValueError):build.resume_identity(self.state,current,True)


if __name__ == '__main__': unittest.main()
