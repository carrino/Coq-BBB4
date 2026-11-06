import json
from pathlib import Path
import resource
import subprocess
import sys
import unittest
from unittest import mock

import with_coq_stack as wrapper


class StackLimitTests(unittest.TestCase):
    def assert_limit(self, original, expected):
        with mock.patch.object(wrapper.resource, 'getrlimit', return_value=original), \
             mock.patch.object(wrapper.resource, 'setrlimit') as change:
            wrapper.raise_stack_limit()
            if expected is None:
                change.assert_not_called()
            else:
                change.assert_called_once_with(resource.RLIMIT_STACK, expected)

    def test_raise_soft_without_changing_unlimited_hard(self):
        self.assert_limit((8 << 20, resource.RLIM_INFINITY),
                          (64 << 20, resource.RLIM_INFINITY))

    def test_clamp_to_finite_hard_limit(self):
        self.assert_limit((4 << 20, 16 << 20), (16 << 20, 16 << 20))

    def test_preserve_higher_and_unlimited_soft_limits(self):
        self.assert_limit((128 << 20, 256 << 20), None)
        self.assert_limit((resource.RLIM_INFINITY, resource.RLIM_INFINITY), None)

    def test_preserve_limit_already_at_hard_ceiling(self):
        self.assert_limit((8 << 20, 8 << 20), None)

    def test_error_prevents_exec(self):
        with mock.patch.object(wrapper, 'raise_stack_limit', side_effect=ValueError('denied')), \
             mock.patch.object(wrapper.os, 'execvp') as execute, \
             mock.patch('sys.stderr'):
            self.assertEqual(wrapper.main(['coqc', 'input.v']), 1)
            execute.assert_not_called()

    def test_missing_command_is_usage_error(self):
        with mock.patch('sys.stderr'):
            self.assertEqual(wrapper.main([]), 2)

    def test_exec_preserves_arguments_and_exit_status(self):
        script = str(Path(wrapper.__file__).resolve())
        args = ['argument with spaces', 'literal $HOME', 'semi;colon']
        code = 'import json,resource,sys; print(json.dumps([resource.getrlimit(resource.RLIMIT_STACK),sys.argv[1:]]));sys.exit(7)'
        result = subprocess.run([sys.executable, script, '--', sys.executable, '-c', code, *args],
                                text=True, capture_output=True, check=False)
        self.assertEqual(result.returncode, 7, result.stderr)
        (soft, hard), actual_args = json.loads(result.stdout)
        original_soft, original_hard = resource.getrlimit(resource.RLIMIT_STACK)
        expected = original_soft
        if original_soft != resource.RLIM_INFINITY and original_soft < wrapper.STACK_BYTES:
            expected = wrapper.STACK_BYTES if original_hard == resource.RLIM_INFINITY else min(wrapper.STACK_BYTES, original_hard)
        self.assertEqual((soft, hard), (expected, original_hard))
        self.assertEqual(actual_args, args)

    def test_real_child_hard_limit_is_clamped_and_unchanged(self):
        script = str(Path(wrapper.__file__).resolve())
        _, hard = resource.getrlimit(resource.RLIMIT_STACK)
        ceiling = 16 << 20 if hard == resource.RLIM_INFINITY else min(16 << 20, hard)
        if ceiling <= 0:
            self.skipTest('no positive child stack limit available')
        initial = min(4 << 20, ceiling)
        launcher = ('import os,resource,sys; '
                    f'resource.setrlimit(resource.RLIMIT_STACK,({initial},{ceiling})); '
                    'os.execv(sys.executable,[sys.executable,*sys.argv[1:]])')
        child = 'import json,resource;print(json.dumps(resource.getrlimit(resource.RLIMIT_STACK)))'
        result = subprocess.run([sys.executable, '-c', launcher, script, sys.executable, '-c', child],
                                text=True, capture_output=True, check=True)
        self.assertEqual(json.loads(result.stdout), [ceiling, ceiling])


if __name__ == '__main__':
    unittest.main()
