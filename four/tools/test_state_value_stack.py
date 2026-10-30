"""Process-stack policy and actual exec inheritance for selected Coq builds."""
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import with_coq_stack as stack

MIB=1024**2
WRAPPER=Path(stack.__file__).resolve()


class StackTests(unittest.TestCase):
    def test_small_soft_limit_is_raised_without_changing_hard_limit(self):
        with patch.object(resource,'getrlimit',return_value=(8*MIB,resource.RLIM_INFINITY)), \
             patch.object(resource,'setrlimit') as setter:
            stack.ensure_stack()
        setter.assert_called_once_with(resource.RLIMIT_STACK,(64*MIB,resource.RLIM_INFINITY))

    def test_large_and_unlimited_soft_limits_are_preserved(self):
        for soft in (64*MIB,128*MIB,resource.RLIM_INFINITY):
            with self.subTest(soft=soft), \
                 patch.object(resource,'getrlimit',return_value=(soft,resource.RLIM_INFINITY)), \
                 patch.object(resource,'setrlimit') as setter:
                stack.ensure_stack();setter.assert_not_called()

    def test_insufficient_hard_limit_is_rejected_without_changes(self):
        with patch.object(resource,'getrlimit',return_value=(8*MIB,32*MIB)), \
             patch.object(resource,'setrlimit') as setter:
            with self.assertRaisesRegex(ValueError,'hard limit of at least 64 MiB'):
                stack.ensure_stack()
        setter.assert_not_called()

    def test_exec_preserves_the_argument_vector(self):
        args=['coqc','-q','path with spaces.v','literal$(argument)']
        with patch.object(sys,'argv',[str(WRAPPER),*args]), \
             patch.object(stack,'ensure_stack') as ensure, \
             patch.object(os,'execvp') as execute:
            stack.main()
        ensure.assert_called_once_with();execute.assert_called_once_with('coqc',args)

    def test_missing_command_is_rejected_before_exec(self):
        with patch.object(sys,'argv',[str(WRAPPER)]),patch.object(os,'execvp') as execute:
            with self.assertRaisesRegex(ValueError,'Usage:'):stack.main()
        execute.assert_not_called()

    def test_real_child_inherits_stack_environment_cwd_and_literal_arguments(self):
        with tempfile.TemporaryDirectory() as folder:
            env=os.environ.copy();env['BBB24_STACK_TEST']='unchanged environment'
            output='''import json,os,resource,sys
print(json.dumps(dict(stack=resource.getrlimit(resource.RLIMIT_STACK),cwd=os.getcwd(),
 marker=os.environ['BBB24_STACK_TEST'],args=sys.argv[1:])))
'''
            bootstrap='''import os,resource,sys
soft,hard=resource.getrlimit(resource.RLIMIT_STACK)
resource.setrlimit(resource.RLIMIT_STACK,(8*1024**2,hard))
os.execv(sys.executable,[sys.executable,*sys.argv[1:]])
'''
            result=subprocess.run([sys.executable,'-c',bootstrap,str(WRAPPER),sys.executable,
                '-c',output,'with spaces','literal$(argument)'],cwd=folder,env=env,
                capture_output=True,text=True,timeout=15,check=True)
            data=json.loads(result.stdout)
            self.assertEqual(data['stack'][0],64*MIB)
            self.assertEqual(data['stack'][1],resource.getrlimit(resource.RLIMIT_STACK)[1])
            self.assertEqual(data['cwd'],folder)
            self.assertEqual(data['marker'],'unchanged environment')
            self.assertEqual(data['args'],['with spaces','literal$(argument)'])

    def test_real_child_with_low_hard_limit_stops_before_command(self):
        bootstrap='''import os,resource,sys
resource.setrlimit(resource.RLIMIT_STACK,(8*1024**2,32*1024**2))
os.execv(sys.executable,[sys.executable,*sys.argv[1:]])
'''
        result=subprocess.run([sys.executable,'-c',bootstrap,str(WRAPPER),sys.executable,
            '-c','print("COMMAND MUST NOT RUN")'],capture_output=True,text=True,timeout=15)
        self.assertEqual(result.returncode,2)
        self.assertIn('hard limit of at least 64 MiB',result.stderr)
        self.assertNotIn('COMMAND MUST NOT RUN',result.stdout)


if __name__=='__main__':unittest.main()
