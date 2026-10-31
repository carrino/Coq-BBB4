"""Actual tiny Python-process negatives; no Coq/native/compiler execution."""
from concurrent.futures import ThreadPoolExecutor
import os
from pathlib import Path
import sys
import tempfile
import time
import unittest

from proof24_common import clean_environment
from proof24_resources import CommandBatch, MIB, run_capped


@unittest.skipUnless(sys.platform.startswith('linux') and Path('/proc').is_dir(), 'Linux/WSL subreaper fixtures')
class OwnedLifecycle(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='python-process-fixture-')
        self.root = Path(self.temp.name)
        self.limits = {'address_space_bytes': 512 * MIB, 'rss_guard_bytes': 256 * MIB}

    def tearDown(self):
        self.temp.cleanup()

    def run_python(self, name, script, batch=None, timeout=5):
        return run_capped([sys.executable, '-c', script], self.root, clean_environment(),
                          self.root / (name + '.log'), self.limits, timeout, batch)

    def assert_pid_gone(self, name):
        path = self.root / name
        self.assertTrue(path.is_file(), name)
        pid = int(path.read_text())
        self.assertFalse(Path('/proc', str(pid)).exists(), 'Owned fixture process remains: ' + str(pid))

    def test_normal_command_has_complete_lifetime(self):
        result = self.run_python('normal', 'print("tiny Python fixture only")')
        self.assertEqual(result['exit_code'], 0)
        self.assertIn('tiny Python fixture only', (self.root / 'normal.log').read_text())

    def test_leader_exit_with_live_descendant_fails_and_reaps(self):
        script = '''import os,time
from pathlib import Path
pid=os.fork()
if pid == 0:
 Path('descendant.pid').write_text(str(os.getpid()))
 time.sleep(30)
else:
 while not Path('descendant.pid').exists(): time.sleep(0.01)
 os._exit(0)
'''
        with self.assertRaises(RuntimeError):
            self.run_python('orphan', script)
        self.assert_pid_gone('descendant.pid')
        self.assertIn('descendant', (self.root / 'orphan.log').read_text())

    def test_escaped_session_fails_and_reaps(self):
        script = '''import os,time
from pathlib import Path
pid=os.fork()
if pid == 0:
 Path('escaped.pid').write_text(str(os.getpid()))
 os.setsid()
 time.sleep(30)
else:
 time.sleep(30)
'''
        with self.assertRaises(RuntimeError):
            self.run_python('escaped', script)
        self.assert_pid_gone('escaped.pid')

    def test_one_failure_cancels_all_owned_concurrent_groups(self):
        owner = CommandBatch()
        long_script = '''import os,time
from pathlib import Path
Path('parallel.pid').write_text(str(os.getpid()))
time.sleep(30)
'''
        bad_script = '''import os,time
from pathlib import Path
while not Path('parallel.pid').exists(): time.sleep(0.01)
os._exit(7)
'''
        started = time.monotonic()
        with ThreadPoolExecutor(max_workers=2) as pool:
            futures = [pool.submit(self.run_python, 'parallel', long_script, owner),
                       pool.submit(self.run_python, 'failure', bad_script, owner)]
            for future in futures:
                with self.assertRaises(RuntimeError):
                    future.result()
        self.assertLess(time.monotonic() - started, 5)
        self.assertTrue(owner.cancelled.is_set())
        self.assertEqual(owner.processes, {})
        self.assert_pid_gone('parallel.pid')

    def test_timeout_kills_and_reaps_the_owned_command(self):
        script = '''import os,time
from pathlib import Path
Path('timed.pid').write_text(str(os.getpid()))
time.sleep(30)
'''
        with self.assertRaises(RuntimeError):
            self.run_python('timeout', script, timeout=0.3)
        self.assert_pid_gone('timed.pid')


if __name__ == '__main__':
    unittest.main()
