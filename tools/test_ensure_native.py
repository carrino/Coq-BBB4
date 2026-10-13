#!/usr/bin/env python3
"""Check which existing .vo ensure_native.py hands to coqnative, and in what order."""
import os
from pathlib import Path
import sys
import tempfile
import time
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import ensure_native as en  # noqa: E402

DEPS = '''theories/A.vo theories/A.glob theories/A.v.beautified theories/A.required_vo: theories/A.v
theories/Sub/B.vo theories/Sub/B.glob theories/Sub/B.v.beautified theories/Sub/B.required_vo: theories/Sub/B.v theories/A.vo
theories/C.vo theories/C.glob theories/C.v.beautified theories/C.required_vo: theories/C.v theories/Sub/B.vo theories/A.vo
theories/C.vio: theories/C.v theories/Sub/B.vio
'''


class EnsureNativeTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.cwd = os.getcwd()
        os.chdir(self.tmp.name)
        Path('.Makefile.coq.d').write_text(DEPS)
        self.deps = en.read_deps()

    def tearDown(self):
        os.chdir(self.cwd)
        self.tmp.cleanup()

    def touch(self, path, t):
        p = Path(path)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text('')
        os.utime(p, (t, t))

    def test_native_file_names_follow_the_logical_path(self):
        self.assertEqual(en.cmxs_of('theories/A.vo'),
                         'theories/.coq-native/NBBB4_A.cmxs')
        self.assertEqual(en.cmxs_of('theories/Sub/B.vo'),
                         'theories/Sub/.coq-native/NBBB4_Sub_B.cmxs')

    def test_dependencies_come_first(self):
        self.assertEqual(self.deps['theories/C.vo'], ['theories/Sub/B.vo', 'theories/A.vo'])
        self.assertEqual(en.closure(['theories/C.vo'], self.deps),
                         ['theories/A.vo', 'theories/Sub/B.vo', 'theories/C.vo'])

    def test_stale_or_missing_objects_are_left_to_make(self):
        now = time.time()
        for f in ['theories/A.v', 'theories/Sub/B.v', 'theories/C.v']:
            self.touch(f, now - 100)
        self.touch('theories/A.vo', now - 50)
        self.touch('theories/Sub/B.vo', now - 60)   # older than its dependency A.vo
        self.assertTrue(en.up_to_date('theories/A.vo', self.deps))
        self.assertFalse(en.up_to_date('theories/Sub/B.vo', self.deps))
        self.assertFalse(en.up_to_date('theories/C.vo', self.deps))
        self.touch('theories/A.v', now)              # source edited after the build
        self.assertFalse(en.up_to_date('theories/A.vo', self.deps))


if __name__ == '__main__':
    unittest.main()
