#!/usr/bin/env python3
"""Check changed-proof coverage, including renames and failed git selection."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from ci_changed import changed, partition


class ChangedProofTests(unittest.TestCase):
    def test_partition_is_complete_disjoint_and_stable(self):
        targets = ['theories/Family%d/Proof%d.vo' % (i % 9, i) for i in range(3434)]
        parts = partition(targets, 6)
        self.assertEqual(sorted(x for part in parts for x in part), sorted(targets))
        self.assertEqual(parts, partition(list(reversed(targets)), 6))
        self.assertLessEqual(max(map(len, parts)) - min(map(len, parts)), 1)
        self.assertEqual(partition([], 1), [[]])
        with self.assertRaises(ValueError):
            partition(targets, 0)

    def test_real_git_diff_includes_new_renamed_modified_not_deleted(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            def git(*args):
                return subprocess.check_output(['git', '-C', tmp, *args], text=True).strip()
            git('init', '-q')
            git('config', 'user.email', 'test@example.invalid')
            git('config', 'user.name', 'CI test')
            (root / 'theories/CloseoutTr').mkdir(parents=True)
            for name in ['Old.v', 'Modified.v', 'Deleted.v', 'Same.v']:
                (root / 'theories' / name).write_text('(* original *)\n')
            git('add', '.')
            git('commit', '-qm', 'base')
            base = git('rev-parse', 'HEAD')
            (root / 'theories/Old.v').rename(root / 'theories/Renamed.v')
            (root / 'theories/Deleted.v').unlink()
            for name in ['Modified.v', 'New.v', 'CloseoutTr/CloseoutTr.v', 'CloseoutTr/RemainingTr.v']:
                (root / 'theories' / name).write_text('(* changed *)\n')
            git('add', '-A')
            git('commit', '-qm', 'changes')
            previous = os.getcwd()
            try:
                os.chdir(root)
                self.assertEqual(changed(base), ['theories/Modified.vo', 'theories/New.vo', 'theories/Renamed.vo'])
                with self.assertRaises(subprocess.CalledProcessError):
                    changed('nonexistent-base')
            finally:
                os.chdir(previous)


if __name__ == '__main__':
    unittest.main()
