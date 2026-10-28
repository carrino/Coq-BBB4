"""Small regression tests for the audit cache's fail-closed boundaries."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

from kernel_audit_cache import _covered, _load_receipt, audit, digest, fresh_paths


class CacheTests(unittest.TestCase):
    def setUp(self):
        self.snapshot=dict(runtime={'compiler':'fixed'},plugins={},graph={
            'A':dict(source_sha256='a',object_sha256='A',dependencies=[]),
            'B':dict(source_sha256='b',object_sha256='B',dependencies=['A'])})
        self.receipt=dict(snapshot=self.snapshot)

    def test_dependency_change_invalidates_dependents(self):
        current=copy.deepcopy(self.snapshot)
        self.assertEqual(_covered(current,[self.receipt]),{'A','B'})
        current['graph']['A']['object_sha256']='changed'
        self.assertEqual(_covered(current,[self.receipt]),set())

    def test_runtime_change_disables_reuse(self):
        current=copy.deepcopy(self.snapshot);current['runtime']['compiler']='changed'
        self.assertEqual(_covered(current,[self.receipt]),set())

    def test_new_root_is_not_implicitly_covered(self):
        current=copy.deepcopy(self.snapshot)
        current['graph']['C']=dict(source_sha256='c',object_sha256='C',dependencies=['B'])
        self.assertEqual(_covered(current,[self.receipt]),{'A','B'})

    def test_existing_artifacts_cannot_be_overwritten(self):
        with tempfile.TemporaryDirectory() as temp:
            receipt,log=fresh_paths(temp);receipt.write_text('preserved')
            with self.assertRaisesRegex(ValueError,'immutable'):
                audit([],[],[],receipt,log)
            self.assertNotEqual(fresh_paths(temp)[0],receipt)
            self.assertEqual(receipt.read_text(),'preserved')

    def test_incomplete_log_is_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            path=Path(temp)/'audit.json';log=path.with_suffix('.log')
            log.write_text('Checking library: A\nChecking library: B\n')
            data=dict(schema=1,result='passed',kind='recursive',parents=[],snapshot=self.snapshot,
                      checked_modules=['A','B'],reused_modules=[],command=['coqchk','B'],log=str(log),log_sha256=digest(log))
            path.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError,'completion'):_load_receipt(path)
            log.write_text(log.read_text()+'Modules were successfully checked\n')
            data['log_sha256']=digest(log);path.write_text(json.dumps(data))
            self.assertEqual(_load_receipt(path)['kind'],'recursive')
            log.write_text('tampered')
            with self.assertRaisesRegex(ValueError,'log changed'):_load_receipt(path)


if __name__=='__main__':unittest.main()
