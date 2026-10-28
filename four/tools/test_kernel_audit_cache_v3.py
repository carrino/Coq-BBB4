"""Small regression tests for the audit cache's fail-closed boundaries."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

from kernel_audit_cache_v3 import ReceiptValidation, _covered, _load_receipt, audit, digest, fresh_paths


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


class ReceiptMemoTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.directory=Path(self.temp.name)
        self.base=self.directory/'base.json';self.log=self.directory/'base.log'
        self.log.write_text('Checking library: A\nModules were successfully checked\n')
        self.data=dict(schema=1,result='passed',kind='recursive',parents=[],
                       snapshot=dict(runtime={},plugins={},graph={'A':dict(dependencies=[])}),
                       checked_modules=['A'],reused_modules=[],command=['coqchk','A'],
                       log=str(self.log),log_sha256=digest(self.log))
        self.base.write_text(json.dumps(self.data))
        self.child=self.child_receipt('child')

    def child_receipt(self,name):
        path=self.directory/(name+'.json');log=path.with_suffix('.log')
        log.write_text('All requested artifacts match previously successful audits.\n')
        data={**self.data,'kind':'incremental',
              'parents':[dict(path=str(self.base),sha256=digest(self.base))],
              'checked_modules':[],'reused_modules':['A'],'command':['coqchk'],
              'log':str(log),'log_sha256':digest(log)}
        path.write_text(json.dumps(data));return path

    def test_shared_ancestor_is_validated_once(self):
        other=self.child_receipt('other');validation=ReceiptValidation()
        validation.load(self.child);ancestor=validation.memo[self.base]
        validation.load(other)
        self.assertIs(validation.memo[self.base],ancestor)
        self.assertEqual(len(validation.memo),3)
        self.assertEqual(len(validation.artifacts),6)
        validation.recheck()

    def test_every_visited_receipt_and_log_is_rechecked(self):
        for target in (self.base,self.log,self.child,self.child.with_suffix('.log')):
            with self.subTest(target=target.name):
                validation=ReceiptValidation();validation.load(self.child)
                original=target.read_bytes();target.write_bytes(original+b' ')
                with self.assertRaisesRegex(ValueError,'changed'):validation.recheck()
                target.write_bytes(original)

    def test_release_keeps_all_mutation_guards(self):
        validation=ReceiptValidation();validation.load(self.child)
        artifacts=validation.artifacts.copy();validation.release()
        self.assertEqual(validation.memo,{})
        self.assertEqual(validation.artifacts,artifacts)
        self.log.write_text('changed')
        with self.assertRaisesRegex(ValueError,'changed'):validation.recheck()

    def test_parent_hash_checked_even_after_memo_hit(self):
        validation=ReceiptValidation();validation.load(self.base)
        data=json.loads(self.child.read_text());data['parents'][0]['sha256']='0'*64
        self.child.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError,'Parent receipt changed'):validation.load(self.child)

    def test_cycles_rejected(self):
        data=json.loads(self.child.read_text());data['parents'][0]['path']=str(self.child)
        self.child.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError,'Cyclic'):ReceiptValidation().load(self.child)

    def test_fabricated_checked_list_rejected(self):
        data=json.loads(self.base.read_text());data['checked_modules']=[]
        self.base.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError,'checked-module list'):_load_receipt(self.base)

    def test_memo_does_not_survive_a_new_validation(self):
        ReceiptValidation().load(self.child)
        self.log.write_text('changed')
        with self.assertRaisesRegex(ValueError,'log changed'):ReceiptValidation().load(self.child)


if __name__=='__main__':unittest.main()
