#!/usr/bin/env python3
"""Tiny synthetic Python fixtures only; never run Coq or claim corpus coverage."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

import gen_tr_hints as g


class GeneratorTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='tr-hints-synthetic-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.put('_CoqProject', b'-Q theories BBB4\ntheories/Keep.v\n' + g.PROJECT_ANCHOR.encode() + b'\ntheories/End.v\n')
        checked = {}
        for name in g.INTERFACES:
            self.put(name, (name + '\n').encode())
            checked[name] = g.sha((self.root/name).read_bytes())
        payload = {'source_sha256': {'/inert/nonexistent/source.v': 'a'*64},
            'compiled_sha256': {'/inert/nonexistent/source.vo': 'b'*64},
            'toolchain': {}, 'tag_schema': g.tag_schema(),
            'policy': {'units': 96, 'frontier_levels': 3, 'pop_exponent': 13, 'rounds': 4096},
            'parameters_coq_source': 'synthetic fixture, not executed'}
        self.manifest = {'format': 'tr-hint-source-v1', 'schema_version': 1,
            'units': 96, 'frontier_count': 1792, 'chunk_size': 2,
            'safety_limits': {'input_bytes': 32768, 'input_rows': 16, 'chunks': 8,
                'rationale': 'Tiny synthetic test only'},
            'source_digest': g.sha(g.canonical(payload)), 'trace_payload': payload,
            'trace_provenance': {'synthetic': True}, 'checked_interfaces': checked, 'unit_files': []}
        self.records = {}
        self.add_unit(10, [[1,0],[2,37],[17**8,12]])
        self.save_manifest()

    def put(self, name, data):
        path = self.root/name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)

    def save_manifest(self):
        self.put(g.MANIFEST, g.encoded(self.manifest))

    def add_unit(self, unit, rows):
        record = {'format': 'tr-hint-unit-v1', 'source_digest': self.manifest['source_digest'],
            'unit': unit, 'complete': True, 'frontier_indices': list(range(unit,1792,96)),
            'row_count': len(rows), 'rows': rows}
        self.records[unit] = record
        self.save_unit(unit)

    def save_unit(self, unit):
        path = f'{g.INPUT_DIR}/unit{unit:02d}.rows.json'
        data = g.encoded(self.records[unit]); self.put(path,data)
        self.manifest['unit_files'] = [item for item in self.manifest['unit_files'] if item['unit'] != unit]
        self.manifest['unit_files'].append({'unit': unit, 'path': path, 'sha256': g.sha(data)})
        self.manifest['unit_files'].sort(key=lambda item:item['unit']); self.save_manifest()

    def snapshot(self):
        return {str(p.relative_to(self.root)): (p.read_bytes(),p.stat().st_mtime_ns)
                for p in self.root.rglob('*') if p.is_file()}

    def rejects(self, message):
        before = self.snapshot()
        with self.assertRaisesRegex(ValueError, message):
            g.generate(self.root)
        self.assertEqual(before,self.snapshot(), 'rejection must not partially mutate output')

    def test_replay_check_and_partial_coverage(self):
        result = g.generate(self.root)
        self.assertEqual(result['row_count'],3); self.assertEqual(result['chunk_count'],2)
        before=self.snapshot(); self.assertEqual(g.generate(self.root)['changed_files'],0)
        self.assertEqual(g.generate(self.root,True)['changed_files'],0); self.assertEqual(before,self.snapshot())
        meta=json.loads((self.root/g.OUTPUT_MANIFEST).read_bytes())
        self.assertEqual(meta['coverage']['included_units'],[10])
        self.assertFalse(meta['coverage']['all_unit_records_present'])
        self.assertEqual(len(meta['coverage']['omitted_units']),95)
        self.assertEqual(meta['coq_source_bytes'],sum((self.root/name).stat().st_size for name in meta['files_sha256']))

    def test_empty_api(self):
        (self.root/self.manifest['unit_files'][0]['path']).unlink()
        self.manifest['unit_files']=[]; self.save_manifest(); result=g.generate(self.root)
        self.assertEqual(result['chunk_count'],0)
        self.assertIn('Definition hint_rows_tr : list TrHintRow := [].',(self.root/g.WRAPPER).read_text())

    def test_check_is_readonly_on_missing_output(self):
        before=self.snapshot()
        with self.assertRaisesRegex(ValueError,'stale'):
            g.generate(self.root,True)
        self.assertEqual(before,self.snapshot())

    def test_same_winner_dedup(self):
        self.add_unit(47,[[1,0],[3,4]])
        result=g.generate(self.root)
        self.assertEqual((result['input_row_count'],result['row_count']),(5,4))

    def test_conflicting_winners(self):
        self.add_unit(47,[[1,1]]); self.rejects('conflicting')

    def test_exact_frontier_coverage(self):
        self.records[10]['frontier_indices'].pop(); self.save_unit(10); self.rejects('frontier coverage')

    def test_invalid_rows(self):
        for rows in [[[True,1]], [[0,1]], [[17**8+1,1]], [[1,38]], [[1,False]],
                     [[1,'0']], [[1,1.0]], [[2,1],[1,1]], [[1,1],[1,1]]]:
            with self.subTest(rows=rows):
                self.records[10]['rows']=rows; self.records[10]['row_count']=len(rows)
                self.save_unit(10); self.rejects('invalid|sorted')

    def test_incomplete_record(self):
        self.records[10]['complete']=False; self.save_unit(10); self.rejects('incomplete unit')

    def test_count_mismatch(self):
        self.records[10]['row_count']=2; self.save_unit(10); self.rejects('row_count')

    def test_mixed_digest(self):
        self.records[10]['source_digest']='f'*64; self.save_unit(10); self.rejects('mixed')

    def test_digest_payload_tampering(self):
        self.manifest['trace_payload']['parameters_coq_source']+=' changed'
        self.save_manifest(); self.rejects('digest mismatch')

    def test_input_and_interface_hashes(self):
        name=self.manifest['unit_files'][0]['path']; original=(self.root/name).read_bytes()
        self.put(name,original+b'\n'); self.rejects('input hash mismatch'); self.put(name,original)
        self.put(g.INTERFACES[0],b'changed'); self.rejects('interface changed')

    def test_missing_and_undeclared_inputs(self):
        self.put(g.INPUT_DIR+'/extra.rows.json',b'{}'); self.rejects('inventory differs')
        (self.root/g.INPUT_DIR/'extra.rows.json').unlink()
        (self.root/self.manifest['unit_files'][0]['path']).unlink(); self.rejects('inventory differs')

    def test_duplicate_json_fields(self):
        raw=(self.root/g.MANIFEST).read_bytes().replace(b'"chunk_size": 2,',b'"chunk_size": 2, "chunk_size": 2,')
        self.put(g.MANIFEST,raw); self.rejects('duplicate JSON')

    def test_duplicate_units(self):
        self.manifest['unit_files'].append(copy.deepcopy(self.manifest['unit_files'][0]))
        self.save_manifest(); self.rejects('sorted and unique')

    def test_paths_and_symlinks(self):
        item=self.manifest['unit_files'][0]; original=item['path']; item['path']='../escape'
        self.save_manifest(); self.rejects('noncanonical')
        item['path']=original; self.save_manifest()
        path=self.root/original; actual=self.root/'fixture.json'; path.rename(actual); path.symlink_to(actual)
        self.rejects('symlink')

    def test_output_symlink(self):
        outside=self.root/'external.v'; outside.write_text('unchanged')
        wrapper=self.root/g.WRAPPER; wrapper.symlink_to(outside); self.rejects('symlink')

    def test_explicit_budget_growth(self):
        self.manifest['safety_limits']['input_rows']=2; self.save_manifest(); self.rejects('safety limit')
        self.manifest['safety_limits']['input_rows']=3; self.manifest['safety_limits']['chunks']=1
        self.save_manifest(); self.rejects('chunks exceed')
        self.manifest['safety_limits']['chunks']=2; self.manifest['safety_limits']['input_bytes']=1
        self.save_manifest(); self.rejects('byte budget')
        self.manifest['safety_limits']['input_bytes']=32768; self.save_manifest()
        self.assertEqual(g.generate(self.root)['row_count'],3)

    def test_chunk_size_range_and_1024(self):
        for invalid in [0,1025,True,'256']:
            self.manifest['chunk_size']=invalid; self.save_manifest(); self.rejects('chunk_size')
        self.manifest['chunk_size']=1024; self.save_manifest()
        self.assertEqual(g.generate(self.root)['chunk_count'],1)

    def test_stale_generated_source(self):
        self.put(g.PART_DIR+'/HintsTr_Data_P9999.v',g.HEADER.encode()); self.rejects('stale generated')

    def test_project_preserves_others_and_has_no_oscillation(self):
        before=(self.root/'_CoqProject').read_text().splitlines()
        g.generate(self.root); after=(self.root/'_CoqProject').read_text().splitlines()
        self.assertEqual([line for line in after if line in before],before)
        self.assertEqual(len(after),len(set(after)))
        self.assertLess(after.index(g.INTERFACES[5]),after.index(g.PROJECT_ANCHOR))
        with (self.root/'_CoqProject').open('a') as out:
            out.write('theories/CloseoutTr/Unrelated.v\n')
        # Unrelated project changes don't invalidate generated-data metadata.
        self.assertEqual(g.generate(self.root,True)['changed_files'],0)

    def test_missing_project_anchor(self):
        self.put('_CoqProject',b'-Q theories BBB4\n'); self.rejects('anchor')

    def test_unsupported_schema_and_policy(self):
        self.manifest['trace_payload']['tag_schema'][0]['code']=False
        self.manifest['source_digest']=g.sha(g.canonical(self.manifest['trace_payload']))
        self.save_manifest(); self.rejects('winner tag schema')
        self.manifest['trace_payload']['tag_schema']=g.tag_schema()
        self.manifest['trace_payload']['policy']['rounds']=2048
        self.manifest['source_digest']=g.sha(g.canonical(self.manifest['trace_payload']))
        self.save_manifest(); self.rejects('exploration policy')

    def test_nonstandard_json_number(self):
        with self.assertRaisesRegex(ValueError, 'nonstandard JSON'):
            g.parse(b'{"bad": NaN}')

    def test_arbitrary_single_consistent_trace_digest(self):
        self.manifest['trace_payload']['parameters_coq_source']='new immutable fallback closure'
        self.manifest['source_digest']=g.sha(g.canonical(self.manifest['trace_payload']))
        self.records[10]['source_digest']=self.manifest['source_digest']; self.save_unit(10)
        self.assertEqual(g.generate(self.root)['row_count'],3)


if __name__ == '__main__':
    unittest.main()
