"""Protect stable IDs and the boundary between research claims and proof credit."""
import copy
import json
import unittest

from check_campaign import ROOT, unpack
from instruction_worklist import FIELDS, LANES, apply_claims, batch_id, identity, load_rows, next_rows
from instruction_worklist_html import render
from instruction_core_targets import targets
from replay_instruction_proofs import accepted, command


class InstructionWorklistTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows, _ = load_rows()

    def test_exact_open_inventory_and_injective_ids(self):
        self.assertEqual(len(self.rows), 28653)
        summary = json.loads((ROOT / 'research/instruction-burndown-summary.json').read_text())
        self.assertEqual(sum(r['proof_status'] == 'open' for r in self.rows), summary['remaining_instruction_families'])
        self.assertEqual(len({r['id'] for r in self.rows}), len(self.rows))
        for row in self.rows:
            self.assertEqual(unpack(int(row['id'][5:]), 17), row['machine'])

    def test_batch_and_id_do_not_move_after_a_proof_is_removed(self):
        before = {r['machine']: (r['id'], r['batch']) for r in self.rows}
        for row in self.rows[1:]:
            self.assertEqual((identity(row['machine']), batch_id(row['machine'])), before[row['machine']])

    def test_claim_cannot_close_a_proof_obligation(self):
        row = copy.deepcopy(next(r for r in self.rows if r['proof_status'] == 'open'))
        claims = dict(schema_version=1, batches={}, machines={row['id']: dict(owner='alice', status='proved')})
        with self.assertRaisesRegex(ValueError, 'proof status'):
            apply_claims([row], claims)
        claims['machines'][row['id']]['status'] = 'proposed'
        apply_claims([row], claims)
        self.assertEqual(row['proof_status'], 'open')
        self.assertEqual(row['work_status'], 'proposed')

    def test_machine_claim_overrides_batch_without_changing_ids(self):
        row = copy.deepcopy(next(r for r in self.rows if r['proof_status'] == 'open'))
        claims = dict(schema_version=1, batches={row['batch']: dict(owner='alice')},
                      machines={row['id']: dict(owner='bob', status='in_progress')})
        apply_claims([row], claims)
        self.assertEqual(row['owner'], 'bob')
        self.assertEqual(row['id'], identity(row['machine']))

    def test_next_batch_is_unclaimed_open_work_and_has_prior_attempts(self):
        selected = next_rows(self.rows)
        self.assertEqual(len(selected), 64)
        self.assertTrue(all(r['proof_status'] == 'open' and r['work_status'] == 'unclaimed' for r in selected))
        retry_count = sum(r['proof_status'] == 'open' and r['lane'] == 'retry_history' for r in self.rows)
        candidate_count = sum(r['proof_status'] == 'open' and r['lane'] == 'replay_candidate' for r in self.rows)
        start = min(64, candidate_count)
        self.assertTrue(all(r['lane'] == 'retry_history' for r in selected[start:start + min(64-start, retry_count)]))

    def test_final_state_case_is_linked_without_instruction_credit(self):
        row = next(r for r in self.rows if r['state_case'] == 'S071')
        self.assertEqual(row['state_package'], 'burn43-s071-far')
        self.assertEqual(row['proof_status'], 'open')

    def test_neighbor_search_keeps_unresolved_attempts_without_proof_credit(self):
        ledger = json.loads((ROOT / 'research/instruction-neighbor-search-ledger.json').read_text())
        machines = {values[0] for values in ledger['rows']}
        touched = [row for row in self.rows if row['machine'] in machines]
        self.assertEqual(len(touched), len(machines))
        self.assertTrue(all('neighbors:' in row['search_history'] for row in touched))
        self.assertTrue(any(row['proof_status'] == 'open' for row in touched))
        self.assertTrue(all(row['proof_theorem'] for row in touched if row['proof_status'] == 'proved'))

    def test_clean_replay_builds_inventory_and_tail_dependencies(self):
        required = {'Bootstrap', 'CertifiedBoard', 'StateOnlyCloseout', 'DualCloseout',
                    'OrbitCloseout', 'BoardManifest', 'OneStateReach', 'TotalCompletion'}
        self.assertTrue({'theories/' + name + '.vo' for name in required} <= set(targets()))

    def test_every_accepted_batch_has_a_reviewed_replay_driver(self):
        names = accepted()
        self.assertEqual(len(names), len(set(names)))
        for name in names:
            selected = command(name)
            self.assertTrue((ROOT / 'tools' / selected[0]).is_file())

    def test_unknown_batch_cannot_select_an_arbitrary_driver(self):
        with self.assertRaisesRegex(ValueError, 'reviewed replay driver'):
            command('../unreviewed.py')

    def test_claim_notes_are_text_in_the_standalone_browser(self):
        row = copy.deepcopy(self.rows[0])
        row['note'] = '</script><script>alert(1)</script>'
        page = render([row], {}, FIELDS, LANES)
        encoded = page.split('<script id="data" type="application/json">', 1)[1].split('</script>', 1)[0]
        self.assertNotIn('<', encoded)
        data = json.loads(encoded)
        self.assertEqual(data['extra'][row['id'][5:]]['note'], row['note'])


if __name__ == '__main__':
    unittest.main()
