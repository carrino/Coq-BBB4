#!/usr/bin/env python3
"""Tests of the untrusted replay boundary (no Coq installation needed)."""
import csv
from pathlib import Path
import tempfile
import unittest

import replay_rank_samples as replay


class ReplayTests(unittest.TestCase):
    def row(self, i, n=2, t=100, full=0):
        return dict(index=str(i), kind='tail_ngram_candidate',
                    machine='0RA0RA_0RB0RB_0RC0RC_0RD' + ('0RD' if full else '---'),
                    full=str(full), ngram_n=str(n), ngram_t=str(t), contexts='7',
                    candidate_wait_upper='8')

    def select(self, rows):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / 'ledger.tsv'
            with p.open('w') as stream:
                w = csv.DictWriter(stream, rows[0].keys(), delimiter='\t')
                w.writeheader()
                w.writerows(rows)
            return replay.select_samples(p, 2)

    def test_order_independent_bounded_stratification(self):
        rows = [self.row(i, full=i % 2) for i in range(100)]
        first, counts = self.select(rows)
        second, _ = self.select(list(reversed(rows)))
        self.assertEqual(first, second)
        self.assertEqual(len(first), 4)
        self.assertEqual(counts, {'2:100:0': 50, '2:100:1': 50})

    def test_ignore_non_candidates_and_other_rungs(self):
        unrelated = self.row(2)
        unrelated['kind'] = 'halt_completion'
        rows = [self.row(1), unrelated, self.row(3, n=5)]
        selected, counts = self.select(rows)
        self.assertEqual([r['index'] for r in selected], ['1'])
        self.assertEqual(counts, {'2:100:0': 1})

    def test_validate_partial_flag(self):
        row = self.row(1)
        row['full'] = '1'
        with self.assertRaises(ValueError):
            self.select([row])

    def test_rejected_has_no_window_theorem(self):
        src = replay.proof_source(self.row(1), 44, 10, False)
        self.assertIn('tN]', src)
        self.assertIn('verdict = false', src)
        self.assertNotIn('Theorem replay_window', src)
        self.assertNotIn('Eval vm_compute', src)

    def test_accepted_keeps_checked_gate_and_anchor(self):
        src = replay.proof_source(self.row(1), 44, 10, True)
        self.assertIn('verdict = true', src)
        self.assertIn('forall B, 100 <= B -> WindowBound machine B 8', src)
        self.assertIn('ngram_ranked_search_sound machine 2 100 44 10 8 B', src)
        self.assertIn('ngram_ranked_search_completion machine 2 100 44 10 8', src)
        self.assertIn("TM_le machine tm' -> NonHalt tm'", src)
        self.assertNotIn('Admitted', src)

    def test_duplicate_indices_fail_closed(self):
        row = self.row(1)
        with self.assertRaises(ValueError):
            self.select([row, dict(row, contexts='8')])

    def test_rejects_malformed_or_unbounded_parameters(self):
        for key, value in [('contexts', '100000'), ('ngram_t', '-1'), ('candidate_wait_upper', '1. Axiom injected : False.')]:
            row = self.row(1); row[key] = value
            with self.assertRaises(ValueError):
                replay.source(row, 44, 10)


if __name__ == '__main__':
    unittest.main()
