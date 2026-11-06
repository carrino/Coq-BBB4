import csv
import hashlib
from pathlib import Path
import tempfile
import unittest

from replay_periodic import checked_source, machine_term, parse_results, probe_source, sample, verify_selection


class ReplayPeriodicTests(unittest.TestCase):
    def test_machine_encoding_preserves_slots_and_holes(self):
        term = machine_term("1RB---_0LA1RA_------_------")
        self.assertIn("StA, S0 => Some (mkTrans S1 DR StB)", term)
        self.assertIn("StA, S1 => None", term)
        self.assertIn("StB, S0 => Some (mkTrans S0 DL StA)", term)
        self.assertEqual(term.count("=> None"), 5)

    def test_rejects_out_of_domain_tables(self):
        for text in ("1RZ---_------_------_------", "2RA---_------_------_------", "1RA---"):
            with self.assertRaises(ValueError):
                machine_term(text)

    def test_incomplete_probe_discharges_nothing(self):
        for text in ("= [true; false] : list bool", "= [true; ...] : list bool", "Error: timeout"):
            with self.assertRaises(ValueError):
                parse_results(text, 3)
        self.assertEqual(parse_results("= [true;\n false] : list bool", 2), [True, False])

    def test_rejected_entries_stay_out_of_proof_batch(self):
        source = checked_source([False, True, False], 32779478, 4096)
        self.assertIn(":= [entry_1]", source)
        self.assertNotIn("entry_0", source)
        self.assertIn("periodic_batch_completion", source)
        self.assertIn("vm_compute. reflexivity.", source)

    def test_selection_is_bounded_deterministic_and_keeps_strata(self):
        fields = ["index", "kind", "machine", "ptr", "anchor", "period", "excursion_width", "full", "side"]
        rows = [dict(zip(fields, [str(i), "cycle_hash_candidate", "0RA---_------_------_------", "1", "0", "1", "0", "0", "left" if i % 2 else "right"])) for i in range(30)]
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "ledger.tsv"
            def write(items):
                with p.open("w", newline="") as f:
                    w = csv.DictWriter(f, fields, delimiter="\t")
                    w.writeheader()
                    w.writerows(items)
            write(rows)
            first, counts = sample(p, 3)
            write(list(reversed(rows)))
            second, _ = sample(p, 3)
        self.assertEqual(first, second)
        self.assertEqual(len(first), 6)
        self.assertEqual(sum(counts.values()), 30)
        self.assertEqual({r["side"] for r in first}, {"left", "right"})

    def test_metadata_cannot_misattribute_proofs_or_inject_source(self):
        row = dict(index="1", kind="cycle_hash_candidate", machine="0RA---_------_------_------", ptr="1", anchor="0", period="1", excursion_width="0", full="0", side="right")
        source = probe_source([row], 10, 1)
        selection = dict(schema_version=1, selected=[row], cutoff=10, width=1, cases_sha256=hashlib.sha256(source.encode()).hexdigest())
        verify_selection(selection, source)
        row["machine"] = "1RA---_------_------_------"
        with self.assertRaises(ValueError):
            verify_selection(selection, source)
        row["machine"] = "0RA---_------_------_------"
        row["index"] = "999999"
        with self.assertRaises(ValueError):
            verify_selection(selection, source)
        row["index"] = "1"
        row["ptr"] = "0"
        with self.assertRaises(ValueError):
            verify_selection(selection, source)
        row["ptr"] = "1"
        row["kind"] = "invented-kind"
        with self.assertRaises(ValueError):
            verify_selection(selection, source)
        row["kind"] = "cycle_hash_candidate"
        selection["width"] = "1%N. Axiom injected : False."
        with self.assertRaises(ValueError):
            verify_selection(selection, source)

    def test_bad_strata_and_duplicate_indices_fail_closed(self):
        row = dict(index="1", kind="cycle_hash_candidate", machine="0RA---_------_------_------", ptr="1", anchor="0", period="1", excursion_width="0", full="0", side="right")
        with tempfile.TemporaryDirectory() as d:
            p = Path(d)/"ledger.tsv"
            def write(rows):
                with p.open("w", newline="") as f:
                    w = csv.DictWriter(f, list(row), delimiter="\t")
                    w.writeheader(); w.writerows(rows)
            write([row, dict(row, anchor="2")])
            with self.assertRaises(ValueError):
                sample(p, 4)
            write([dict(row, side="arbitrary-category")])
            with self.assertRaises(ValueError):
                sample(p, 4)


if __name__ == "__main__":
    unittest.main()
