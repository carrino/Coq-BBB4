"""Tests for parsing and inventory consistency; no mathematical proof claims."""
import tempfile
from pathlib import Path
import unittest

import census_inventory as census


class InventoryTests(unittest.TestCase):
    def test_text_rejects_foreign_state_and_trailing_data(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / "rows.txt"
            for text in ("1RE---_------_------_------", "1RA---_------_------_------ HALT"):
                path.write_text(text + "\n")
                with self.assertRaises(ValueError):
                    census.read_text_rows(path)

    def test_coq_literal_decodes_holes_and_order(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / "Rows.v"
            path.write_text("Definition rows := [[t1RB;tN;t0LC;t0RA;t0LD;tN;t1RA;t1LC]].")
            self.assertEqual(census.read_coq_rows(path), ["1RB---_0LC0RA_0LD---_1RA1LC"])

    def test_set_hash_ignores_order_and_duplicates(self):
        a, b = "1RA---_------_------_------", "0RB---_------_------_------"
        left, right = census.summarize([a, b, a]), census.summarize([b, a])
        self.assertEqual(left["sorted_unique_rows_sha256"], right["sorted_unique_rows_sha256"])
        self.assertEqual(left["duplicate_rows"], 1)
        self.assertEqual(left["undefined_slots_histogram"], {"7": 2})

    def test_frozen_deferred_sources_match_without_coverage_claim(self):
        data = census.inventory()
        self.assertTrue(data["state_deferred_crosscheck"]["same_row_set"])
        self.assertFalse(data["coverage"]["universal_waiting_bound_proved"])
        self.assertFalse(data["coverage"]["full_waiting_holdout_list_available"])


if __name__ == "__main__":
    unittest.main()
