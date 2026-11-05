"""Small deterministic native surveys; none exceeds 1,000 popped nodes."""
import csv
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
BUILD = ROOT / "wait42/build"


class CensusProbeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        BUILD.mkdir(parents=True, exist_ok=True)
        cls.temp = tempfile.TemporaryDirectory(prefix="probe-tests-", dir=BUILD)
        cls.directory = Path(cls.temp.name)
        cls.binary = cls.directory / "census_probe"
        subprocess.run(["gcc", "-O2", "-std=c11", "-Wall", "-Wextra", "-Werror",
                        str(ROOT / "wait42/tools/census_probe.c"), "-o", str(cls.binary)], check=True)
        cls.comparison = cls.directory / "ngram_comparison"
        comparison_source = cls.directory / "ngram_comparison.c"
        comparison_source.write_text(f'''#define main legacy_census_ladder_main
#include "{ROOT / 'tools/census_ladder.c'}"
#undef main
#include "{ROOT / 'wait42/tools/ngram_tail.inc'}"
int main(void) {{
  const char *machines[] = {{"1RB---_0RB---_------_------", "0RB---_0RA---_------_------"}};
  for (int m = 0; m < 2; ++m) for (int t = 0; t < 2; ++t) {{
    uint8_t slots[8]; if (!parse_tm(machines[m], slots)) return 2;
    wipe_tape(); int legacy = ngram_check(slots, 1, t);
    wipe_tape(); int tail = tail_ngram_check(slots, 1, t);
    wipe_tape(); printf("%d %d %d %d\\n", m, t, legacy, tail);
  }}
  return 0;
}}
''')
        subprocess.run(["gcc", "-O2", "-std=c11", "-Wall", "-Wextra", "-Werror",
                        str(comparison_source), "-o", str(cls.comparison)], check=True)

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def run_probe(self, label, maximum, gas, *extra):
        prefix = self.directory / label
        run = subprocess.run([str(self.binary), "--max-nodes", str(maximum), "--gas", str(gas),
                              "--output", str(prefix), *extra], check=True, text=True,
                             capture_output=True, timeout=30)
        summary = json.loads(run.stdout)
        self.assertEqual(summary, json.loads(prefix.with_suffix(".summary.json").read_text()))
        files = {suffix: prefix.with_suffix("." + suffix).read_bytes()
                 for suffix in ("ledger.tsv", "residual.tsv", "frontier.tsv", "summary.json")}
        rows = {key: list(csv.DictReader(io.StringIO(value.decode()), delimiter="\t"))
                for key, value in files.items() if key.endswith(".tsv")}
        self.assertLessEqual(summary["nodes_visited"], maximum)
        self.assertEqual(summary["seed_nodes"] + summary["generated_children"],
                         summary["nodes_visited"] + summary["pending"])
        self.assertEqual(summary["nodes_visited"], summary["expanded_popped_nodes"] +
                         summary["cycle_candidates"] + summary["translated_cycle_candidates"] +
                         summary["ngram_candidates"] + summary["unknown"])
        self.assertEqual(len(rows["ledger.tsv"]), summary["nodes_visited"] +
                         summary["virtual_root_expanded"])
        self.assertEqual(len(rows["frontier.tsv"]), summary["pending"])
        self.assertEqual(len(rows["residual.tsv"]), summary["unknown"] + summary["pending"])
        self.assertEqual(summary["kernel_credit"], 0)
        self.assertFalse(summary["coverage_proved"])
        self.assertEqual(summary["ngram_tier"], "tail_ngram")
        self.assertTrue(summary["stack_accounting_ok"])
        for row in rows["ledger.tsv"] + rows["frontier.tsv"]:
            self.assertIn(int(row["ptr"]), (1, 2, 3, 4))
        return summary, rows, files

    def test_zero_budget_preserves_all_four_roots(self):
        data, rows, _ = self.run_probe("zero", 0, 64)
        self.assertEqual(data["nodes_visited"], 0)
        self.assertEqual(data["pending"], 4)
        self.assertEqual([row["machine"][:3] for row in rows["frontier.tsv"]],
                         ["0RA", "1RA", "0RB", "1RB"])
        self.assertEqual(rows["ledger.tsv"][0]["kind"], "halt_completion")
        self.assertEqual(rows["ledger.tsv"][0]["halt_slot"], "0")

    def test_one_halt_pop_expands_every_next_state_direction_and_write(self):
        data, rows, _ = self.run_probe("one", 1, 8, "--root", "0RB")
        self.assertEqual(data["expanded_popped_nodes"], 1)
        self.assertEqual(data["generated_children"], 12)
        children = rows["frontier.tsv"]
        self.assertEqual({row["machine"][7:10] for row in children},
                         {f"{write}{direction}{state}" for write in "01"
                          for direction in "LR" for state in "ABC"})
        for row in children:
            self.assertEqual(row["ptr"], "3" if row["machine"][9] == "C" else "2")

    def test_unknown_is_explicit_and_short_roots_finish(self):
        data, rows, _ = self.run_probe("unknown", 10, 0, "--root", "0RA")
        self.assertEqual(data["unknown"], 1)
        self.assertEqual(rows["residual.tsv"][0]["kind"], "unknown")
        for root, tier in (("0RA", "cycle_candidates"), ("1RA", "translated_cycle_candidates")):
            data, rows, _ = self.run_probe(root, 10, 64, "--root", root)
            self.assertEqual(data[tier], 1)
            self.assertTrue(data["tree_exhausted_untrusted"])
            row = rows["ledger.tsv"][0]
            self.assertEqual(int(row["period"]), 1)
            self.assertEqual(row["side"], "right")
            self.assertEqual(row["trust"], "untrusted")

    def test_pilot_full_machines_last_hole_and_reproducibility(self):
        left, rows, files = self.run_probe("pilot-a", 1000, 64, "--rungs", "1:0,2:0")
        right, _, repeated = self.run_probe("pilot-b", 1000, 64, "--rungs", "1:0,2:0")
        self.assertEqual(left, right)
        self.assertEqual(files, repeated)
        self.assertGreater(left["full_nodes_visited"], 0)
        self.assertGreater(left["ngram_candidates"], 0)
        halts = [row for row in rows["ledger.tsv"] if row["kind"] == "halt_completion"
                 and row["machine"] != "------_------_------_------"]
        self.assertTrue(any(row["machine"].count("---") == 1 for row in halts))
        self.assertEqual(left["generated_children"],
                         sum(4 * (min(int(row["ptr"]), 3) + 1) for row in halts))
        self.assertEqual(left["full_nodes_visited"],
                         sum(int(row["full"]) for row in rows["ledger.tsv"]))
        for row in rows["ledger.tsv"]:
            if row["kind"] == "tail_ngram_candidate":
                self.assertEqual(int(row["candidate_wait_upper"]), int(row["contexts"]) + 1)
                self.assertEqual(row["ngram_n"], "2")

    def test_tail_gate_ignores_only_prefix_states(self):
        run = subprocess.run([str(self.comparison)], check=True, capture_output=True,
                             text=True, timeout=30)
        values = {tuple(map(int, row.split()[:2])): tuple(map(int, row.split()[2:]))
                  for row in run.stdout.splitlines()}
        # At anchor 1, A has disappeared: legacy rejects, tail accepts.
        self.assertEqual(values[(0, 1)], (0, 1))
        # At anchor 0, A appears in the closure, with a B cycle avoiding it.
        # This real rank obstruction must still reject both checkers.
        self.assertEqual(values[(0, 0)], (0, 0))
        # Two alternating states both recur; the tail relaxation preserves acceptance.
        self.assertEqual(values[(1, 0)], (1, 1))
        self.assertEqual(values[(1, 1)], (1, 1))

    def test_bad_limits_roots_and_rungs_fail_before_survey(self):
        for extra in (("--gas", "8193"), ("--gas", "-1"), ("--root", "1RC"),
                      ("--max-nodes", "-1"), ("--rungs", "0:0"),
                      ("--rungs", "9:0"), ("--rungs", "2:65"),
                      ("--rungs", "2:0,"), ("--holdouts", "anything")):
            run = subprocess.run([str(self.binary), "--max-nodes", "1", "--gas", "64", *extra],
                                 capture_output=True, text=True)
            self.assertEqual(run.returncode, 2, (extra, run.stderr))


if __name__ == "__main__":
    unittest.main()
