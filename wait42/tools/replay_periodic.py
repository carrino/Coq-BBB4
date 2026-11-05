#!/usr/bin/env python3
"""Generate exact Coq replay of a bounded, stratified periodic-ledger sample.

The ledger and this generator are untrusted. A successful Checked.v compilation
and recursive coqchk, not a search verdict or parsed probe, supplies proof credit.
All omitted or rejected rows remain obligations of the global census.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import heapq
import json
from pathlib import Path
import re


KINDS = {"cycle_hash_candidate", "translated_cycle_candidate"}
MACHINE = re.compile(r"(?:[01][LR][ABCD]|---){2}(?:_(?:[01][LR][ABCD]|---){2}){3}")
HEADER = """From Coq Require Import List NArith.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import TNF_QH.
From BBBWait42 Require Import Spec Batch.
Import ListNotations.
"""


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def machine_term(text: str) -> str:
    if not MACHINE.fullmatch(text):
        raise ValueError(f"invalid four-state binary table: {text!r}")
    slots = text.replace("_", "")
    arms = []
    for i in range(8):
        tr = slots[3*i:3*i+3]
        value = "None" if tr == "---" else f"Some (mkTrans S{tr[0]} D{tr[1]} St{tr[2]})"
        arms.append(f"| St{'ABCD'[i//2]}, S{i%2} => {value}")
    return "(fun q a => match q,a with " + " ".join(arms) + " end)"


def validate_row(row: dict) -> None:
    if row["kind"] not in KINDS:
        raise ValueError("invalid periodic candidate kind")
    if not isinstance(row["machine"], str) or not MACHINE.fullmatch(row["machine"]):
        raise ValueError("invalid machine table")
    for key in ("index", "ptr", "anchor", "period", "excursion_width", "full"):
        if not isinstance(row[key], str) or not re.fullmatch(r"[0-9]+", row[key]):
            raise ValueError(f"invalid {key}: {row[key]!r}")
    if int(row["period"]) == 0 or row["side"] not in {"left", "right", "stationary"}:
        raise ValueError("invalid periodic candidate")
    if row["full"] not in {"0", "1"} or row["ptr"] not in {"1", "2", "3", "4"}:
        raise ValueError("invalid family metadata")
    if ("---" not in row["machine"]) != (row["full"] == "1"):
        raise ValueError("full-table flag disagrees with the table")
    if any(int(row[k]) > 8192 for k in ("anchor", "period", "excursion_width")):
        raise ValueError("certificate exceeds the short-replay limit of 8192")


def sample(source: Path, per_stratum: int) -> tuple[list[dict], dict]:
    """Smallest SHA256 priorities, stratified by kind/direction/full/period size."""
    if per_stratum < 1:
        raise ValueError("per-stratum must be positive")
    heaps: dict[tuple, list] = {}
    counts: dict[tuple, int] = {}
    with source.open(newline="") as f:
        for row in csv.DictReader(f, delimiter="\t"):
            if row["kind"] not in KINDS:
                continue
            validate_row(row)
            key = (row["kind"], row["side"], row["full"], "short" if int(row["period"]) <= 16 else "long")
            counts[key] = counts.get(key, 0) + 1
            priority = int.from_bytes(hashlib.sha256((row["index"] + ":" + row["machine"]).encode()).digest(), "big")
            item = (-priority, -int(row["index"]), json.dumps(row, sort_keys=True))
            h = heaps.setdefault(key, [])
            if len(h) < per_stratum:
                heapq.heappush(h, item)
            elif item[:2] > h[0][:2]:
                heapq.heapreplace(h, item)
    selected = sorted((json.loads(x[2]) for h in heaps.values() for x in h), key=lambda r: int(r["index"]))
    if len({row["index"] for row in selected}) != len(selected):
        raise ValueError("duplicate selected ledger indices")
    return selected, {"/".join(k): v for k, v in sorted(counts.items())}


def entry_term(row: dict) -> str:
    validate_row(row)
    cert = ("{| pc_anchor := " + row["anchor"] + "%N; pc_period := " + row["period"]
            + "; pc_width := " + row["excursion_width"] + "; pc_left := "
            + ("true" if row["side"] == "left" else "false") + " |}")
    return "(" + machine_term(row["machine"]) + ", " + cert + ")"


def probe_source(rows: list[dict], cutoff: int, width: int) -> str:
    if type(cutoff) is not int or type(width) is not int or cutoff < 0 or width < 0:
        raise ValueError("bounds must be nonnegative")
    defs = ""
    for i, row in enumerate(rows):
        term = entry_term(row)
        provenance = hashlib.sha256(json.dumps(row, sort_keys=True).encode()).hexdigest()
        defs += f"(* Source row {row['index']}; ptr {row['ptr']}; SHA256 {provenance}. *)\n"
        defs += f"Definition entry_{i} : TM * periodic_certificate := {term}.\n"
    names = "; ".join(f"entry_{i}" for i in range(len(rows)))
    return (HEADER + defs + f"Definition entries := [{names}].\n"
            + f"Eval vm_compute in map (periodic_entry_check {cutoff}%N {width}%N) entries.\n")


def parse_results(log: str, count: int) -> list[bool]:
    matches = re.findall(r"=\s*\[([^\]]*)\]\s*:\s*list bool", log)
    if len(matches) != 1:
        raise ValueError("expected exactly one complete Coq list-bool result")
    tokens = [s.strip() for s in matches[0].split(";") if s.strip()]
    if len(tokens) != count or any(s not in {"true", "false"} for s in tokens):
        raise ValueError("incomplete or malformed Coq result; no rows discharged")
    return [s == "true" for s in tokens]


def checked_source(results: list[bool], cutoff: int, width: int) -> str:
    names = "; ".join(f"entry_{i}" for i, ok in enumerate(results) if ok)
    return HEADER + "From BBBWait42Replay Require Import Cases.\n" + f"""
Definition accepted : list (TM * periodic_certificate) := [{names}].
Theorem accepted_count : length accepted = {sum(results)}.
Proof. reflexivity. Qed.
Theorem accepted_checked : periodic_batch_check {cutoff}%N {width}%N accepted = true.
Proof. vm_compute. reflexivity. Qed.
Theorem accepted_all_completions : forall tm cert tm',
 In (tm,cert) accepted -> TM_le tm tm' ->
 periodic_result tm' (N.to_nat {cutoff}%N) (N.to_nat {width}%N).
Proof. exact (periodic_batch_completion _ _ accepted accepted_checked). Qed.
Print Assumptions accepted_all_completions.
"""


def verify_selection(selection: dict, source: str) -> None:
    """Bind reported machines and bounds to the actual probed Coq definitions."""
    if selection.get("schema_version") != 1:
        raise ValueError("unknown selection schema")
    rows = selection["selected"]
    if len({row["index"] for row in rows}) != len(rows):
        raise ValueError("duplicate selected ledger indices")
    if probe_source(rows, selection["cutoff"], selection["width"]) != source:
        raise ValueError("selection metadata does not match Cases.v")
    if hashlib.sha256(source.encode()).hexdigest() != selection["cases_sha256"]:
        raise ValueError("Cases.v changed since selection")


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--source", type=Path)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--per-stratum", type=int, default=4)
    p.add_argument("--cutoff", type=int, default=32779478)
    p.add_argument("--width", type=int, default=4096)
    p.add_argument("--expect-accepted", type=int, help="Regression gate for a frozen sample; never implies census coverage")
    p.add_argument("--probe-log", type=Path, help="Finalize an existing selection; exact proofs still need compilation and audit")
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    selection_path = args.output / "selection.json"
    # A failed attempt must not leave a prior finalization looking current.
    for name in ("Checked.v", "Checked.vo", "Checked.vos", "Checked.vok", "Checked.glob", "replay.json"):
        (args.output / name).unlink(missing_ok=True)
    if args.probe_log is None:
        if args.source is None:
            p.error("--source is required when preparing a selection")
        rows, counts = sample(args.source, args.per_stratum)
        if not rows:
            p.error("no periodic candidates selected")
        source = probe_source(rows, args.cutoff, args.width)
        (args.output / "Cases.v").write_text(source)
        selection = {"schema_version": 1, "source_sha256": digest(args.source),
                     "generator_sha256": digest(Path(__file__)), "per_stratum": args.per_stratum,
                     "cutoff": args.cutoff, "width": args.width, "strata_population": counts,
                     "selected": rows, "cases_sha256": digest(args.output / "Cases.v"),
                     "status": "untrusted selection; no proof credit"}
        selection_path.write_text(json.dumps(selection, indent=2) + "\n")
        print(json.dumps({"selected": len(rows), "population": sum(counts.values()), "status": selection["status"]}))
    else:
        selection = json.loads(selection_path.read_text())
        verify_selection(selection, (args.output / "Cases.v").read_text())
        results = parse_results(args.probe_log.read_text(), len(selection["selected"]))
        if args.expect_accepted is not None and sum(results) != args.expect_accepted:
            p.error(f"expected {args.expect_accepted} accepted entries, got {sum(results)}")
        (args.output / "Checked.v").write_text(checked_source(results, selection["cutoff"], selection["width"]))
        report = {"schema_version": 1, "selection_sha256": digest(selection_path),
                  "probe_log_sha256": digest(args.probe_log), "accepted_candidates": sum(results),
                  "rejected_candidates": len(results)-sum(results),
                  "status": "generated proofs; compile and recursively audit Checked.v before claiming proof credit",
                  "global_coverage_proved": False,
                  "rows": [dict(row, replay_candidate=ok) for row, ok in zip(selection["selected"], results)]}
        (args.output / "replay.json").write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps({k: v for k, v in report.items() if k != "rows"}))


if __name__ == "__main__":
    main()
