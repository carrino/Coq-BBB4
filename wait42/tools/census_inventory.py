#!/usr/bin/env python3
"""UNTRUSTED, deterministic inventory; does not walk or certify coverage.

Run from any directory: python3 wait42/tools/census_inventory.py --output
wait42/research/census-inventory.json. Hashes use repository bytes; row-set
hashes use sorted distinct machine strings, each followed by a newline.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
MACHINE = re.compile(r"(?:---|[01][LR][ABCD]){2}(?:_(?:---|[01][LR][ABCD]){2}){3}")
TEXT_LISTS = {
    "state_holdouts": "tools/census_holdouts_kept.txt",
    "state_residue": "tools/census_residue.txt",
    "state_proven_snapshot": "tools/censustr/state_tiers/proven.txt",
    "state_provenqh_snapshot": "tools/censustr/state_tiers/provenqh.txt",
    "state_rerootqh_snapshot": "tools/censustr/state_tiers/rerootqh.txt",
    "instruction_deferred_v10": "censustr_deferred_v10.txt",
    "instruction_inwalk_v7": "censustr_deferred_v7_inwalk.txt",
}
SOURCES = [
    "LICENSE", "theories/Census/TNF_QH.v", "theories/Census/Decide.v",
    "theories/Census/Run_Compute.v", "theories/Census/Run.v",
    "theories/Census/Deferred_Data.v", "theories/Census/Proven_List.v",
    "theories/Census/ProvenQH_List.v", "theories/Census/RerootQH_List.v",
    "theories/CensusTr/TNF_QHTr.v", "theories/CensusTr/DecideTr.v",
    "theories/CensusTr/RunTr_Compute.v", "theories/CensusTr/DeferredTr_Data.v",
    "tools/nghist/BB4_verified_enumeration.README", "tools/nghist/oracle_lookup.py",
    "tools/census_ladder.c", "tools/gen_deferred.py",
    "tools/censustr/classify_deferred.py",
]


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def read_text_rows(path):
    rows = []
    for number, line in enumerate(path.read_text().splitlines(), 1):
        row = line.strip()
        if row and not row.startswith("#"):
            if MACHINE.fullmatch(row) is None:
                raise ValueError(f"{path}:{number}: invalid machine row")
            rows.append(row)
    return rows


def read_coq_rows(path):
    """Decode literal eight-slot rows, not arbitrary Coq expressions."""
    rows = []
    slot = r"t(?:N|[01][LR][ABCD])"
    for match in re.finditer(r"\[(" + slot + r"(?:;" + slot + r"){7})\]", path.read_text()):
        slots = ["---" if x == "tN" else x[1:] for x in match[1].split(";")]
        rows.append("_".join("".join(slots[i:i + 2]) for i in range(0, 8, 2)))
    if not rows:
        raise ValueError(f"{path}: no literal machine rows")
    return rows


def summarize(rows):
    unique = set(rows)
    return {
        "rows": len(rows), "unique_rows": len(unique),
        "duplicate_rows": len(rows) - len(unique),
        "full_unique_rows": sum("---" not in row for row in unique),
        "partial_unique_rows": sum("---" in row for row in unique),
        "undefined_slots_histogram": dict(sorted(Counter(str(row.count("---")) for row in unique).items())),
        "sorted_unique_rows_sha256": sha256("".join(row + "\n" for row in sorted(unique)).encode()),
    }


def inventory(root=ROOT):
    lists, rowsets, fingerprints = {}, {}, {}

    def fingerprint(path):
        data = (root / path).read_bytes()
        fingerprints[path] = {"bytes": len(data), "sha256": sha256(data)}

    for name, path in TEXT_LISTS.items():
        fingerprint(path)
        rows = read_text_rows(root / path)
        lists[name] = {"paths": [path], **summarize(rows)}
        rowsets[name] = set(rows)
    for name, pattern in (("state_deferred_coq", "theories/Census/Deferred_[0-9][0-9].v"),
                          ("instruction_deferred_coq", "theories/CensusTr/DeferredTr_[0-9][0-9].v")):
        paths = sorted(root.glob(pattern))
        if not paths:
            raise ValueError(f"missing source glob: {pattern}")
        rows = []
        for path in paths:
            fingerprint(path.relative_to(root).as_posix())
            rows.extend(read_coq_rows(path))
        lists[name] = {"paths": [p.relative_to(root).as_posix() for p in paths], **summarize(rows)}
        rowsets[name] = set(rows)
    for path in SOURCES:
        fingerprint(path)
    old = rowsets["state_holdouts"] | rowsets["state_residue"]
    coq = rowsets["state_deferred_coq"]
    all_rows = set().union(*rowsets.values())
    return {
        "schema_version": 1, "trust": "untrusted bookkeeping; no coverage or waiting certificate",
        "coverage": {
            "universal_waiting_bound_proved": False,
            "full_waiting_holdout_list_available": False,
            "full_tnf_walk_performed": False,
            "labelled_tables_including_undefined": 17 ** 8,
            "labelled_total_transition_tables": 16 ** 8,
            "table_count_note": "Combinatorial counts only; neither is a TNF representative count.",
            "candidate_universe": "Adapt Census/TNF_QH full tree: first-use states, first move right, no cnt=1 pruning.",
            "limitations": [
                "Listed rows are historical subsets, not all TNF leaves and not all waiting holdouts.",
                "Legacy QHBound / NeverQuasiHalts certificates do not bound later return gaps.",
                "Different rows may share a swap/reflection/completion orbit; no orbit quotient is computed.",
                "state_tiers text snapshots are not re-extracted or verified against current Coq data lists.",
                "No all-leaf tier ledger was found or regenerated; in-walk accepted leaves are absent here.",
            ],
        },
        "lists": lists,
        "combined_observed_unique_rows": summarize(sorted(all_rows)),
        "state_deferred_crosscheck": {
            "holdouts_union_residue_unique": len(old),
            "coq_literal_unique": len(coq), "same_row_set": old == coq,
            "only_in_text_union": len(old - coq), "only_in_coq_literals": len(coq - old),
        },
        "external_halting_enumeration": {
            "url": "https://docs.bbchallenge.org/CoqBB5_release_v1.0.0/BB4_verified_enumeration.csv",
            "local_path_present": (root / "tools/nghist/BB4_verified_enumeration.csv").exists(),
            "downloaded_by_this_tool": False, "license_verified": False,
            "coverage_limitation": "oracle_lookup.py documents cnt>=1 pruning and zero full machines; unsuitable as full waiting universe.",
        },
        "source_fingerprints": dict(sorted(fingerprints.items())),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    text = json.dumps(inventory(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
