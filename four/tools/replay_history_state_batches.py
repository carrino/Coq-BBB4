"""Rebuild the frozen closed16/4/3 state batches with current dependencies.

The original reports, renderers and statements remain immutable. A current,
fully recursive HistoryMarker receipt replaces historical compiled-object byte
comparisons. Each selected batch is compiled and recursively audited afresh.
"""

import argparse
import hashlib
import importlib
import json
from pathlib import Path
import resource
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
SHARED_SHA256 = "5727993233c1f8971a1ba0371e1b6814cd55b99246f9ab28efc6c85cbf0dadfb"
BATCHES = {
    "closed16": (16, "144d81e9f3a54e0491d91129b2850d1af10ef4cdb61abc5a0b6d2bbe97a1e19e"),
    "closed4": (4, "5b6afe7b236614230515a20f66ddce6479cb14d6de8820d291c63eec3d1b7e37"),
    "closed3": (3, "2d532fc0aa343f07d035d0574076fda068d6b889e7261fd143288b7e80aadbd4"),
}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def require(test, message):
    if not test:
        raise ValueError(message)


def prepare(batch):
    require(batch in BATCHES, "Unsupported historical batch")
    helper = ROOT / "tools/replay_shared_state_case.py"
    require(sha(helper) == SHARED_SHA256, "Frozen prerequisite validator changed")
    shared = importlib.import_module("replay_shared_state_case")
    count, report_sha = BATCHES[batch]
    package = "burn12-history-marker-" + batch
    report_path = ROOT / "research" / (package + "-checked.json")
    require(sha(report_path) == report_sha, "Frozen batch report changed")
    frozen = json.loads(report_path.read_text())
    shared.source_groups(frozen)
    data = json.loads((ROOT / "research" / (package + "-proof-input.json")).read_text())
    rows = data["rows"]
    require(data["state_bound"] == 0 and len(rows) == count, "Unexpected batch scope")
    require(len({r["machine"] for r in rows}) == count, "Duplicate machine")
    selection = ROOT / data["selection_report"]
    require(sha(selection) == data["selection_sha256"], "Frozen selection changed")
    require(rows == json.loads(selection.read_text())["rows"], "Selection rows differ")
    dependency_name = "burn12-history-marker"
    dependency_report = ROOT / "research" / (dependency_name + "-checked.json")
    require(sha(dependency_report) == data["generic_report_sha256"], "Frozen generic report changed")
    generic = json.loads(dependency_report.read_text())
    shared.source_groups(generic)
    # Import project renderers only after their source pins have been checked.
    pilot = importlib.import_module("check_burn12_history_marker")
    campaign = importlib.import_module("check_campaign")
    codes = importlib.import_module("generate_pipeline_examples").codes
    kernel = importlib.import_module("kernel_audit_cache_v3")
    for row in rows:
        table = codes(row["machine"])
        require(len(table) == 8 and all(0 <= v < 16 for v in table), "Expected a complete two-state table")
        require(row["code"] == sum(v * 17**i for i, v in enumerate(table)), "Machine code differs")
        require(len(row["weights"]) == 4 and row["weights"][0] == 0
                and row["invariant"] == "conditional" and 0 < row["history_marker_mask"] < 256,
                "Invalid history-marker parameters")
    dependency = shared.dependency_current(dependency_name, generic, kernel)
    output = ROOT / "build" / package / "proof"
    output.mkdir(parents=True, exist_ok=True)
    namespace = "BBB24Burn12HistoryMarker" + batch.capitalize()
    paths = [(ROOT / "theories", "BBB24"), (pilot.OUTPUT, pilot.NS), (output, namespace)]
    descriptor = dict(
        id="burn12_history_marker_" + batch, scope="state", rows=count, state_bound=0,
        instruction_bound=None, module=namespace + ".Inventory", board="board",
        small_sound="small_sound", sound="sound", was_pending="was_pending",
        proof_source=str((output / "Inventory.v").relative_to(ROOT)),
        exact_inventory_theorem=namespace + ".Inventory.inventory_exact",
        inventories=[dict(path="research/" + package + "-machines.json", format="rows")],
        load_paths=[dict(path=str(p.relative_to(ROOT)), namespace=ns) for p, ns in paths[1:]],
    )
    require(descriptor == frozen["descriptor"], "Descriptor differs from original theorem")
    files = []
    for i, row in enumerate(rows):
        path = output / f"Example{i:02d}.v"
        shared.exact(path, pilot.example(i, row))
        files.append(path)
    path = output / "Board.v"
    shared.exact(path, pilot.board(rows).replace("From " + pilot.NS + " Require Import Example",
                                               "From " + namespace + " Require Import Example"))
    files.append(path)
    path = output / "Inventory.v"
    shared.exact(path, campaign.inventory_source(dict(
        descriptor, module=namespace + ".Board", machines=[r["machine"] for r in rows])))
    files.append(path)
    inventory_path = ROOT / descriptor["inventories"][0]["path"]
    inventory = json.dumps(dict(rows=[dict(machine=r["machine"]) for r in rows]), indent=2) + "\n"
    require(inventory_path.read_text() == inventory, "Regenerated inventory differs")
    flags = [part for p, ns in paths for part in ("-Q", str(p), ns)]
    sources = campaign.dependency_hashes(files, flags)
    sources.update({p: sha(ROOT / p) for p in frozen["source_sha256"] if p.startswith("tools/")})
    inputs = {str(p.relative_to(ROOT)): sha(p) for p in
              (ROOT / "research" / (package + "-proof-input.json"), selection, dependency_report)}
    require(sources == frozen["source_sha256"], "Regenerated source dependency closure differs")
    require(inputs == frozen["inputs_sha256"], "Regenerated input closure differs")
    require(frozen["checked_state_families"] == count and frozen["checked_instruction_families"] == 0,
            "Frozen proof counts differ")
    require(set(frozen["object_sha256"]) == {str(p.with_suffix(".vo").relative_to(ROOT)) for p in files},
            "Generated module inventory differs")
    shared.source_groups(frozen, generated=True)
    protected = {report_path: report_sha, dependency_report: sha(dependency_report),
                 inventory_path: sha(inventory_path), helper: SHARED_SHA256,
                 Path(__file__): sha(Path(__file__)), dependency["path"]: dependency["sha256"]}
    return dict(package=package, frozen=frozen, files=files, paths=paths, flags=flags,
                namespace=namespace, dependency=dependency, kernel=kernel, shared=shared,
                protected=protected, count=count, report_sha256=report_sha)


def replay(context, timeout, audit_timeout):
    package, files, kernel = context["package"], context["files"], context["kernel"]
    output = ROOT / "build/history-state-batch-replay" / package
    output.mkdir(parents=True, exist_ok=True)
    timings = {}
    for path in files:
        started = time.monotonic()
        with (output / (path.stem + ".log")).open("w") as log:
            subprocess.run(["coqc", "-w", "-abstract-large-number", "-native-compiler", "no",
                            *context["flags"], str(path)], stdout=log, stderr=subprocess.STDOUT,
                           check=True, timeout=timeout)
        timings[path.stem] = round(time.monotonic() - started, 3)
        print("Compiled " + path.stem + ": " + str(timings[path.stem]) + "s", flush=True)
    receipt, log = kernel.fresh_paths(output, "kernel-audit")
    started = time.monotonic()
    audit = kernel.audit([context["namespace"] + ".Inventory"], [files[-1]], context["paths"],
                         receipt, log, recursive=True, timeout=audit_timeout)
    audit_seconds = round(time.monotonic() - started, 3)
    require(audit["kind"] == "recursive" and audit["parents"] == [] and audit["reused_modules"] == [],
            "Batch audit must check the complete dependency closure without reuse")
    require(set(audit["checked_modules"]) == set(audit["snapshot"]["graph"]), "Audit module closure differs")
    require(kernel.snapshot([files[-1]], context["paths"]) == audit["snapshot"], "Batch closure changed")
    dependency = context["dependency"]
    dependency["validation"].recheck()
    require(kernel.snapshot(dependency["roots"], dependency["paths"]) == dependency["snapshot"],
            "Generic dependency changed during replay")
    context["shared"].source_groups(context["frozen"], generated=True)
    for path, expected in context["protected"].items():
        require(sha(path) == expected, "Frozen/current prerequisite metadata changed: " + str(path))
    record = dict(
        schema=1, package=package, scope=context["frozen"]["scope"],
        descriptor=context["frozen"]["descriptor"], frozen_report_sha256=context["report_sha256"],
        checked_state_families=context["count"], checked_instruction_families=0,
        inputs_sha256=context["frozen"]["inputs_sha256"], source_sha256=context["frozen"]["source_sha256"],
        inventory_sha256=context["frozen"]["inventory_sha256"], replay_checker_sha256=sha(Path(__file__)),
        compile_seconds=timings, audit_seconds=audit_seconds,
        checked_modules=len(audit["checked_modules"]), reused_modules=0,
        dependency_current_receipt=str(dependency["path"].relative_to(ROOT)),
        dependency_current_receipt_sha256=dependency["sha256"],
        dependency_kernel_receipt_sha256=dependency["receipt_sha256"],
        kernel_receipt=str(receipt.relative_to(ROOT)), kernel_receipt_sha256=sha(receipt),
        current_runtime=audit["snapshot"]["runtime"],
        object_sha256={str(p.with_suffix(".vo").relative_to(ROOT)): sha(p.with_suffix(".vo")) for p in files},
    )
    (output / "current-proof-receipt.json").write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print(package + " compiled and fully recursively audited.", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--batch", choices=sorted(BATCHES), required=True)
    parser.add_argument("--timeout", type=int, default=600)
    parser.add_argument("--audit-timeout", type=int, default=3600)
    args = parser.parse_args()
    if min(args.timeout, args.audit_timeout) < 1:
        parser.error("Positive budgets required")
    resource.setrlimit(resource.RLIMIT_AS, (3 * 1024**3, 3 * 1024**3))
    resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, resource.RLIM_INFINITY))
    replay(prepare(args.batch), args.timeout, args.audit_timeout)


if __name__ == "__main__":
    main()
