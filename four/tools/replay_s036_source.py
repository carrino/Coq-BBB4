"""Rebuild the frozen S036 proof from source, without historical workspace objects.

All accepted report, compact input, renderer and Coq source bytes remain pinned.
The 146-entry preservation map is retained as author provenance; its unrelated
artifact targets are not proof dependencies. Every replay compiles the exact five
original modules and performs a fresh full recursive kernel audit without reuse.
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
PACKAGE = "burn31-s036"
NAMESPACE = "BBB24Burn31S036"
MACHINE = "1LB2LA2RB1RA_3RB3LA0LB0RB"
REPORT_SHA256 = "821fab7fd2abddf9358709509e776f9a7f4d70f95b14edb042f32b1395f036c5"
SHARED_SHA256 = "5727993233c1f8971a1ba0371e1b6814cd55b99246f9ab28efc6c85cbf0dadfb"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def require(test, message):
    if not test:
        raise ValueError(message)


def prepare():
    checker_sha256 = sha(Path(__file__))
    report_path = ROOT / "research/burn31-s036-checked.json"
    helper = ROOT / "tools/replay_shared_state_case.py"
    # Check both trust anchors before importing any project Python.
    require(sha(report_path) == REPORT_SHA256, "Frozen S036 report changed")
    require(sha(helper) == SHARED_SHA256, "Frozen source validator changed")
    shared = importlib.import_module("replay_shared_state_case")
    frozen = json.loads(report_path.read_text())
    shared.source_groups(frozen)
    input_path = ROOT / "research/burn31-s036-proof-input.json"
    data = json.loads(input_path.read_text())
    rows = data["rows"]
    require(rows == [dict(machine=MACHINE, code=1273477485)]
            and data["state_bound"] == 0 and data["metadata_revision"] == 1,
            "Unexpected S036 machine, code or scope")
    selection = ROOT / data["selection_report"]
    native = json.loads(selection.read_text())
    require(sha(selection) == data["selection_sha256"]
            and native["rows"] == rows and native["metadata_revision"] == 1,
            "Frozen native input differs")
    checkpoint = ROOT / "research/state-holdouts-78.txt"
    require(sha(checkpoint) == data["frozen_checkpoint_sha256"]
            and checkpoint.read_text().splitlines()[35] == MACHINE,
            "Original S036 checkpoint membership differs")
    prior = ROOT / native["prior_remaining_report"]
    require(sha(prior) == native["prior_remaining_sha256"]
            and len(prior.read_text().splitlines()) == native["prior_remaining_count"] == 12
            and MACHINE in prior.read_text().splitlines(), "Frozen prior frontier differs")
    programs = ROOT / native["programs_report"]
    require(sha(programs) == native["programs_sha256"], "Frozen context programs differ")
    preserved = ROOT / "research/burn31-s036-preserved-pins.json"
    preservation_map = json.loads(preserved.read_text())
    require(sha(preserved) == data["preserved_pins_sha256"]
            and preservation_map == frozen["preserved_artifacts_sha256"]
            and len(preservation_map) == 146, "Frozen preservation provenance differs")
    # Deliberately do not dereference preservation_map: it records author workspace
    # preservation, not imports or premises of S036's mathematical proof.
    inputs = {str(p.relative_to(ROOT)): sha(p) for p in
              (input_path, selection, programs, checkpoint, prior, preserved)}
    require(inputs == frozen["inputs_sha256"], "Regenerated compact input closure differs")
    require(data["template_sha256"] == frozen["template_sha256"]
            and set(data["template_sha256"]) == {
                "proof-sources/burn31-s036/WordCycle.v",
                "proof-sources/burn31-s036/Regression.v"}, "Template inventory differs")
    # All original producer/import source pins were checked above.
    producer = importlib.import_module("check_burn31_s036")
    campaign = importlib.import_module("check_campaign")
    codes = importlib.import_module("generate_pipeline_examples").codes
    kernel = importlib.import_module("kernel_audit_cache_v3")
    require(producer.MACHINE == MACHINE and producer.NS == NAMESPACE
            and codes(MACHINE) == [5, 8, 11, 6, 15, 12, 1, 3]
            and rows[0]["code"] == sum(v * 17**i for i, v in enumerate(codes(MACHINE))),
            "Exact machine identity differs")
    build = ROOT / "build/burn31-s036/proof"
    paths = [(ROOT / "theories", "BBB24"), (build, NAMESPACE)]
    descriptor = dict(
        id="burn31_s036", scope="state", rows=1, state_bound=0, instruction_bound=None,
        module=NAMESPACE + ".Inventory", board="board", small_sound="small_sound",
        sound="sound", was_pending="was_pending",
        proof_source="build/burn31-s036/proof/Inventory.v",
        exact_inventory_theorem=NAMESPACE + ".Inventory.inventory_exact",
        inventories=[dict(path="research/burn31-s036-machines.json", format="rows")],
        load_paths=[dict(path="build/burn31-s036/proof", namespace=NAMESPACE)],
    )
    require(descriptor == frozen["descriptor"], "Descriptor differs from original theorem")
    require(frozen["checked_state_families"] == 1 and frozen["checked_instruction_families"] == 0,
            "Frozen proof counts differ")
    files = []
    for name in ("WordCycle.v", "Regression.v"):
        target = build / name
        shared.exact(target, (ROOT / "proof-sources/burn31-s036" / name).read_text())
        files.append(target)
    path = build / "Example00.v"
    shared.exact(path, producer.example(0, rows[0]))
    files.append(path)
    path = build / "Board.v"
    shared.exact(path, producer.board(rows))
    files.append(path)
    path = build / "Inventory.v"
    shared.exact(path, campaign.inventory_source(dict(
        descriptor, module=NAMESPACE + ".Board", machines=[MACHINE])))
    files.append(path)
    require(set(build.glob("*.v")) == set(files), "Unexpected generated module")
    require(set(frozen["object_sha256"]) == {
        str(p.with_suffix(".vo").relative_to(ROOT)) for p in files}, "Module inventory differs")
    inventory_path = ROOT / descriptor["inventories"][0]["path"]
    inventory = json.dumps(dict(rows=[dict(machine=MACHINE)]), indent=2) + "\n"
    require(inventory_path.read_text() == inventory, "Regenerated inventory differs")
    flags = [part for path, namespace in paths for part in ("-Q", str(path), namespace)]
    sources = campaign.dependency_hashes(files, flags)
    sources.update({p: sha(ROOT / p) for p in frozen["source_sha256"] if p.startswith("tools/")})
    require(sources == frozen["source_sha256"], "Regenerated source dependency closure differs")
    shared.source_groups(frozen, generated=True)
    protected = {report_path: REPORT_SHA256, helper: SHARED_SHA256,
                 Path(__file__): checker_sha256, inventory_path: sha(inventory_path)}
    return dict(frozen=frozen, files=files, paths=paths, flags=flags, shared=shared,
                kernel=kernel, protected=protected, preservation_map_sha256=sha(preserved))


def replay(context, timeout, audit_timeout):
    files, kernel = context["files"], context["kernel"]
    output = ROOT / "build/s036-source-replay/burn31-s036"
    output.mkdir(parents=True, exist_ok=True)
    receipt, log = kernel.fresh_paths(output, "kernel-audit")
    timings, compile_logs = {}, {}
    for path in files:
        started = time.monotonic()
        compile_log = output / (receipt.stem + "-" + path.stem + ".log")
        with compile_log.open("w") as stream:
            subprocess.run(["coqc", "-w", "-abstract-large-number", "-native-compiler", "no",
                            *context["flags"], str(path)], stdout=stream, stderr=subprocess.STDOUT,
                           check=True, timeout=timeout)
        timings[path.stem] = round(time.monotonic() - started, 3)
        compile_logs[str(compile_log.relative_to(ROOT))] = sha(compile_log)
        print("Compiled " + path.stem + ": " + str(timings[path.stem]) + "s", flush=True)
    started = time.monotonic()
    audit = kernel.audit([NAMESPACE + ".Inventory"], [files[-1]], context["paths"],
                         receipt, log, recursive=True, timeout=audit_timeout)
    audit_seconds = round(time.monotonic() - started, 3)
    require(audit["kind"] == "recursive" and audit["parents"] == [] and audit["reused_modules"] == [],
            "Audit must check the full recursive closure without reuse")
    require(set(audit["checked_modules"]) == set(audit["snapshot"]["graph"])
            and all(NAMESPACE + "." + p.stem in audit["checked_modules"] for p in files),
            "Audit module closure differs")
    validation = kernel.ReceiptValidation()
    require(validation.load(receipt) == audit, "Published kernel receipt differs")
    require(kernel.snapshot([files[-1]], context["paths"]) == audit["snapshot"],
            "Current source/object/runtime closure changed")
    context["shared"].source_groups(context["frozen"], generated=True)
    for path, expected in context["protected"].items():
        require(sha(path) == expected, "Frozen metadata or replay checker changed: " + str(path))
    context["shared"].pins(compile_logs)
    validation.recheck()
    frozen = context["frozen"]
    record = dict(
        schema=1, package=PACKAGE, scope=frozen["scope"], descriptor=frozen["descriptor"],
        frozen_report_sha256=REPORT_SHA256, checked_state_families=1, checked_instruction_families=0,
        inputs_sha256=frozen["inputs_sha256"], template_sha256=frozen["template_sha256"],
        source_sha256=frozen["source_sha256"], inventory_sha256=frozen["inventory_sha256"],
        replay_checker_sha256=sha(Path(__file__)), shared_validator_sha256=SHARED_SHA256,
        historical_preservation_provenance=dict(
            map_sha256=context["preservation_map_sha256"], entries=146, targets_dereferenced=False,
            scope="Author workspace preservation only; unrelated artifact targets are not proof dependencies."),
        compile_seconds=timings, compile_log_sha256=compile_logs, audit_seconds=audit_seconds,
        checked_modules=len(audit["checked_modules"]), reused_modules=0,
        kernel_receipt=str(receipt.relative_to(ROOT)), kernel_receipt_sha256=sha(receipt),
        current_runtime=audit["snapshot"]["runtime"],
        object_sha256={str(p.with_suffix(".vo").relative_to(ROOT)): sha(p.with_suffix(".vo")) for p in files},
    )
    (output / "current-proof-receipt.json").write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print("S036 exact source proof compiled and fully recursively audited.", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout", type=int, default=600)
    parser.add_argument("--audit-timeout", type=int, default=3600)
    args = parser.parse_args()
    if min(args.timeout, args.audit_timeout) < 1:
        parser.error("Positive budgets required")
    resource.setrlimit(resource.RLIMIT_AS, (3 * 1024**3, 3 * 1024**3))
    resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, resource.RLIM_INFINITY))
    replay(prepare(), args.timeout, args.audit_timeout)


if __name__ == "__main__":
    main()
