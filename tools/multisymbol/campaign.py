#!/usr/bin/env python3
"""Reproduce small census candidates. Only Coq establishes their validity.

Run `make -C small search` first. Working data stays in small/build.
This writes a candidate .v there; it never replaces a checked theorem.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
BUILD = ROOT / "small/build"

# kind, window/block length, anchor, exploration fuel, rounds/threshold/history.
PLANS = {
    "32": (3, 2, 55, 55, "both", [
        ("ng", 2, 55, 4096, 32),
        ("ng", 3, 55, 4096, 32),
        ("rw", 1, 128, 1024, 2),
        ("rw", 2, 128, 2048, 2),
        ("finite", 2, 128, 4096, 128),
        ("hist", 2, 128, 4096, 2),
        ("rw", 2, 512, 1024, 3),
        ("rw", 3, 512, 1024, 2),
    ]),
    "23-conditional": (2, 3, 59, 67, "both", [
        ("ng", 2, 67, 4096, 32),
        ("ng", 3, 67, 4096, 32),
        ("ng", 4, 67, 4096, 32),
        ("rw", 1, 128, 1024, 2),
        ("rw", 2, 128, 2048, 2),
        ("rw", 3, 128, 4096, 2),
    ]),
    "32-state": (3, 2, 55, 55, "state", [
        ("ng", 2, 55, 4096, 32),
        ("rw", 1, 55, 512, 2),
        ("rw", 2, 55, 1024, 2),
        ("rw", 3, 55, 2048, 2),
        ("rw", 4, 55, 8192, 2),
        ("finite", 2, 55, 4096, 128),
        ("hist", 2, 55, 4096, 2),
    ]),
    "22": (2, 2, 6, 8, "both", [("ng", 2, 8, 4096, 32)]),
    "23-state": (2, 3, 59, 67, "state", [
        ("ng", 2, 67, 4096, 32),
        ("rw", 1, 67, 512, 2),
        ("rw", 2, 67, 1024, 2),
        ("ng", 3, 67, 4096, 32),
        ("ng", 4, 67, 4096, 32),
        ("rw", 4, 67, 8192, 2),
        ("finite", 2, 67, 4096, 128),
    ]),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("plan", choices=PLANS)
    args = parser.parse_args()
    ns, ms, bs, bi, mode, plan = PLANS[args.plan]
    work = BUILD / args.plan
    work.mkdir(parents=True, exist_ok=True)
    prefix = work / "survey"
    with (work / "survey.json").open("w") as output:
        subprocess.run([str(BUILD / "survey"), str(prefix), str(ms), "256", "64", str(ns)],
                       stdout=output, check=True)
    source = Path(str(prefix) + ".unresolved.txt")
    known = {"32": "known32.json", "23-conditional": "known23.json"}.get(args.plan)
    known_path = ROOT / "small/certificates" / known if known else None
    known_machines = ({d["machine"].replace("_", "")
                       for d in json.loads(known_path.read_text())} if known_path else set())
    stages = []
    for i, (kind, n, t, fuel, extra) in enumerate(plan):
        residue = work / f"residue-{i:02d}.txt"
        # Keep registry leaves in the census residue, but do not spend search
        # time rediscovering their existing proofs. Only newly solved leaves
        # disappear from a stage, so the generator assigns certificates safely.
        previous = source.read_text().splitlines()
        registered = [m for m in previous if m.replace("_", "") in known_machines]
        probe_input = work / f"probe-input-{i:02d}.txt"
        probe_residue = work / f"probe-residue-{i:02d}.txt"
        probe_input.write_text("".join(m + "\n" for m in previous
                                       if m.replace("_", "") not in known_machines))
        command = [BUILD / "probe", ("state-" if mode == "state" else "") + kind,
                   probe_input, probe_residue, ns, ms, bs, bi, n, t, fuel, extra]
        subprocess.run(list(map(str, command)), check=True)
        residue.write_text("".join(m + "\n" for m in
                           sorted(registered + probe_residue.read_text().splitlines())))
        certificate = {
            "ng": f"NGram {n} {t}",
            "rw": f"RepWL {n} {extra} {t} {fuel}",
            "finite": f"FiniteNGram {n} {t} {fuel} {extra}",
            "hist": f"HistNGram {extra} {n} {t} {fuel} 128",
        }[kind]
        stages.append(dict(input=str(source), residue=str(residue), certificate=certificate))
        source = residue
    stages_path = work / "stages.json"
    stages_path.write_text(json.dumps(stages, indent=2) + "\n")
    if {m.replace("_", "") for m in source.read_text().splitlines()} - known_machines:
        raise SystemExit(f"Unresolved machines remain in {source}")
    output = work / "Census.v"
    subprocess.run([sys.executable, str(Path(__file__).with_name("generate_certificates.py")),
                    str(prefix) + ".certificates.tsv", str(stages_path), str(output),
                    "--states", str(ns), "--symbols", str(ms), "--state-bound", str(bs),
                    "--instruction-bound", str(bi), "--mode", mode]
                   + (["--known", str(known_path)] if known_path else [])
                   + (["--residue"] if args.plan == "23-conditional" else []), check=True)
    print(f"Candidate generated: {output}\nCompile it with coqc to check the claim.")


if __name__ == "__main__":
    main()
