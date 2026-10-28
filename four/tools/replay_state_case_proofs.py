"""Build and recursively audit the frozen standalone BBB(2,4) state cases."""

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
FOUR = ROOT / "four"
MANIFEST = FOUR / "research/state-case-proofs-checkpoint.json"
BUILD = FOUR / "build/state-case-proof-replay"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--only", help="Replay one package, including its prerequisites")
    selection.add_argument("--group", type=int, choices=(1, 2, 3), help="CI partition")
    parser.add_argument("--list", action="store_true", help="List packages without building")
    parser.add_argument("--jobs", type=int, default=2, help="Public-theory make workers")
    parser.add_argument("--timeout", type=int, default=600, help="Per-module driver budget")
    parser.add_argument("--audit-timeout", type=int, default=3600)
    args = parser.parse_args()
    if min(args.jobs, args.timeout, args.audit_timeout) < 1:
        parser.error("Budgets and worker count must be positive")
    manifest = json.loads(MANIFEST.read_text())
    packages = {p["package"]: p for p in manifest["packages"]}
    if args.only and args.only not in packages:
        parser.error("Unknown package: " + args.only)
    selected = [p for p in packages.values() if
                (not args.only or p["package"] == args.only) and
                (not args.group or p["group"] == args.group)]
    if args.list:
        for package in selected:
            print(f'{package["package"]}: ' + ", ".join(c["id"] for c in package["cases"]))
        return

    # Fail before compiling if a frozen source, input, report, or note changed.
    for name, expected in manifest["files_sha256"].items():
        path = ROOT / name
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError("Frozen checkpoint file missing or changed: " + name)
    for tool in ("make", "coqc", "coqchk"):
        if shutil.which(tool) is None:
            raise RuntimeError(tool + " missing; activate the Coq toolchain first")

    BUILD.mkdir(parents=True, exist_ok=True)
    result = {"scope": manifest["scope"], "selected": [p["package"] for p in selected],
              "status": "running", "commands": []}
    result_path = BUILD / "result.json"

    def save():
        result_path.write_text(json.dumps(result, indent=2) + "\n")

    def run(label, command):
        log = BUILD / f"{len(result['commands']):02d}-{label}.log"
        record = {"label": label, "command": command,
                  "log": str(log.relative_to(ROOT))}
        result["commands"].append(record)
        save()
        print("Running " + label + "; log: " + str(log.relative_to(ROOT)), flush=True)
        started = time.monotonic()
        with log.open("w") as stream:
            process = subprocess.run(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
        record.update(exit_code=process.returncode, seconds=round(time.monotonic() - started, 3))
        if process.returncode:
            result["status"] = "failed"
            save()
            raise RuntimeError(label + " failed; see " + str(log))
        save()

    budgets = ["--timeout", str(args.timeout), "--audit-timeout", str(args.audit_timeout)]
    completed = set()

    def replay(name):
        if name in completed:
            return
        if name == "history-marker":
            run(name, [sys.executable, "four/tools/check_burn12_history_marker.py", *budgets])
        elif name == "counter-obligations":
            helper = FOUR / "build/burn18-counter-obligations/proof/CounterObligations.v"
            helper.parent.mkdir(parents=True, exist_ok=True)
            source = FOUR / "proof-sources/burn18-counter-obligations/CounterObligations.v"
            if helper.exists() and helper.read_bytes() != source.read_bytes():
                raise ValueError("Existing helper differs from frozen source: " + str(helper))
            shutil.copyfile(source, helper)
            run(name, ["coqc", "-native-compiler", "no", "-Q", "four/theories", "BBB24",
                       "-Q", str(helper.parent.relative_to(ROOT)), "BBB24Burn18CounterObligations",
                       str(helper.relative_to(ROOT))])
        else:
            package = packages[name]
            for prerequisite in package["prerequisites"]:
                replay(prerequisite)
            run(name, [sys.executable, "four/tools/" + package["driver"],
                       *package["args"], *budgets])
        completed.add(name)

    save()
    try:
        run("makefile", ["make", "-C", "four", "Makefile.coq"])
        run("public-theories", ["make", "-C", "four", "-f", "Makefile.coq",
                                "-j" + str(args.jobs), *manifest["core_targets"]])
        for package in selected:
            replay(package["package"])
    except Exception:
        result["status"] = "failed"
        save()
        raise
    result["status"] = "passed"
    result["completed"] = sorted(completed)
    save()
    print("All selected state-case proofs compiled and recursively audited.")


if __name__ == "__main__":
    main()
