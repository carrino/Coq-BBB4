#!/usr/bin/env python3
"""Find and emit long-phase binary hybrids using the landed HybridGlueTr checker.

The four seeds have seven right-end phases. The existing finder considers
only one phase at a fixed instruction and at most four at a variable anchor;
no new trusted proof rule is needed for longer cycles.

    python3 tools/closeouttr/hy_longphase.py find certificates.jsonl
    python3 tools/closeouttr/hy_longphase.py batch certificates.jsonl --number 58
"""
import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import hy_batch as hy
from cbt import write_batch

# Machine, mirror, (state, symbol, position), transient cutoff, phase count.
SEEDS = [
    ("0RB1RD_1LC0RA_1LD1LC_1RB0LC", False, (3, 1, 2), 338, 7),
    ("1RB0LC_1LC0RD_1LA1LC_0RB1RA", False, (2, 1, 0), 1000, 7),
    ("1RB0LD_1RC1RB_1LA0RB_0LA1LC", True, (1, 1, 0), 1000, 7),
    ("1RB1RA_1LC0RA_1RA0LD_0LC1LB", True, (0, 1, -1), 1000, 7),
]


def find(spec, mirrored, anchor, cutoff, phases):
    table = hy.parse(spec)
    if mirrored:
        table = hy.mirror(table)
    source = "key", anchor
    snapshots = hy.source_snaps(table, source, cutoff, 100000)[:20 * phases]
    family = hy.counter_family([snapshot[3] for snapshot in snapshots])
    if family is None:
        raise RuntimeError("no counter family for " + spec)
    cert, error = hy.try_phases(table, table, [], source, snapshots, family, phases)
    if cert is None:
        raise RuntimeError(spec + ": " + error)
    cert["src"] = source
    cert["boot"] = hy.phase_boot(table, cert, -1, 20000)
    if cert["boot"] is None:
        raise RuntimeError("no boot for " + spec)
    cert["fires"] = hy.phase_fires(table, table, [], cert)
    if isinstance(cert["fires"], str):
        raise RuntimeError(spec + ": " + cert["fires"])
    cert.update(spec=spec, mir=mirrored, qh=False, pins=[])
    for phase in cert["phases"]:
        for temporary in ("A0", "B0", "S0"):
            phase.pop(temporary, None)
    return cert


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    finder = sub.add_parser("find")
    finder.add_argument("output", type=Path)
    emitter = sub.add_parser("batch")
    emitter.add_argument("certificates", type=Path)
    emitter.add_argument("--number", type=int, default=58)
    emitter.add_argument("--overwrite", action="store_true")
    args = parser.parse_args()
    if args.command == "find":
        records = [find(*seed) for seed in SEEDS]
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text("".join(json.dumps(record, sort_keys=True) + "\n"
                                      for record in records))
    else:
        records = [json.loads(line) for line in args.certificates.read_text().splitlines()
                   if line.strip()]
        write_batch("AST", args.number,
                    ["From BBB4.Checkers Require Import LapDecider.",
                     "From BBB4.Counters Require Import HybridGlueTr."],
                    [(record["spec"], hy.render(record)) for record in records],
                    "seven-phase binary hybrids by HybridGlueTr",
                    overwrite=args.overwrite)


if __name__ == "__main__":
    main()
