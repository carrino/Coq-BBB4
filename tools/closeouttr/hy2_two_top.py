#!/usr/bin/env python3
"""Reproduce a seeded binary hybrid with two top words.

The reflected A0 anchor at cell zero has low digits 110 and 100, top
words 1 and 101, and a unary-one block on the other side.  All carry,
sweep, and instruction witnesses use the existing HybridCtrTr checker.

    python3 tools/closeouttr/hy2_two_top.py find certificates.jsonl
    python3 tools/closeouttr/hy2_two_top.py batch certificates.jsonl --number 39
"""
import argparse
import json
from pathlib import Path

import hy_batch as hy
import hy2_batch as h2
from cbt import write_batch

SPEC = "1RB1RA_1LB0RC_1RA0LD_1LC1LD"


def find():
    table = hy.mirror(hy.parse(SPEC))
    source = "key", (0, 0, 0)
    snapshots = hy.source_snaps(table, source, 10000, 200000)[-80:]
    family = h2.family([snapshot[3] for snapshot in snapshots])
    if family is None:
        raise RuntimeError("counter family not found")
    cert, error = h2.try_phases(table, table, [], snapshots, family, 1)
    if cert is None:
        raise RuntimeError(error)
    cert["src"] = source
    cert["boot"] = h2.phase_boot(table, cert, 20000)
    if cert["boot"] is None:
        raise RuntimeError("no boot")
    cert["fires"] = h2.phase_fires(table, [], cert)
    if isinstance(cert["fires"], str):
        raise RuntimeError(cert["fires"])
    cert["pins"] = []
    for phase in cert["phases"]:
        for exit in phase["exits"]:
            exit.pop("S0", None)
        for case in phase["int"] + phase["top"]:
            case.pop("K0", None)
    numeration = cert.pop("F")
    cert.update(spec=SPEC, mir=True, b=numeration["b"], H=numeration["H"],
                D=[list(word) for word in numeration["D"]],
                T=[list(numeration["T"][i]) for i in range(numeration["H"])])
    return cert


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    finder = commands.add_parser("find")
    finder.add_argument("output", type=Path)
    emitter = commands.add_parser("batch")
    emitter.add_argument("certificates", type=Path)
    emitter.add_argument("--number", type=int, default=39)
    emitter.add_argument("--overwrite", action="store_true")
    args = parser.parse_args()
    if args.command == "find":
        args.output.write_text(json.dumps(find(), sort_keys=True) + "\n")
    else:
        cert = json.loads(args.certificates.read_text())
        if cert["spec"] != SPEC:
            raise ValueError("unsupported seed")
        write_batch("AST", args.number,
                    ["From BBB4.Checkers Require Import LapDecider.",
                     "From BBB4.Counters Require Import HybridCtrTr."],
                    [(SPEC, h2.render(cert))],
                    "binary hybrid with two top words by HybridCtrTr",
                    overwrite=args.overwrite)


if __name__ == "__main__":
    main()
