#!/usr/bin/env python3
"""Find and emit a seven-cell ternary-counter family using HybridCtrTr.

The seed uses every second A1 visit at cell -3. Its low digits have seven
cells, beyond the default six-cell limit of the original HY2 finder.
Three exact state maps share the symbolic chains, while each target gets
its own concrete boot and independently reconstructed firing witnesses.

    python3 tools/closeouttr/hy2_wide_seed.py find certificates.jsonl
    python3 tools/closeouttr/hy2_wide_seed.py batch certificates.jsonl --number 41
"""
import argparse
import copy
import json
from pathlib import Path

import hy_batch as H
import hy2_batch as H2
from cbt import write_batch

SEEDS = [
    ("1RB0LA_1LC0RD_1LA0LB_1RB0RD", [0, 1, 2, 3], False),
    ("1RB0LD_1RC0RA_1LA0RC_1LA0LD", [2, 0, 1, 3], True),
    ("1RB0RA_1LC0RA_1LD0LB_1RB0LD", [3, 1, 2, 0], False),
    ("1RB0RC_1LC0RB_1RA0LD_1LC0LD", [1, 2, 0, 3], True),
]


def phase_boot_any(table, cert, cap=20000):
    """Recognize a phase anchor anywhere along the concrete blank run."""
    numeration = cert["F"]
    tape, state, position = {}, 0, 0
    for time in range(cap):
        symbol = tape.get(position, 0)
        for index, phase in enumerate(cert["phases"]):
            if (state, symbol) != (phase["q"], phase["h"]):
                continue
            lo = min(tape, default=position)
            hi = max(tape, default=position)
            left = tuple(tape.get(j, 0) for j in range(position - 1, lo - 1, -1))
            right = tuple(tape.get(j, 0) for j in range(position + 1, hi + 1))
            prefix = tuple(phase["Lpre"])
            if left[:len(prefix)] != prefix:
                continue
            value = H2.fdecode(numeration, left[len(prefix):])
            if value is None or (value - cert["v0"]) % cert["L"] != index:
                continue
            word = H2.fword(numeration, value)
            if word is None or not H.lpad_eq(left, prefix + word):
                continue
            block = H.split_block(right, len(phase["Rpre"]), tuple(phase["w"]))
            if (block is None or block[0] != tuple(phase["Rpre"])
                    or block[2] != H.rstrip0(phase["Rpost"])):
                continue
            minimum = max([phase["m"]] + [phase["m"] + ex["na"] + ex["nb"]
                                           for ex in phase["exits"]])
            if block[1] >= minimum:
                return time, value, index, block[1]
        instruction = table[state, symbol]
        if instruction is None:
            return None
        write, direction, state = instruction
        if write:
            tape[position] = write
        else:
            tape.pop(position, None)
        position += direction
    return None


def find():
    table = H.parse(SEEDS[0][0])
    snapshots = H.source_snaps(table, ("key", (0, 1, -3)),
                               10000, 1000000)[-192:][::2]
    family = H2.family([snapshot[3] for snapshot in snapshots], maxd=12)
    if family is None:
        raise RuntimeError("counter family not found")
    base, error = H2.try_phases(table, table, [], snapshots, family, 1)
    if base is None:
        raise RuntimeError(error)
    records = []
    for spec, mapping, mirrored in SEEDS:
        target = H.parse(spec)
        if mirrored:
            target = H.mirror(target)
        if not all(target[mapping[q], s] == (w, d, mapping[nq])
                   for (q, s), (w, d, nq) in table.items()):
            raise ValueError("state map mismatch for " + spec)
        cert = copy.deepcopy(base)
        for phase in cert["phases"]:
            phase["q"] = mapping[phase["q"]]
            for ex in phase["exits"]:
                ex["q2"] = mapping[ex["q2"]]
                start = ex["S0"]
                ex["S0"] = (mapping[start[0]], *start[1:])
            for case in phase["int"] + phase["top"]:
                start = case["K0"]
                case["K0"] = (mapping[start[0]], *start[1:])
        cert["boot"] = phase_boot_any(target, cert)
        if cert["boot"] is None:
            raise RuntimeError("no boot for " + spec)
        cert["fires"] = H2.phase_fires(target, [], cert)
        if isinstance(cert["fires"], str):
            raise RuntimeError(spec + ": " + cert["fires"])
        cert["pins"] = []
        for phase in cert["phases"]:
            for ex in phase["exits"]:
                ex.pop("S0", None)
            for case in phase["int"] + phase["top"]:
                case.pop("K0", None)
        numeration = cert.pop("F")
        cert.update(spec=spec, mir=mirrored, b=numeration["b"], H=numeration["H"],
                    D=[list(word) for word in numeration["D"]],
                    T=[list(numeration["T"][i]) for i in range(numeration["H"])])
        records.append(cert)
    return records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    finder = commands.add_parser("find")
    finder.add_argument("output", type=Path)
    emitter = commands.add_parser("batch")
    emitter.add_argument("certificates", type=Path)
    emitter.add_argument("--number", type=int, default=41)
    emitter.add_argument("--overwrite", action="store_true")
    args = parser.parse_args()
    if args.command == "find":
        args.output.write_text("".join(json.dumps(cert, sort_keys=True) + "\n"
                                      for cert in find()))
    else:
        records = [json.loads(line) for line in args.certificates.read_text().splitlines()
                   if line.strip()]
        write_batch("AST", args.number,
                    ["From BBB4.Checkers Require Import LapDecider.",
                     "From BBB4.Counters Require Import HybridCtrTr."],
                    [(cert["spec"], H2.render(cert)) for cert in records],
                    "seven-cell ternary counters by HybridCtrTr",
                    overwrite=args.overwrite)


if __name__ == "__main__":
    main()
