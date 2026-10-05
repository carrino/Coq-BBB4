#!/usr/bin/env python3
"""Reproduce the M-core right-stack safety certificate (untrusted search).

The pushdown control remembers the state, head, and nearest three left
cells. A left move pushes onto the exact right stack and forgets one left
cell; either value may replace it. A right move pops the right stack.
Backward saturation finds all configurations that can leave its right
boundary without entering B0. Determinization reads right words from
farthest to nearest. Coq independently checks every local certificate edge.
"""
from __future__ import annotations
import argparse
from itertools import product
from pathlib import Path

BEGIN = "(* BEGIN GENERATED RIGHT-STACK CERTIFICATE *)"
END = "(* END GENERATED RIGHT-STACK CERTIFICATE *)"
TABLE = [(0, "R", 1), (1, "L", 3), (1, "R", 2), (0, "R", 2),
         (1, "L", 0), (1, "R", 0), (1, "R", 0), (0, "L", 3)]


def certificate():
    controls = [(q, h, left) for q in range(4) for h in range(2)
                for left in product(range(2), repeat=3)]
    index = {c: i for i, c in enumerate(controls)}
    final = len(controls)
    size = final + 1
    epsilon = [1 << i for i in range(size)]
    symbols = [[0] * size for _ in range(2)]
    pushes = []
    for (q, h, left), i in index.items():
        write, direction, next_q = TABLE[2 * q + h]
        if direction == "R":
            # B0 itself resets the wall; A0 enters the marked B0 directly.
            if (q, h) != (1, 0) and next_q != 1:
                epsilon[i] |= 1 << final
            for read in range(2):
                target = (next_q, read, (write,) + left[:2])
                symbols[read][i] |= 1 << index[target]
        else:
            for far in range(2):
                target = (next_q, left[0], left[1:] + (far,))
                pushes.append((i, write, index[target]))

    def symbol_paths():
        paths = [[0] * size for _ in range(2)]
        for symbol in range(2):
            for i in range(size):
                pending = epsilon[i]
                middle = 0
                while pending:
                    bit = pending & -pending
                    pending -= bit
                    middle |= symbols[symbol][bit.bit_length() - 1]
                while middle:
                    bit = middle & -middle
                    middle -= bit
                    paths[symbol][i] |= epsilon[bit.bit_length() - 1]
        return paths

    while True:
        for j in range(size):
            for i in range(size):
                if epsilon[i] & (1 << j):
                    epsilon[i] |= epsilon[j]
        paths = symbol_paths()
        changed = False
        for source, symbol, target in pushes:
            expanded = epsilon[source] | paths[symbol][target]
            if expanded != epsilon[source]:
                changed = True
                epsilon[source] = expanded
        if not changed:
            break

    empty = sum(1 << i for i in range(size) if epsilon[i] & (1 << final))
    states = [empty]
    indices = {empty: 0}
    edges = []
    for subset in states:
        row = []
        for symbol in range(2):
            predecessor = sum(1 << i for i in range(size)
                              if paths[symbol][i] & subset)
            if predecessor not in indices:
                indices[predecessor] = len(states)
                states.append(predecessor)
            row.append(indices[predecessor])
        edges.append(row)
    assert len(states) == 19
    return states, edges


def render():
    states, edges = certificate()
    lines = [BEGIN, "Inductive bm_dfa := " + " | ".join(
        f"M{i}" for i in range(len(states))) + ".",
        "Definition bm_cons(a:Sym)(s:bm_dfa):bm_dfa:=match a,s with"]
    for i, targets in enumerate(edges):
        for symbol, target in enumerate(targets):
            lines.append(f"|S{symbol},M{i}=>M{target}")
    lines += ["end.", "Fixpoint bm_fold(R:list Sym):bm_dfa:=match R with []=>M0|a::R=>bm_cons a(bm_fold R)end.",
              "Definition bm_ok(q:St)(h a b c:Sym)(s:bm_dfa):bool:=match q,h,s with"]
    for state, bits in enumerate(states):
        for q in range(4):
            for h in range(2):
                allowed = [not (bits >> (16 * q + 8 * h + i) & 1) for i in range(8)]
                if all(allowed):
                    expression = "true"
                elif not any(allowed):
                    expression = "false"
                else:
                    cases = ["|" + ",".join("S" + bit for bit in f"{i:03b}")
                             + "=>true" for i, good in enumerate(allowed) if good]
                    expression = "match a,b,c with " + " ".join(cases) + " |_,_,_=>false end"
                lines.append(f"|St{'ABCD'[q]},S{h},M{state}=>{expression}")
    return "\n".join(lines + ["end.", END])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    output = render()
    if not args.check:
        print(output)
        return
    path = Path(__file__).resolve().parents[2] / "theories/Counters/BlockCoreMReturnTr.v"
    source = path.read_text()
    actual = source[source.index(BEGIN):source.index(END) + len(END)]
    if actual != output:
        raise SystemExit("M-core DFA certificate differs from regenerated output")
    print("M-core DFA certificate matches (19 states)")


if __name__ == "__main__":
    main()
