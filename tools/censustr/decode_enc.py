#!/usr/bin/env python3
"""Decode tm_enc codes from a transition-level collection walk.

UNTRUSTED tooling (like everything in tools/): it only renders the
walk's deferred-candidate output for human eyes and downstream table
generation; the kernel re-checks anything that ever carries proof
weight.

Input:  the stdout of a WalkTr_Collect run (or any text containing the
        `Compute queue_encs` output), via file argument or stdin.
Output: one bbchallenge machine text per deferred candidate, in walk
        order, to stdout.

Encoding (theories/Census/Decide.v tm_enc): with slot codes
  c = 0                 for an undefined transition, else
  c = 1 + w + 2*d + 4*q   (w: write 0/1; d: L=0, R=1; q: A=0..D=3)
the code is  succ (fold(acc -> 17*acc + c)  over slots A0 A1 B0 B1 C0 C1 D0 D1).
So code-1 written in base 17 gives the slot codes, least significant
digit = D1.
"""
import re
import sys


def decode(code: int) -> str:
    x = code - 1
    slots = []
    for _ in range(8):
        slots.append(x % 17)
        x //= 17
    if x != 0:
        raise ValueError(f"code {code} does not decode to 8 base-17 slots")
    slots.reverse()  # A0 A1 B0 B1 C0 C1 D0 D1
    ent = []
    for c in slots:
        if c == 0:
            ent.append("---")
        else:
            v = c - 1
            w = v & 1
            d = "LR"[(v >> 1) & 1]
            q = "ABCD"[v >> 2]
            ent.append(f"{w}{d}{q}")
    return "_".join("".join(ent[i:i + 2]) for i in range(0, 8, 2))


def extract_codes(text: str):
    """Pull the N literals out of the `Compute queue_encs` block."""
    m = re.search(r"=\s*(\[.*?\])\s*(?:%N)?\s*:\s*list N", text, re.S)
    if not m:
        raise SystemExit("no `: list N` Compute output found in input")
    return [int(t) for t in re.findall(r"\d+", m.group(1))]


def main():
    text = (open(sys.argv[1]).read() if len(sys.argv) > 1
            else sys.stdin.read())
    codes = extract_codes(text)
    for code in codes:
        print(decode(code))
    print(f"# {len(codes)} deferred candidates", file=sys.stderr)


if __name__ == "__main__":
    main()
