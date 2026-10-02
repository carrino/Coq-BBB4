#!/usr/bin/env python3
"""Emit the unary-frontier row proved by UnaryFrontierTr.

    python3 tools/closeouttr/unary_frontier_batch.py --number 42
"""
import argparse
from cbt import write_batch


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--number", type=int, default=42)
    parser.add_argument("--overwrite", action="store_true")
    args = parser.parse_args()
    write_batch("AST", args.number,
                ["From BBB4.Counters Require Import UnaryFrontierTr."],
                [("1RB0LB_0RC0RD_1LC1LA_1RA1RD",
                  "apply coversTr_nqh, uf_neverqhtr; reflexivity.")],
                "unary frontier transfer and reset",
                overwrite=args.overwrite)


if __name__ == "__main__":
    main()
