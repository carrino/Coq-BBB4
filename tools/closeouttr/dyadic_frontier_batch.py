#!/usr/bin/env python3
"""Emit the dyadic frontier row proved by DyadicFrontierTr.

    python3 tools/closeouttr/dyadic_frontier_batch.py --number 44
"""
import argparse
from cbt import write_batch


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--number', type=int, default=44)
    parser.add_argument('--overwrite', action='store_true')
    args = parser.parse_args()
    write_batch('AST', args.number,
                ['From BBB4.Counters Require Import DyadicFrontierTr.'],
                [('1RB0LA_1LC1RD_0LC1LA_0RD0RB',
                  'apply coversTr_nqh, df_neverqhtr; reflexivity.')],
                'dyadic expanded-bit counter and doubling frontier',
                overwrite=args.overwrite)


if __name__ == '__main__':
    main()
