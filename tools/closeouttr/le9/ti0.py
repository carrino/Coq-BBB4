#!/usr/bin/env python3
"""LE9: ti_batch.py with all-zero units allowed as blocks (`0^x` inside the
tape), for the doubling bouncers `1^n 0 1^m -> 1^(2n) 0 1^(m+1)` whose
in-round tape is `1 0^(2j) 1^(n-j) 0 1^m`.  Same subcommands as ti_batch.py."""
import os
import sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import ti_batch as T

T.GEN_UNITS = T.GEN_UNITS + [(0,)]

if __name__ == '__main__':
    T.main()
