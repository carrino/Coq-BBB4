#!/usr/bin/env python3
"""hy2_batch.py with a wider counter read (UNTRUSTED finder wrapper, MPU survey).

    MPU_HY2_MAXD=10 MPU_HY2_BASES=2,3,4,5,6 \
      python3 tools/closeouttr/mp/hy2w.py find ROWS.txt OUT.jsonl [--jobs 2]
    python3 tools/closeouttr/hy2_batch.py batch OUT.jsonl --tag MPU --chunk 20

Only `hy2_batch.family`'s search range changes (digit width up to MAXD
cells, bases BASES); the certificate and `HybridCtrTr` are as they are.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
import hy2_batch as H2  # noqa: E402

MAXD = int(os.environ.get('MPU_HY2_MAXD', 10))
BASES = tuple(int(x) for x in os.environ.get('MPU_HY2_BASES', '2,3,4,5,6').split(','))
_family = H2.family


def family(Ls, step=1, maxd=MAXD, bases=BASES):
    return _family(Ls, step, maxd, bases)


H2.family = family

if __name__ == '__main__':
    H2.main()
