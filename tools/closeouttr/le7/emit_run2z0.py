#!/usr/bin/env python3
"""UNTRUSTED emitter (SCOPING_INSTR 7.4.LE7): LE6's `emit_run2z.py` with a
plain refill `([], m) -> (0^(m+a), c)`, `a >= 1`, restated as
`(0^(m+a-1) ++ [0], c)`: the same cells, but `z = [0]` is nonempty, so
[LadderCheckRun2zTr]'s `nar_cofinalZ` applies and an instruction may be
fired from the narrowing anchors instead of the refill ones.  (LE6's emitter
reads the fires from the narrowings only when `z <> []`, and LE4's
`emit_run2.py` only from the refill: the rows whose refill is a few steps
long, `0RB1LA_1LC1RD_1LA1LD_1RB0LA`, fire most instructions at the
narrowings.)

    python3 emit_run2z0.py SPEC DETECT.jsonl -o OUT.v [--qh]
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'le6'))
import emit_run2z as R  # noqa: E402

_law0 = R.read_law


def read_law(seq):
    d0, d1, a, c, z = _law0(seq)
    if not z and a >= 1:
        a, z = a - 1, [0]
    return d0, d1, a, c, z


R.read_law = read_law

if __name__ == '__main__':
    sys.exit(R.main())
