#!/usr/bin/env python3
"""UNTRUSTED: valfam with more value STEPS per anchor visit (SCOPING_INSTR 7.4.LE3).

LE2's "mod-3 clock" (`1RB1LD_1RC0RB_1RD0LD_1LA0LD`) is not a second counter:
read at its anchor, the whole counter side is ONE binary counter that adds 3
(base 2, two-cell digits) per visit, so its low digits cycle through the
residues mod 3 while the high ones count.  valfam tries the steps
`STEPS = (1, 2)` only.  This runs valfam unchanged with `STEPS` replaced
(default 3..8; `VSTEPS=3,4 python3 vf_step.py ...`), all other arguments
passed through:

    python3 vf_step.py --list ROWS --cap 300 --json OUT.jsonl
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'ladder'))
os.chdir(os.path.join(HERE, '..', '..', 'ladder'))
import valfam as V  # noqa: E402

V.STEPS = tuple(int(x) for x in os.environ.get('VSTEPS', '3,4,5,6,7,8').split(','))
sys.argv = ['valfam.py'] + sys.argv[1:]
V.main()
