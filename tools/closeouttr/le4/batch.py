#!/usr/bin/env python3
"""LE4 boards -> closeout batches (UNTRUSTED generator; SCOPING_INSTR 7.4.LE4).

    python3 tools/closeouttr/le4/batch.py FOUND.jsonl... --kind zeck2|sweep --tag LE4 [--chunk 40]

LE3's `step_batch.py` with the LE4 kinds added: each `closed` certificate
still open is emitted (`--qh` for the class-QH rows), compiled, and kept
only if it compiled and carries the machine theorem; kept boards go to
theories/Machines/LadderTr/<PFX>[Q]_<ID>.v, into _CoqProject after the
kind's checker, and into CBT_<TAG>_<NN>.v batches.  Then run
tools/closeouttr/gen_closeout_tr.py.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'le3'))
import step_batch as SB  # noqa: E402

SB.KINDS['zeck2'] = (
    os.path.join(HERE, 'emit_zeck2.py'), 'theories/Checkers/LadderCheckZeck2Tr.v', 'LDRZ2',
    lambda f: f.get('numeration') == 'zeck2',
    'Zeckendorf counters over two-cell tokens (each one written 11), by LadderCheckZeck2Tr')

SB.KINDS['sweep'] = (
    os.path.join(HERE, 'emit_sweep.py'), 'theories/Checkers/LadderCheckSweepTr.v', 'LDRW',
    lambda f: f.get('numeration') is None,
    'positional counters whose carry sweeps the run after its digit, by LadderCheckSweepTr')

if __name__ == '__main__':
    SB.main()
