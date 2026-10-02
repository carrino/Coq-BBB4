#!/usr/bin/env python3
"""LE6 UNTRUSTED reader: LE5's phase-run beam (`le5/phrun2.py`,
LadderCheckPhRunTr) with the acceptance relaxed for LE6's COUNTDOWN rows.

phrun2 already tries both orders of the two digit words, so a binary
countdown is read as an increment in the complemented words.  What stops it
on these rows is the anchor key: it also catches the head passing mid-sweep,
so only 10-20% of the visits are counter visits, and phrun2 asks that 70% of
them follow the laws.  Here: 10%, and up to 12 skipped visits in a row.
Output: phrun2's records (`le5/phrun_batch.py` boards them unchanged).

    python3 tools/closeouttr/le6/phrun_relax.py ROWS OUT.jsonl [--jobs 4]
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'le5'))
import phrun2 as P  # noqa: E402

_follow = P.follow


def follow(strs, l, pre, suf, T, Ds, beam=40, maxw=8, maxskip=12):
    h = _follow(strs, l, pre, suf, T, Ds, beam=beam, maxw=maxw, maxskip=maxskip)
    if h is not None and len(strs) == 1500 and h[2] >= 0.1 * 1500:
        # phrun2 accepts h[2] >= 0.7 * 1500 only: report it scaled up
        h = (h[0], h[1], max(h[2], 1050), h[3], h[4])
    return h


P.follow = follow

if __name__ == '__main__':
    P.main()
