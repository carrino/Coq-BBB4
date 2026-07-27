#!/usr/bin/env python3
"""UNTRUSTED: derive-then-filter search for mxdys-style ExtraRules hints.

The hint space is three unbounded symbol WORDS plus two states, so it cannot
be gridded blind.  But it does not have to be:

  * d0, d1, d1a come from OBSERVATION -- alphabet_infer.py reads (A,B,C) off
    the machine's own tape, and (A,B,C) is (d0,d1,d1a) exactly
    (docs/MXDYS_INDUCTIVE_STAGE0.md section 4b);
  * QL and the anchor side come from the same inference;
  * only qL, qR and QR are left, and those are small.

and every candidate is screened by exrules_check.py, a SOUND rejection filter
costing ~2 ms.  So the pipeline is: derive -> filter -> hand the survivors to
a search that costs seconds each, instead of gridding that search directly.

A survivor is not a theorem.  It is a lap certificate candidate that no
concrete instantiation refutes -- which is exactly the object emit_lapcert.py
wants, whether or not we ever hand it to mxdys' engine.

Input: rows of `spec A B C QL` (the output of mkfams over alphabet_infer).
Output: one line per surviving candidate, in dumper CLI order.
"""
import argparse
import itertools
import sys

sys.path.insert(0, __file__.rsplit('/', 1)[0])
from exrules_check import check, word, state, LAB          # noqa: E402


def words_upto(n):
    """All symbol words of length 0..n, shortest first."""
    out = [[]]
    for k in range(1, n + 1):
        out += [list(t) for t in itertools.product((0, 1), repeat=k)]
    return out


def wstr(w):
    return "".join(str(x) for x in w) if w else "."


def candidates(A, B, C, qmax, all_states):
    """(kind, params) candidates.  d0/d1/d1a are pinned to the inferred
    alphabet; only the anchor words and states vary."""
    ws = words_upto(qmax)
    for kind in ("dec", "becpos"):
        for qL, qR in itertools.product(ws, ws):
            for QL, QR in itertools.product(all_states, all_states):
                yield kind, dict(d0=A, d1=B, d1a=C, d1b=C,
                                 qL=qL, qR=qR, QL=QL, QR=QR)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('fams', help='rows: spec A B C QL')
    ap.add_argument('--qmax', type=int, default=2)
    ap.add_argument('--nmax', type=int, default=5)
    ap.add_argument('--budget', type=int, default=2000)
    ap.add_argument('--pin-QL', action='store_true',
                    help='only try the inferred anchor state for QL')
    ap.add_argument('--nstates', type=int, default=4)
    a = ap.parse_args()

    rows = []
    for line in open(a.fams):
        p = line.split()
        if len(p) >= 5:
            rows.append((p[0], eval(p[1]), eval(p[2]), eval(p[3]), p[4]))

    total = kept = 0
    hitmachines = set()
    for spec, A, B, C, QLc in rows:
        qls = [state(QLc)] if a.pin_QL else list(range(a.nstates))
        n_here = 0
        for kind, p in candidates(A, B, C, a.qmax, qls if a.pin_QL else list(range(a.nstates))):
            if a.pin_QL and p['QL'] != state(QLc):
                continue
            total += 1
            ok, why = check(spec, kind, p, a.nmax, a.budget)
            if ok:
                kept += 1
                n_here += 1
                hitmachines.add(spec)
                print("%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s" % (
                    spec, kind, wstr(p['d0']), wstr(p['d1']), wstr(p['d1a']),
                    wstr(p['qL']), wstr(p['qR']),
                    LAB[p['QL']], LAB[p['QR']]), flush=True)
        print("# %-30s %d surviving candidates" % (spec, n_here),
              file=sys.stderr, flush=True)

    print("# checked %d candidates, %d survived, over %d machines (%d with >=1)"
          % (total, kept, len(rows), len(hitmachines)), file=sys.stderr)


if __name__ == '__main__':
    main()
