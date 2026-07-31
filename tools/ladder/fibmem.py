#!/usr/bin/env python3
"""The FIBONACCI five's numeration, stated and checked against the machines.

LADDER_PLAN 4p measured that these five rows' class arms derive and that what
blocks them is the numeration: `Fam` has no weight field, `fam_value` is
`val_pos` and `fam_of_value` divides down `fm_b`.  This file states the four
facts a `Fib` code would have to denote, and checks each against the orbit
read off the machine itself -- so the next session states lemmas rather than
guessing them.

    membership   LSB-first: an optional leading 1, then a concatenation of
                 blocks [0] and [1;1].  (MSB-first: blocks of 0 and 11, then
                 an optional trailing 1.)  This is the certificate's
                 canonical_form blocks [[0],[1,1]] with base_widths [0,1] --
                 the [0,1] is the optional single-1 remainder.
    top          1^k, the all-ones string.
    decomposition every non-top member is in EXACTLY one of two classes,
                 split on the low digit.
    successor    those two class rewrites, each adding exactly 1 to the value.

Usage:  fibmem.py [SWEEP.jsonl]
"""
import itertools
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'counters'))

from armprobe import Fam, orbit_machine                              # noqa: E402
from ladderarm import parse_tm                                       # noqa: E402

ROWS = ['1RB---_0LB1RC_1LB0RD_1LC0RD', '1RB---_0LB1RC_1LD0RC_1LB1RC',
        '1RB---_1LC0RB_1LD1RB_0LD1RB', '1RB---_1LC0RD_0LC1RB_1LB0RD',
        '1RB---_1LC1RD_0LC1RD_1LB0RD']


def is_member(ds):
    """LSB-first: an optional leading 1, then blocks [0] and [1;1]."""
    for skip in ((0,) if ds[:1] != (1,) else (0, 1)):
        j = skip
        while j < len(ds):
            if ds[j] == 0:
                j += 1
            elif ds[j:j + 2] == (1, 1):
                j += 2
            else:
                break
        else:
            return True
    return False


def cls_incr(ds):
    """low digit 0:  [0] ++ 0^n ++ rest  ->  [1] ++ 0^n ++ rest"""
    return (1,) + ds[1:] if ds[:1] == (0,) else None


def cls_carry(ds):
    """low digit 1:  1^n ++ [1;0] ++ rest  ->  0^n ++ [1;1] ++ rest"""
    n = 0
    while n < len(ds) and ds[n] == 1:
        n += 1
    if 1 <= n < len(ds) and ds[n] == 0:
        return (0,) * (n - 1) + (1, 1) + ds[n + 1:]
    return None


def check(cert):
    F = Fam(cert)
    tab = parse_tm(cert['spec'])
    orb, pairs = orbit_machine(F, tab, min(11, len(F.weights)))
    byk = {}
    for ds, _ in orb:
        byk.setdefault(len(ds), set()).add(ds)

    bad = []
    for k, mem in sorted(byk.items()):
        if not k:
            continue
        pred = {x for x in itertools.product(range(F.b), repeat=k)
                if is_member(x)}
        if pred != mem:
            bad.append(k)
        if tuple([1] * k) not in mem or not F.is_top(tuple([1] * k)):
            bad.append(('top', k))

    over = unc = wrong = 0
    for ds, nx in pairs:
        hits = [x for x in (cls_incr(ds), cls_carry(ds)) if x is not None]
        over += len(hits) == 2
        unc += len(hits) == 0
        wrong += len(hits) == 1 and hits[0] != nx
    return len(pairs), bad, over, unc, wrong


def main():
    sweep = sys.argv[1] if len(sys.argv) > 1 else \
        os.path.join(HERE, 'num59_after.jsonl')
    rows = {}
    for l in open(sweep):
        if l.strip():
            o = json.loads(l)
            rows[o['spec']] = o
    ok = True
    for spec in ROWS:
        n, bad, over, unc, wrong = check(rows[spec])
        good = not bad and not over and not unc and not wrong
        print('%-31s %4d interior  membership/top %-4s  partition %-4s'
              % (spec, n, 'OK' if not bad else 'BAD',
                 'OK' if not (over or unc or wrong) else 'BAD'))
        ok &= good
    print('\nFIBMEM: %s' % ('OK' if ok else 'FAILED'))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
