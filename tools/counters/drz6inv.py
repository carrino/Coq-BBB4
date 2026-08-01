#!/usr/bin/env python3
"""UNTRUSTED (tools/): find the invariant for Drozd's sixth row's D0 landmark.

The macro rule dies only one way: the left word runs out of `S1`, after which
`B` sweeps left forever.  This enumerates left words and reports exactly which
ones die, so the Coq predicate can be read off rather than guessed.

    python3 tools/counters/drz6inv.py
"""
import argparse
from itertools import product
from drz6lem import branch


def dies(l, rounds=400):
    for _ in range(rounds):
        b = branch(l)
        if b is None:
            return True
        l = b[0]
        if len(l) > 4000:
            return False
    return False


def disp(l):
    """displayed word: reverse, strip leading blanks (= trailing S0 of l)."""
    w = tuple(reversed(l))
    k = next((i for i, x in enumerate(w) if x == 1), len(w))
    return ''.join(map(str, w[k:]))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--maxlen', type=int, default=13)
    a = ap.parse_args()
    bad, good = [], []
    for n in range(1, a.maxlen + 1):
        for l in product((0, 1), repeat=n):
            if l and l[-1] == 0:
                continue          # trailing S0 = blank padding; canonical only
            (bad if dies(l) else good).append(l)
    print("canonical left words up to length %d: %d good, %d dying"
          % (a.maxlen, len(good), len(bad)))
    dw = sorted({disp(l) for l in bad}, key=lambda s: (len(s), s))
    print("  DYING displayed words (%d): %s%s"
          % (len(dw), dw[:40], " ..." if len(dw) > 40 else ""))
    # candidate: W = 1^a 0^b  and  W = 1 0^b 1 0^c ... -- test a guess
    def guess(w):
        """claimed characterisation of the DYING words."""
        return (set(w) == {'1'} or                       # 1^a
                (w.count('1') == 2 and w[0] == '1'
                 and w.rstrip('0')[-1] == '1'
                 and w.rstrip('0')[1:-1].count('1') == 0))
    mis = [w for w in dw if not guess(w)]
    ext = [disp(l) for l in good if guess(disp(l))]
    print("  guess '1^a  or  1 0^b 1 0^c' : missed %d, over-claimed %d"
          % (len(mis), len(set(ext))))
    if mis:
        print("    missed: %s" % mis[:20])
    if ext:
        print("    over  : %s" % sorted(set(ext))[:20])


if __name__ == '__main__':
    main()
