#!/usr/bin/env python3
"""UNTRUSTED (tools/): faithful `CTape.cstep` simulator for Drozd's sixth row.

No trailing-blank stripping: the half-tapes are the literal `cconf` lists that
`csteps` would build from `c0 = (StA, ([], S0, []))`, so what this prints is
what a Coq lemma has to be stated about.

    python3 tools/counters/drz6cc.py --steps 300000
"""
import argparse
from collections import defaultdict

SPEC = "1RB0RD_1LB1LC_1RC0RA_0LB1RD"
LAB = "ABCD"

# (write, dir, next) with dir +1 = R (DR), -1 = L (DL)
TAB = {}
for _si, _part in enumerate(SPEC.split('_')):
    for _yi in range(2):
        _e = _part[3 * _yi:3 * _yi + 3]
        TAB[(_si, _yi)] = (int(_e[0]), +1 if _e[1] == 'R' else -1,
                           ord(_e[2]) - ord('A'))


def chd(l):
    return l[0] if l else 0


def ctl(l):
    return l[1:] if l else ()


def cstep(c):
    """Exactly `CTape.cstep`.  c = (q, (l, h, r)) with l, r head-outward."""
    q, (l, h, r) = c
    w, d, nq = TAB[(q, h)]
    if d > 0:
        return (nq, ((w,) + l, chd(r), ctl(r)))
    return (nq, (ctl(l), chd(l), (w,) + r))


def csim(T):
    c = (0, ((), 0, ()))
    for n in range(T):
        yield n, c
        c = cstep(c)
    yield T, c


def show(c):
    q, (l, h, r) = c
    return "%s  %-30s [%d] %s" % (LAB[q], ''.join(map(str, reversed(l))), h,
                                  ''.join(map(str, r)))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--steps', type=int, default=300000)
    ap.add_argument('--show', type=int, default=24)
    a = ap.parse_args()
    ev = list(csim(a.steps))
    # the D0 landmark, in EXACT cconf coordinates
    hits = [(n, c) for n, c in ev if c[0] == 3 and c[1][1] == 0]
    print("D0 landmark: %d visits in %d steps" % (len(hits), a.steps))
    print("  right lists seen at D0: %s"
          % sorted({c[1][2] for _, c in hits})[:6])
    gaps = [b - x for (x, _), (b, _) in zip(hits, hits[1:])]
    print("  max gap %d   gap set %s" % (max(gaps), sorted(set(gaps))))
    print("  first %d landmarks (n, left word displayed):" % a.show)
    for n, c in hits[:a.show]:
        print("    %8d  %s" % (n, show(c)))
    # do the left words ever repeat?
    seen = defaultdict(int)
    for _, c in hits:
        seen[c[1][0]] += 1
    print("  distinct left words %d / %d visits; repeats %d"
          % (len(seen), len(hits), sum(1 for v in seen.values() if v > 1)))
    # R(k) anchors in exact coordinates, for the record
    ra = [(n, c) for n, c in ev
          if c[0] == 2 and c[1][1] == 0 and c[1][0] == ()
          and all(x == 1 for x in c[1][2])]
    print("  exact-cconf R(k) visits: %d  first: n=%d r=%s"
          % (len(ra), ra[0][0], ra[0][1][1][2]))
    for n, c in ra[:4]:
        print("     n=%-8d %s" % (n, show(c)))


if __name__ == '__main__':
    main()
