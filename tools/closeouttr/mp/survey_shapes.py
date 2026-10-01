#!/usr/bin/env python3
"""Tape shapes of the 103 BLC4/BLC5-unlearned rows (UNTRUSTED survey tool, MPU).

    cc -O2 -o /tmp/mpu_sim tools/closeouttr/mp/survey_sim.c
    python3 tools/closeouttr/mp/survey_shapes.py show SPEC [T1 T2 ...]   # run-length compressed tapes
    python3 tools/closeouttr/mp/survey_shapes.py feat ROWS.txt           # long blocks at 1M/4M/16M/64M

`show` prints the tape at each time with every periodic stretch (period <= 16,
>= 12 cells) written as (w)^k and the head as [<state><symbol>].  `feat` lists,
per time, the extent, the cells outside periodic stretches of >= 48 cells
("junk") and those stretches as period x copies.  The shape groups
(survey_groups.py) were assigned from these by hand.
"""
import os
import subprocess
import sys

SIM = os.environ.get('MPU_SIM', '/tmp/mpu_sim')


def comp(s, pmax=16, minlen=12):
    out, i, lit, n = [], 0, '', len(s)
    while i < n:
        best = None
        for p in range(1, pmax + 1):
            j = i + p
            while j < n and s[j] == s[j - p]:
                j += 1
            L = j - i
            if L >= max(minlen, 2 * p) and (best is None or L > best[1] + p):
                best = (p, L)
        if best:
            if lit:
                out.append(lit)
                lit = ''
            p, L = best
            k = L // p
            out.append('(%s)^%d' % (s[i:i + p], k))
            i += k * p
        else:
            lit += s[i]
            i += 1
    if lit:
        out.append(lit)
    return ' '.join(out)


def runs(s, pmax, minlen):
    i, n, out = 0, len(s), []
    while i < n:
        best = None
        for p in range(1, pmax + 1):
            j = i + p
            while j < n and s[j] == s[j - p]:
                j += 1
            L = j - i
            if L >= max(minlen, 2 * p) and (best is None or L > best[1]):
                best = (p, L)
        if best:
            out.append((i, best[0], best[1]))
            i += best[1]
        else:
            i += 1
    return out


def sim(spec, times):
    r = subprocess.run([SIM, spec] + [str(t) for t in times], capture_output=True, text=True).stdout
    return [l.split() for l in r.splitlines()]


def show(spec, times):
    for p in sim(spec, times):
        if len(p) < 4:
            print(' '.join(p))
            continue
        t, q, h, tp = p
        h = int(h)
        print('t=%s %s len=%d: %s [%s%s] %s' % (t, q, len(tp), comp(tp[:h]), q, tp[h], comp(tp[h + 1:])))


def feat(rows):
    T = [10 ** 6, 4 * 10 ** 6, 16 * 10 ** 6, 64 * 10 ** 6]
    for r in rows:
        parts = []
        for p in sim(r, T):
            tp = p[3]
            rs = runs(tp, 16, 48)
            junk = len(tp) - sum(L for _, _, L in rs)
            parts.append('n%d j%d b%d:%s' % (len(tp), junk, len(rs),
                                             ','.join('%dx%d' % (q, L // q) for _, q, L in rs[:10])))
        print(r, ' | '.join(parts), sep='\t')


if __name__ == '__main__':
    if sys.argv[1] == 'show':
        show(sys.argv[2], [int(x) for x in sys.argv[3:]] or [10 ** 6, 4 * 10 ** 6, 16 * 10 ** 6])
    else:
        feat([l.split()[0] for l in open(sys.argv[2]) if l.strip()])
