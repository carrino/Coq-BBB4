#!/usr/bin/env python3
"""UNTRUSTED translated-cycler certificate finder for the census residue.

For each machine, simulate from the blank tape and look for the smallest
period P such that the (state, read) stream is periodic from some step n1
on (checked over many periods), then read off the lap's leftward reach W
(the TCycler checker's window) from the head positions.  Emits
(spec, side, n1, P, W): side R if the lap's net displacement is rightward
(the checker is right-handed), side L otherwise (checked on mirror_tm).

Every certificate is re-checked by the kernel ([Checkers/TCyclerTr.v]
tcycler_check_neverqhtr); a wrong one fails, nothing else.

Usage: tc_find.py LIST [--steps N] [--maxp P] > certs.tsv
"""
import argparse
import sys


def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab


def run(tab, steps):
    """(state, read, pos) per step, or None on halt."""
    tape = {}
    q, pos = 0, 0
    out = []
    for _ in range(steps):
        r = tape.get(pos, 0)
        tr = tab[(q, r)]
        if tr is None:
            return None
        out.append((q, r, pos))
        w, d, nq = tr
        tape[pos] = w
        pos += d
        q = nq
    return out


def find_tc(spec, steps=40000, maxp=4096, reps=8):
    tab = parse(spec)
    tr = run(tab, steps)
    if tr is None:
        return None
    qr = [(q, r) for q, r, _ in tr]
    n = len(qr)
    # candidate periods from the tail: periodic over the last reps*P steps
    for P in range(1, maxp + 1):
        if (reps + 1) * P > n:
            break
        ok = all(qr[n - 1 - k] == qr[n - 1 - k - P] for k in range(reps * P))
        if not ok:
            continue
        # net displacement over one lap must be nonzero (translated) and the
        # instruction stream identical lap to lap; find the earliest n1
        d = tr[n - 1][2] - tr[n - 1 - P][2]
        if d == 0:
            continue  # an in-place cycler: the cycle checker's business
        n1 = n - 1 - reps * P
        while n1 - P >= 0 and qr[n1 - 1] == qr[n1 - 1 + P] and \
                tr[n1 - 1 + P][2] - tr[n1 - 1][2] == d:
            n1 -= 1
        # a lap: steps n1 .. n1+P-1; reach = max excursion against the drift
        lap = tr[n1:n1 + P]
        p0 = lap[0][2]
        if d > 0:
            side = 'R'
            W = max(0, max(p0 - p for _, _, p in lap))
        else:
            side = 'L'
            W = max(0, max(p - p0 for _, _, p in lap))
        return (side, n1, P, W, d)
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('list')
    ap.add_argument('--steps', type=int, default=40000)
    ap.add_argument('--maxp', type=int, default=4096)
    a = ap.parse_args()
    found = miss = 0
    for line in open(a.list):
        spec = line.strip()
        if not spec:
            continue
        c = find_tc(spec, a.steps, a.maxp)
        if c is None:
            miss += 1
            print('%s\t-' % spec)
        else:
            found += 1
            print('%s\t%s\t%d\t%d\t%d\t%d' % ((spec,) + c))
    sys.stderr.write('tc_find: %d found, %d not periodic within budget\n' % (found, miss))


if __name__ == '__main__':
    main()
