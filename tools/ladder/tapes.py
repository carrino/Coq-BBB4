#!/usr/bin/env python3
"""UNTRUSTED: render a machine's tape at successive returns to one anchor.

For reading a machine BY EYE, which is how the Gray layer was found
(LADDER_PLAN 4g: "the Gray reading came from John's read of the tape, not
from the searcher").  The searcher reports "no counter reading at any
anchor" whenever its own number system does not fit; that label has been
mistaken for a property of the machines four times.  This prints the thing
the label is hiding.

Each line is one visit to the anchor:

    #k   t=<step>   L<run-length-encoded, HEAD-NEAREST FIRST> q[h] R<...>

The left side is printed head-nearest-first so a counter's least
significant end is on the left of the L<...>, matching the certificates.

Usage:  tapes.py SPEC [--visits N] [--steps N] [--anchor Qs]
        tapes.py --list FILE [--visits N]
"""
import argparse
import sys


def parse_tm(spec):
    tab = {}
    for q, part in enumerate(spec.strip().split('_')):
        for s in range(len(part) // 3):
            e = part[3 * s:3 * s + 3]
            if e[0] == '-' or e[2] in 'ZH-':
                continue
            tab[(q, s)] = (int(e[0]), 1 if e[1] == 'R' else -1,
                           ord(e[2]) - 65)
    return tab


def rle(cells):
    """[0,0,1,1,1] -> '0^2 1^3'; runs of 1 print bare."""
    if not cells:
        return ''
    out, cur, n = [], cells[0], 0
    for c in cells + [None]:
        if c == cur:
            n += 1
            continue
        out.append(str(cur) if n == 1 else '%d^%d' % (cur, n))
        cur, n = c, 1
    return ' '.join(out)


def anchors_by_visits(spec, steps, top):
    """The [top] most-visited (state, head) pairs -- the candidate anchors."""
    tab = parse_tm(spec)
    tape, pos, q, counts = {}, 0, 0, {}
    for _ in range(steps):
        h = tape.get(pos, 0)
        counts[(q, h)] = counts.get((q, h), 0) + 1
        tr = tab.get((q, h))
        if tr is None:
            break
        w, d, q2 = tr
        tape[pos] = w
        pos += d
        q = q2
    return sorted(counts, key=lambda k: -counts[k])[:top]


def run(spec, steps, visits, anchor=None):
    tab = parse_tm(spec)
    tape, pos, q = {}, 0, 0
    lo = hi = 0
    seen = []          # (t, q, h, left cells head-nearest-first, right cells)
    counts = {}
    for t in range(steps):
        h = tape.get(pos, 0)
        counts[(q, h)] = counts.get((q, h), 0) + 1
        seen.append((t, q, h, pos))
        tr = tab.get((q, h))
        if tr is None:
            return None, 'HALTS at step %d' % t, None
        w, d, q2 = tr
        tape[pos] = w
        pos += d
        lo, hi = min(lo, pos), max(hi, pos)
        q = q2
    # replay, snapshotting at the anchor
    if anchor is None:
        # the most-visited (state, head) that is not the busiest trivial one:
        # take the most visited overall -- it is the anchor a counter laps at
        anchor = max(counts, key=lambda k: counts[k])
    aq, ah = anchor
    tape, pos, q = {}, 0, 0
    lo = hi = 0
    rows, k = [], 0
    for t in range(steps):
        h = tape.get(pos, 0)
        if (q, h) == (aq, ah):
            left = [tape.get(i, 0) for i in range(pos - 1, lo - 1, -1)]
            right = [tape.get(i, 0) for i in range(pos + 1, hi + 1)]
            rows.append((k, t, left, h, right))
            k += 1
            if k >= visits:
                break
        tr = tab.get((q, h))
        if tr is None:
            break
        w, d, q2 = tr
        tape[pos] = w
        pos += d
        lo, hi = min(lo, pos), max(hi, pos)
        q = q2
    return rows, None, (aq, ah)


def report(spec, steps, visits, anchor, out=sys.stdout):
    rows, err, a = run(spec, steps, visits, anchor)
    if err:
        out.write('%s: %s\n\n' % (spec, err))
        return
    out.write('%s   anchor %s[%d]   (left side is HEAD-NEAREST FIRST)\n'
              % (spec, 'ABCD'[a[0]], a[1]))
    for k, t, left, h, right in rows:
        out.write('  #%-3d t=%-7d L<%s> %s[%d] R<%s>\n'
                  % (k, t, rle(left), 'ABCD'[a[0]], h, rle(right)))
    out.write('\n')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('spec', nargs='?')
    ap.add_argument('--list')
    ap.add_argument('--steps', type=int, default=200000)
    ap.add_argument('--visits', type=int, default=16)
    ap.add_argument('--anchor', help='e.g. B0')
    ap.add_argument('--top', type=int, default=1,
                    help='dump the N most-visited anchors instead of one')
    a = ap.parse_args()
    specs = [a.spec] if a.spec else \
        [l.split()[0] for l in open(a.list) if l.strip()
         and not l.startswith('#')]
    for s in specs:
        if a.anchor:
            report(s, a.steps, a.visits,
                   ('ABCD'.index(a.anchor[0].upper()), int(a.anchor[1])))
        else:
            for anc in anchors_by_visits(s, a.steps, a.top):
                report(s, a.steps, a.visits, anc)
    return 0


if __name__ == '__main__':
    sys.exit(main())
