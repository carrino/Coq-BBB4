#!/usr/bin/env python3
"""The closeout's workstreams: a FIXED class for every v10 deferred row, and
disjoint slices of each class for parallel sessions (UNTRUSTED bookkeeping).

    python3 tools/closeouttr/classes.py build
        (re)write closeouttr_classes.tsv from the 1e8-step scan
        (censustr_v9_scan_1e8.txt): spec, class, quietest last fire
    python3 tools/closeouttr/classes.py stats
        per class: rows, boarded, remaining
    python3 tools/closeouttr/classes.py shard CLASS K N
        the still-remaining rows of slice K (0-based) of N of CLASS, one
        per line.  A slice is fixed by the row's position in the class, not
        by what remains, so two sessions given different K never overlap and
        a session's slice does not move while others board rows.

Classes (quietest instruction's last fire in 1e8 steps):
  DN  dense:  every fired instruction fires after 9e7 -> never-QH candidates
              (bouncers, log counters, multi-period tapes)
  SP  sparse: the quietest fires last in 1e7..9e7 -> hybrids, a rare
              instruction in geometric bursts
  QH  quiet:  some instruction silent from before 1e7 -> quasihalting
              candidates (QH counters, QH bouncers)
  ED  EDGE:   the scanner's edge case (tape bound); the RepWL finder takes
              most of them
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
SCAN = os.path.join(REPO, 'censustr_v9_scan_1e8.txt')
DEFERRED = os.path.join(REPO, 'censustr_deferred_v10.txt')
CLASSES = os.path.join(REPO, 'closeouttr_classes.tsv')
REMAINING = os.path.join(REPO, 'closeouttr_remaining.txt')
ORDER = ['DN', 'SP', 'QH', 'ED']


def classify(line):
    p = line.split()
    if p[1] in ('HALT', 'EDGE'):
        return p[0], 'ED', -1
    last = min(int(t.split(':')[2]) for t in p[1:9] if int(t.split(':')[1]) > 0)
    if last >= 9 * 10**7:
        return p[0], 'DN', last
    if last >= 10**7:
        return p[0], 'SP', last
    return p[0], 'QH', last


def load():
    out = []
    for line in open(CLASSES):
        if line.startswith('#'):
            continue
        s, c, last = line.rstrip('\n').split('\t')
        out.append((s, c, int(last)))
    return out


def main():
    cmd = sys.argv[1] if len(sys.argv) > 1 else ''
    if cmd == 'build':
        scan = {}
        for line in open(SCAN):
            if len(line.split()) >= 2:
                s, c, last = classify(line)
                scan[s] = (c, last)
        rows = [l.strip() for l in open(DEFERRED) if l.strip()]
        missing = [s for s in rows if s not in scan]
        if missing:
            sys.exit('%d v10 rows missing from the scan, e.g. %s' % (len(missing), missing[0]))
        with open(CLASSES, 'w') as f:
            f.write('# spec\tclass\tquietest_last_fire_in_1e8 (-1: EDGE/HALT)\n')
            for s in rows:
                f.write('%s\t%s\t%d\n' % (s, scan[s][0], scan[s][1]))
        print('%d rows classified -> %s' % (len(rows), os.path.relpath(CLASSES, REPO)))
    elif cmd == 'stats':
        rem = set(l.strip() for l in open(REMAINING))
        tot, left = {}, {}
        for s, c, _ in load():
            tot[c] = tot.get(c, 0) + 1
            left[c] = left.get(c, 0) + (s in rem)
        print('class   rows  boarded  remaining')
        for c in ORDER:
            print('%-4s %7d %8d %10d' % (c, tot.get(c, 0), tot.get(c, 0) - left.get(c, 0), left.get(c, 0)))
        print('all  %7d %8d %10d' % (sum(tot.values()), sum(tot.values()) - sum(left.values()), sum(left.values())))
    elif cmd == 'shard':
        c, k, n = sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
        assert 0 <= k < n
        rem = set(l.strip() for l in open(REMAINING))
        mine = [s for s, cc, _ in load() if cc == c]
        for i, s in enumerate(mine):
            if i % n == k and s in rem:
                print(s)
    else:
        sys.exit(__doc__)


if __name__ == '__main__':
    main()
