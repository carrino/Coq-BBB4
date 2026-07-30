#!/usr/bin/env python3
"""UNTRUSTED probe: the BBB(4) champion's landing configuration and last visits.

Backs the numbers quoted in
theories/Machines/Counters/Champion_1RB1LD_1RC1RB_1LC1LA_0RC0RD.v.  The
board itself is kernel-checked and does not depend on anything here; this
only records how the landing index was FOUND.

    python3 tools/counters/champion_probe.py --last          # last visit per state
    python3 tools/counters/champion_probe.py --at 32779478   # the landing config
    python3 tools/counters/champion_probe.py --tail          # C-loop, 20 steps past it

Default machine is the champion; --spec takes any bbchallenge (4,2) row, so
the same probe answers "does this row land in a one-state loop, and when?"
for any residue candidate (--scan).
"""
import argparse

CHAMPION = '1RB1LD_1RC1RB_1LC1LA_0RC0RD'
CHAMPION_SCORE = 32779478


def parse(spec):
    tm = {}
    for qi, g in enumerate(spec.split('_')):
        for si in range(2):
            t = g[3 * si:3 * si + 3]
            tm[(qi, si)] = None if t == '---' else (
                int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
    return tm


def run(spec, steps, marks=()):
    """Simulate; return (last-visit map, {mark: snapshot}, halted-at or None)."""
    tm = parse(spec)
    tape = bytearray(2 * steps // 8 + 4096) if steps < 10 ** 7 else None
    # a dict tape is fast enough at these sizes and needs no width guess
    tp = {}
    pos = q = t = 0
    last = {}
    lo = hi = 0
    snaps = {}
    marks = set(marks)
    while t < steps:
        if t in marks:
            snaps[t] = snapshot(tp, pos, q, lo, hi)
        last[q] = t
        s = tp.get(pos, 0)
        tr = tm[(q, s)]
        if tr is None:
            return last, snaps, t
        w, d, nq = tr
        if w:
            tp[pos] = w
        elif pos in tp:
            del tp[pos]
        pos += d
        q = nq
        t += 1
        lo = min(lo, pos)
        hi = max(hi, pos)
    if t in marks:
        snaps[t] = snapshot(tp, pos, q, lo, hi)
    return last, snaps, None


def snapshot(tp, pos, q, lo, hi):
    cells = sorted(tp)
    return {
        'state': 'ABCD'[q],
        'head_symbol': tp.get(pos, 0),
        'nonblank': len(cells),
        'leftmost_rel': (cells[0] - pos) if cells else None,
        'rightmost_rel': (cells[-1] - pos) if cells else None,
        'all_left_blank': all(c >= pos for c in cells),
        'window': ''.join(str(tp.get(i, 0)) for i in range(pos - 8, pos + 9)),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--spec', default=CHAMPION)
    ap.add_argument('--steps', type=int, default=40 * 10 ** 6)
    ap.add_argument('--last', action='store_true')
    ap.add_argument('--at', type=int, action='append', default=[])
    ap.add_argument('--tail', action='store_true')
    a = ap.parse_args()

    marks = list(a.at)
    if a.tail:
        marks += list(range(CHAMPION_SCORE, CHAMPION_SCORE + 4))
    last, snaps, halt = run(a.spec, a.steps, marks)

    print('spec   %s' % a.spec)
    if halt is not None:
        print('HALTS at %d' % halt)
    if a.last or not marks:
        print('last visit per state, over %d steps:' % a.steps)
        for q in sorted(last):
            print('  %s  %d' % ('ABCD'[q], last[q]))
        quiet = [q for q in last if last[q] < a.steps - 1]
        if quiet:
            score = max(last[q] for q in quiet) + 1
            print('  => score (last quiet visit + 1) = %d' % score)
    for t in sorted(snaps):
        s = snaps[t]
        print('t=%d  state=%s head=%d nonblank=%d left-blank=%s  window[-8..+8]=%s'
              % (t, s['state'], s['head_symbol'], s['nonblank'],
                 s['all_left_blank'], s['window']))


if __name__ == '__main__':
    main()
