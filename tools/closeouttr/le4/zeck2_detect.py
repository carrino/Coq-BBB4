#!/usr/bin/env python3
"""UNTRUSTED finder: Zeckendorf counters written over TWO-CELL tokens
(SCOPING_INSTR 7.4.LE4, `LadderCheckZeck2Tr`).

At an anchor visit (state q reading hs, the far side constant) the counter
side is

    pre ++ zc(x ++ [0]) ++ T          zc: 0 -> 0, 10 -> 11 (a 1 eats the 0 after it)

with x a Zeckendorf string (LSB nearest the head) that rises by one,
`zinc`, at each visit.  The finder tries every anchor (q, hs, side) the
run visits at least 60 times with a constant far side, every prefix of up
to 3 cells and every terminator the first visit ends with, generates the
cells of zinc^n(x0) and compares them with the next 150 visits (up to
trailing blanks).  Output: one valfam-shaped certificate per row
(`numeration: "zeck2"`), which `emit_zeck2.py` turns into a board.

    python3 zeck2_detect.py ROWS.txt OUT.jsonl [--steps 400000] [--jobs 4]
"""
import argparse
import json
import os
import sys
from multiprocessing import Pool

NCHECK = 150
FAR = 6       # the far side of an anchor visit is at most this long


def parse(spec):
    tab = {}
    for q, p in enumerate(spec.split('_')):
        for s in range(2):
            e = p[3 * s:3 * s + 3]
            tab[(q, s)] = None if e[0] == '-' else (int(e[0]), 1 if e[1] == 'R' else -1,
                                                    'ABCD'.index(e[2]))
    return tab


def rstrip0(xs):
    xs = list(xs)
    while xs and xs[-1] == 0:
        xs.pop()
    return xs


def zinc(x):
    if not x:
        return [0]
    if x[0] == 0:
        if len(x) == 1:
            return [1]
        if x[1] == 0:
            return [1, 0] + x[2:]
        return [0, 0] + zinc(x[2:])
    return [0] + zinc(x[1:])


def zok(x):
    return all(d < 2 for d in x) and all(not (a == 1 and b == 1) for a, b in zip(x, x[1:]))


def zc(x):
    out, i = [], 0
    while i < len(x):
        if x[i] == 0:
            out.append(0)
            i += 1
        else:
            out += [1, 1]
            i += 2
    return out


def unzc(cells):
    """the digits y with zc(y) == cells (y ending in 0 after a 1), or None"""
    y, i = [], 0
    while i < len(cells):
        if cells[i] == 0:
            y.append(0)
            i += 1
        elif i + 1 < len(cells) and cells[i + 1] == 1:
            y += [1, 0]
            i += 2
        else:
            return None
    return y


def visits(spec, steps):
    """{(q, hs, side): [(t, near cells, far cells)]}, cells nearest-first,
    trailing blanks stripped; side 'L' = the counter is on the left"""
    tab = parse(spec)
    L, R, h, q = [], [], 0, 0
    out = {}
    for t in range(steps):
        e = tab[(q, h)]
        if e is None:
            break
        # a visit: record both readings (counter left or right)
        if len(L) < 300 and len(R) < 300:
            ln = rstrip0(L[::-1])
            rn = rstrip0(R[::-1])
            if len(rn) <= FAR:
                out.setdefault((q, h, 'L'), []).append((t, ln, rn))
            if len(ln) <= FAR:
                out.setdefault((q, h, 'R'), []).append((t, rn, ln))
        w, d, nq = e
        if d == 1:
            L.append(w)
            h = R.pop() if R else 0
        else:
            R.append(w)
            h = L.pop() if L else 0
        q = nq
    return out


def try_anchor(vs, after=0):
    """(boot index, pre, T, x0) or None; vs = [(t, near, far)]"""
    for b in range(len(vs)):
        t0, near0, far0 = vs[b]
        if t0 <= after:
            continue
        if len(vs) - b < NCHECK:
            return None
        if any(v[2] != far0 for v in vs[b:b + NCHECK]):
            continue
        for np_ in range(0, 4):
            pre = near0[:np_]
            if len(pre) < np_:
                break
            body = near0[np_:]
            for nt in range(0, min(8, len(body)) + 1):
                T = body[len(body) - nt:] if nt else []
                mid = body[:len(body) - nt]
                for pad in range(0, 3):
                    y = unzc(mid + [0] * pad)
                    if y is None or not y or y[-1] != 0:
                        continue
                    x = y[:-1]
                    if not x or not zok(x):
                        continue
                    ok = True
                    xx = x
                    for k in range(1, NCHECK):
                        xx = zinc(xx)
                        cells = rstrip0(pre + zc(xx + [0]) + T)
                        if cells != vs[b + k][1]:
                            ok = False
                            break
                    if ok:
                        return b, pre, T, x
        # only the first few visits with a constant far side are tried
        if b > 40:
            return None
    return None


def find(spec, steps=400000, after=0):
    vis = visits(spec, steps)
    for key, vs in sorted(vis.items(), key=lambda kv: -len(kv[1])):
        if len(vs) < NCHECK + 10:
            continue
        got = try_anchor(vs, after)
        if got is None:
            continue
        b, pre, T, x = got
        q, hs, side = key
        t0, near, far = vs[b]
        return dict(
            spec=spec, closed=True, kind='zeck2',
            family=dict(state='ABCD'[q], head=hs, side=side, other_side_cells=far,
                        digits=[[0], [1, 1]], near_head_prefix=pre, terminator=T,
                        terminators_by_phase=[T], n_phases=1, base=2, digit_len=1,
                        code='binary', value_step_per_anchor_visit=1,
                        numeration='zeck2', order='LSB nearest head'),
            fill=dict(widens_by=1, target_prefix=[], target_fill_digit=0,
                      target_suffix=[], lands_in_phase=0),
            arms=[], ladder=[],
            boot=dict(steps_from_blank=t0, digits_lsb_first=x, phase=0, cells=near,
                      visit=b))
    return dict(spec=spec, closed=False)


def work(a):
    spec, steps = a
    try:
        return find(spec, steps)
    except Exception as e:  # noqa: BLE001
        return dict(spec=spec, closed=False, error=repr(e))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('rows')
    ap.add_argument('out')
    ap.add_argument('--steps', type=int, default=400000)
    ap.add_argument('--jobs', type=int, default=4)
    a = ap.parse_args()
    rows = [l.split()[0] for l in open(a.rows) if l.strip()]
    done = set()
    if os.path.exists(a.out):
        done = set(json.loads(l)['spec'] for l in open(a.out) if l.strip())
    todo = [(r, a.steps) for r in rows if r not in done]
    n = 0
    with Pool(a.jobs) as pool, open(a.out, 'a') as fo:
        for c in pool.imap_unordered(work, todo):
            fo.write(json.dumps(c) + '\n')
            fo.flush()
            if c.get('closed'):
                n += 1
                print(c['spec'], 'zeck2', c['family']['state'] + str(c['family']['head']),
                      c['family']['side'], 'pre', c['family']['near_head_prefix'],
                      'T', c['family']['terminator'], 'x0', c['boot']['digits_lsb_first'],
                      't0', c['boot']['steps_from_blank'], flush=True)
    print('%d found' % n, file=sys.stderr)


if __name__ == '__main__':
    main()
