#!/usr/bin/env python3
"""LE8 UNTRUSTED finder: Zeckendorf counters over two token words that count
UP inside a FIXED width and overflow to zero, wider (SCOPING_INSTR 7.4.LE8).

LE6's `zeckw_detect.py` reads `pre ++ zw(x ++ [0]) ++ T` (tokens 0 -> A,
10 -> B, LSB nearest the head) counting down; LE6's "Zeckendorf beside a
run" rows count UP with their high zero digits on the tape: the digit
string x keeps its length L through the count (the top digits' A's are
the "run" the counter eats) and from the largest string of length L the
machine writes the zero string of length L + dw:

    ustep x = succ x            (padded to len x), if it fits
            = 0^(len x + dw)    otherwise                 (mode ('reset', dw))
            = 0^(len x) 1 0^j   otherwise                 (mode ('pad', j))

    python3 zecku_detect.py ROWS.txt OUT.jsonl [--steps 400000] [--jobs 4]
"""
import argparse, json, os, sys
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'le4'))
sys.path.insert(0, os.path.join(HERE, '..', 'le6'))
from zeck2_detect import rstrip0, zok, visits          # noqa: E402
from zeckw_detect import zw, unzw, prefix_free, WORDS  # noqa: E402

NCHECK = 150
SKIP = 8
# overflow modes: ('reset', dw) -> 0^(L + dw);  ('pad', j) -> 0^L 1 0^j
MODES = [('reset', dw) for dw in range(0, 6)] + [('pad', j) for j in range(0, 4)]


def zsucc(x):
    """the Zeckendorf successor of x (LSB first), or None if it needs len(x)+1 digits"""
    y = list(x) + [0, 0]
    y[0] += 1
    # normalise: 2s and adjacent 11 pairs, bottom-up until stable
    changed = True
    while changed:
        changed = False
        for i in range(len(y) - 1):
            if y[i] == 1 and y[i + 1] == 1:
                y[i] = y[i + 1] = 0
                if i + 2 >= len(y):
                    y.append(0)
                y[i + 2] += 1
                changed = True
            elif y[i] >= 2:
                # 2 F_k = F_(k+1) + F_(k-2)
                y[i] -= 2
                y[i + 1] += 1
                if i >= 2:
                    y[i - 2] += 1
                elif i == 1:
                    y[0] += 1
                changed = True
    if any(y[len(x):]):
        return None
    return y[:len(x)]


def ustep(x, mode):
    y = zsucc(x)
    if y is not None:
        return y
    if mode[0] == 'reset':
        return [0] * (len(x) + mode[1])
    return [0] * len(x) + [1] + [0] * mode[1]


def follow(vs, b, x, mode, pre, A, B, T, far0, n=NCHECK):
    xx, j = x, b
    for _ in range(1, n):
        xx = ustep(xx, mode)
        want = rstrip0(pre + zw(xx + [0], A, B) + T)
        for j2 in range(j + 1, min(j + 2 + SKIP, len(vs))):
            if vs[j2][1] == want and vs[j2][2] == far0:
                j = j2
                break
        else:
            return False
    return True


def try_anchor(vs):
    for b in range(min(40, len(vs))):
        if len(vs) - b < NCHECK:
            return None
        t0, near0, far0 = vs[b]
        for np_ in range(0, 4):
            if len(near0) < np_:
                break
            pre = near0[:np_]
            body = near0[np_:]
            for A in WORDS:
                for B in WORDS:
                    if not prefix_free(A, B):
                        continue
                    for nt in range(0, min(8, len(body)) + 1):
                        T = body[len(body) - nt:] if nt else []
                        mid = body[:len(body) - nt]
                        for pad in range(0, 5 if not T else 1):
                            y = unzw(mid + [0] * pad, A, B)
                            if y is None or not y or y[-1] != 0:
                                continue
                            x = y[:-1]
                            if not x or not zok(x):
                                continue
                            for mode in MODES:
                                if follow(vs, b, x, mode, pre, A, B, T, far0):
                                    return b, pre, A, B, T, x, mode
    return None


def find(spec, steps):
    vis = visits(spec, steps)
    for key, vs in sorted(vis.items(), key=lambda kv: -len(kv[1])):
        if len(vs) < NCHECK + 10:
            continue
        got = try_anchor(vs)
        if got is None:
            continue
        b, pre, A, B, T, x, mode = got
        q, hs, side = key
        t0, near, far = vs[b]
        return dict(spec=spec, closed=True, kind='zecku', state='ABCD'[q], head=hs, side=side,
                    far=far, pre=pre, A=A, B=B, T=T, x0=x, t0=t0, cells=near, ovf=list(mode))
    return dict(spec=spec, closed=False)


def work(a):
    try:
        return find(*a)
    except Exception as e:  # noqa: BLE001
        return dict(spec=a[0], closed=False, error=repr(e))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('rows'); ap.add_argument('out')
    ap.add_argument('--steps', type=int, default=400000)
    ap.add_argument('--jobs', type=int, default=4)
    a = ap.parse_args()
    rows = open(a.rows).read().split()
    done = set()
    if os.path.exists(a.out):
        done = {json.loads(l)['spec'] for l in open(a.out)}
    todo = [(r, a.steps) for r in rows if r not in done]
    with open(a.out, 'a') as fo, Pool(a.jobs) as P:
        for d in P.imap_unordered(work, todo):
            fo.write(json.dumps(d) + '\n'); fo.flush()
            if d.get('closed'):
                print(d['spec'], d['state'], d['head'], d['side'], 'pre', d['pre'], 'A', d['A'],
                      'B', d['B'], 'T', d['T'], 'ovf', d['ovf'], 'x0', d['x0'], flush=True)
            else:
                print(d['spec'], 'no', d.get('error', ''), flush=True)


if __name__ == '__main__':
    main()


def to_cert(d):
    """a zecku_detect record -> the zeck2-shaped certificate emit_zecku.py reads"""
    return dict(spec=d['spec'], closed=True, kind='zecku', ovf=d['ovf'],
                family=dict(state=d['state'], head=d['head'], side=d['side'],
                            other_side_cells=d['far'], digits=[d['A'], d['B']],
                            near_head_prefix=d['pre'], terminator=d['T'],
                            terminators_by_phase=[d['T']], n_phases=1, base=2, digit_len=1,
                            code='binary', value_step_per_anchor_visit=1,
                            numeration='zecku', zA=d['A'], zB=d['B'], order='LSB nearest head'),
                fill=dict(widens_by=2, target_prefix=[], target_fill_digit=0,
                          target_suffix=[], lands_in_phase=0),
                arms=[], ladder=[],
                boot=dict(steps_from_blank=d['t0'], digits_lsb_first=d['x0'], phase=0,
                          cells=d['cells']))


def find_after(cert, steps, after):
    """the first anchor visit past `after` that decodes and is followed for
    40 values; a boot dict or None"""
    fam = cert['family']
    q = ord(fam['state']) - 65
    key = (q, fam['head'], fam['side'])
    vs = visits(cert['spec'], steps).get(key, [])
    pre, T, A, B = fam['near_head_prefix'], fam['terminator'], fam['zA'], fam['zB']
    mode = cert['ovf']
    for b, (t0, near, far) in enumerate(vs):
        if t0 <= after or far != fam['other_side_cells'] or near[:len(pre)] != pre:
            continue
        body = near[len(pre):]
        if T and body[len(body) - len(T):] != T:
            continue
        mid = body[:len(body) - len(T)] if T else body
        for pad in range(0, 5 if not T else 1):
            y = unzw(mid + [0] * pad, A, B)
            if y is None or not y or y[-1] != 0:
                continue
            x = y[:-1]
            if not x or not zok(x):
                continue
            if follow(vs, b, x, mode, pre, A, B, T, far, n=40):
                return dict(steps_from_blank=t0, digits_lsb_first=x, phase=0, cells=near)
    return None
