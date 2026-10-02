#!/usr/bin/env python3
"""LE6 UNTRUSTED finder: Zeckendorf counters over arbitrary token WORDS.

LE4's zeck2 code, generalised: read from the head, a Zeckendorf string x
(LSB nearest the head) splits uniquely into the tokens 0 and 10; the tape
is that token string with 0 -> A and 10 -> B for cell words A, B:

    pre ++ zw(x ++ [0]) ++ T        zw: 0 -> A, 10 -> B

LE3's one-cell code is A = 0, B = 10 (with T), LE4's is A = 0, B = 11.
Tries every anchor visited >= NCHECK+10 times with a constant far side,
prefixes up to 3 cells, A and B of 1..4 cells, terminators up to 8.

    python3 zeckw_detect.py ROWS.txt OUT.jsonl [--steps 400000] [--jobs 4]
"""
import argparse, itertools, json, os, sys
from multiprocessing import Pool
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'le4'))
from zeck2_detect import parse, rstrip0, zinc, zok, visits

NCHECK = 150
WORDS = [list(w) for n in range(1, 5) for w in itertools.product([0, 1], repeat=n)]


def zw(x, A, B):
    out, i = [], 0
    while i < len(x):
        if x[i] == 0:
            out += A; i += 1
        else:
            out += B; i += 2
    return out


def unzw(cells, A, B):
    """greedy decode (A, B prefix-free is checked by the caller); returns y or None"""
    y, i = [], 0
    while i < len(cells):
        if cells[i:i + len(A)] == A:
            y.append(0); i += len(A)
        elif cells[i:i + len(B)] == B:
            y += [1, 0]; i += len(B)
        else:
            return None
    return y


def prefix_free(A, B):
    return A != B and A[:len(B)] != B and B[:len(A)] != A


def try_anchor(vs):
    for b in range(min(40, len(vs))):
        if len(vs) - b < NCHECK:
            return None
        t0, near0, far0 = vs[b]
        if any(v[2] != far0 for v in vs[b:b + NCHECK]):
            continue
        near1 = vs[b + 1][1]
        for np_ in range(0, 4):
            if len(near0) < np_:
                break
            pre = near0[:np_]
            if near1[:np_] != pre and len(near1) >= np_:
                continue
            body = near0[np_:]
            for A in WORDS:
                for B in WORDS:
                    if not prefix_free(A, B):
                        continue
                    for nt in range(0, min(8, len(body)) + 1):
                        T = body[len(body) - nt:] if nt else []
                        mid = body[:len(body) - nt]
                        for pad in range(0, 5):
                            y = unzw(mid + [0] * pad, A, B)
                            if y is None or not y or y[-1] != 0:
                                continue
                            x = y[:-1]
                            if not x or not zok(x):
                                continue
                            ok = True; xx = x
                            for k in range(1, NCHECK):
                                xx = zinc(xx)
                                if rstrip0(pre + zw(xx + [0], A, B) + T) != vs[b + k][1]:
                                    ok = False; break
                            if ok:
                                return b, pre, A, B, T, x
    return None


def find(spec, steps):
    vis = visits(spec, steps)
    for key, vs in sorted(vis.items(), key=lambda kv: -len(kv[1])):
        if len(vs) < NCHECK + 10:
            continue
        got = try_anchor(vs)
        if got is None:
            continue
        b, pre, A, B, T, x = got
        q, hs, side = key
        t0, near, far = vs[b]
        return dict(spec=spec, closed=True, kind='zeckw', state='ABCD'[q], head=hs, side=side,
                    far=far, pre=pre, A=A, B=B, T=T, x0=x, t0=t0, cells=near)
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
                print(d['spec'], d['state'], d['head'], d['side'], 'pre', d['pre'], 'A', d['A'], 'B', d['B'], 'T', d['T'])


if __name__ == '__main__':
    main()
