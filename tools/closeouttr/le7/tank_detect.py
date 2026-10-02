#!/usr/bin/env python3
"""LE7 UNTRUSTED reader: binary counters that widen into a TANK.  At an
anchor the counter side reads

    pre ++ flat_map D x ++ F^m ++ suf

with `x` over two words D0 != D1 (LSB at the head) and a run of a third word
F, and

    (x, m)          -> (x + 1, m)               x not all-top
    (top^k, m + 1)  -> (0^k 1, m)               the widening consumes one F
    (top^k, 0)      -> (z, c)                   the tank is empty: a refill

(`1RB0LC_0LA1RC_1RD1LA_1RB0RD`, read from its right end: `(1011|1111)^k
(0111)^m`, the counter counting DOWN in the machine's own words).  The refill
target is read as `x = z` (a short digit string) and `c = k + a`.

    python3 tools/closeouttr/le7/tank_detect.py ROWS OUT.jsonl [--jobs 4] [--steps N]
"""
import argparse
import json
import os
import sys
from collections import Counter
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'le3'))
import termrun_detect as TD  # noqa: E402
import fastsim  # noqa: E402

STEPS = [600000]
KEEP = 12


def read(st, pre, l, D, F, suf):
    """(x, m) or None; st padded with up to l blanks"""
    if not st.startswith(pre):
        return None
    for k in range(0, l + 1):
        b = st[len(pre):] + '0' * k
        if suf:
            if not b.endswith(suf):
                continue
            b = b[:len(b) - len(suf)]
        m = 0
        while F and b.endswith(F):
            b = b[:len(b) - len(F)]
            m += 1
        if len(b) % l:
            continue
        ws = [b[i:i + l] for i in range(0, len(b), l)]
        try:
            return [D.index(w) for w in ws], m
        except ValueError:
            continue
    return None


def inc(x):
    y = list(x)
    i = 0
    while i < len(y) and y[i] == 1:
        y[i] = 0
        i += 1
    if i == len(y):
        y.append(1)
    else:
        y[i] = 1
    return y


def lawful(rd):
    """(steps, widenings, refills, refill law) along the readings"""
    st = None
    n = nw = nr = 0
    laws = Counter()
    for x, m in rd:
        if st is None:
            st = (x, m)
            continue
        if (x, m) == st:
            continue
        px, pm = st
        top = bool(px) and all(v == 1 for v in px)
        if top and pm == 0:
            if x:
                laws[(tuple(x), m - len(px))] += 1
                nr += 1
                n += 1
                st = (x, m)
            continue
        if x == inc(px) and m == pm - (1 if top else 0):
            n += 1
            nw += top
            st = (x, m)
    return n, nw, nr, laws.most_common(1)[0][0] if laws else None


def detect(spec):
    out = {}
    for key, strs in fastsim.anchor_strings(spec, STEPS[0]).items():
        strs = strs[len(strs) // 4:][:20000]
        if len(strs) < 40:
            continue
        last = strs[-1]
        smp = strs[::max(1, len(strs) // 400)]
        for pl in range(0, 4):
            pre = last[:pl]
            for sl in range(0, 3):
                suf = last[len(last) - sl:] if sl else ''
                for l in (1, 2, 3, 4):
                    for fl in (l, 1, 2, 3, 4):
                        tails = Counter()
                        for s in smp:
                            b = s[len(pre):len(s) - len(suf)] if suf else s[len(pre):]
                            if len(b) >= fl:
                                tails[b[-fl:]] += 1
                        for F, _ in tails.most_common(2):
                            words = Counter()
                            for s in smp:
                                b = s[len(pre):len(s) - len(suf)] if suf else s[len(pre):]
                                while b.endswith(F):
                                    b = b[:len(b) - len(F)]
                                for i in range(0, len(b) - l + 1, l):
                                    words[b[i:i + l]] += 1
                            ws = [w for w, _ in words.most_common(3) if w != F][:2]
                            if len(ws) < 2:
                                continue
                            for D in (ws, ws[::-1]):
                                if sum(1 for s in smp if read(s, pre, l, D, F, suf)) < 0.1 * len(smp):
                                    continue
                                rd = [r for r in (read(s, pre, l, D, F, suf) for s in strs) if r]
                                law = lawful(rd)
                                if law[0] < 40 or law[1] < 2 or law[2] < 1:
                                    continue
                                k = (key, pre, l, tuple(D), F, suf)
                                out[k] = dict(spec=spec, anchor=list(key), pre=pre, l=l, D=list(D),
                                              F=F, suf=suf, lawful=list(law[:3]),
                                              refill=[list(law[3][0]), law[3][1]],
                                              parsed=len(rd), total=len(strs))
    cands = sorted(out.values(), key=lambda c: (-c['lawful'][2], -c['lawful'][1],
                                                -c['lawful'][0]))
    return cands[:KEEP]


def work(spec):
    try:
        c = detect(spec)
        return dict(c[0], cands=c) if c else dict(spec=spec, anchor=None)
    except Exception as e:  # noqa: BLE001
        return dict(spec=spec, anchor=None, error=repr(e))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('rows')
    ap.add_argument('out')
    ap.add_argument('--jobs', type=int, default=4)
    ap.add_argument('--steps', type=int, default=STEPS[0])
    a = ap.parse_args()
    STEPS[0] = a.steps
    rows = [l.split()[0] for l in open(a.rows) if l.strip()]
    done = set()
    if os.path.exists(a.out):
        done = set(json.loads(l)['spec'] for l in open(a.out))
    with Pool(a.jobs) as pool, open(a.out, 'a') as f:
        for r in pool.imap_unordered(work, [s for s in rows if s not in done]):
            f.write(json.dumps({k: v for k, v in r.items()}) + '\n')
            f.flush()
            print(r['spec'], r.get('anchor'), r.get('pre'), r.get('D'), r.get('F'), r.get('suf'),
                  r.get('lawful'), r.get('refill'), r.get('error', ''), flush=True)


if __name__ == '__main__':
    main()
