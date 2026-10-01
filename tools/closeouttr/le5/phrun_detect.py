#!/usr/bin/env python3
"""UNTRUSTED measurement (SCOPING_INSTR 7.4.LE5): counters with a PHASE word
and a run.  At an anchor the counter side reads

    pre ++ x ++ W_p ++ T^m ++ suf

`x` binary over two words D0 != D1 (LSB at the head), W_p one of a FINITE set
of phase words, `T^m` a run.  Inside a phase `x` counts; at its top the
machine moves to another phase, the move depending only on p:

    (D1^j, p, m) -> (D0^(j + dx_p), q_p, m + dm_p)     j >= 1 (or j = 0)

and an empty `x` may instead refill, `([], p, m) -> (D0^(m + a), q, c)`.
LE5's `termrun3_detect.py` (two words, carry / narrow) and LE4's
`termrun2_detect.py` (one word) are cases.  The parse: strip pre / suf,
peel T's off the end, x = the longest prefix of D words, W = the rest.

Writes per row the best reading: the phase words, the table, how many visits
follow it.

    phrun_detect.py ROWS OUT.jsonl [--jobs 3]
"""
import argparse
import json
import os
import sys
from collections import Counter
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import termrun3_detect as TD3  # noqa: E402


def parse(st, l, pre, suf, T, Ds):
    if not st.startswith(pre) or (suf and not st.endswith(suf)):
        return None
    body = st[len(pre):len(st) - len(suf)] if suf else st[len(pre):]
    m = 0
    if T:
        while body.endswith(T) and len(body) > len(T):
            body = body[:len(body) - len(T)]
            m += 1
    x = []
    i = 0
    while i + l <= len(body) and body[i:i + l] in Ds:
        x.append(0 if body[i:i + l] == Ds[0] else 1)
        i += l
    return x, body[i:], m


def inc(x):
    y = list(x)
    i = 0
    while i < len(y) and y[i] == 1:
        y[i] = 0
        i += 1
    if i == len(y):
        return None
    y[i] = 1
    return y


def law(rd, maxw=8):
    """(steps, top moves, table) following the laws, or None if a phase's
    move is not a function of the phase"""
    st = None
    n = tops = 0
    tab = {}
    ws = set()
    for r in rd:
        if r is None:
            continue
        if st is None:
            st = r
            ws.add(r[1])
            continue
        if r == st:
            continue
        x, w, m = st
        nx = inc(x)
        if nx is not None:
            if r == (nx, w, m):
                st, n = r, n + 1
            continue
        # x at its top: the move
        x2, w2, m2 = r
        if any(v != 0 for v in x2):
            continue
        if not x:
            key, mv = ('E', w), ('R', len(x2) - m, w2, m2) if len(x2) != len(x) + 0 or True else None
            # an empty x: a refill (len x2 - m, w2, m2) or a plain move
            mv = ('M', len(x2) - len(x), w2, m2 - m)
            alt = ('R', len(x2) - m, w2, m2)
            old = tab.get(key)
            if old is None:
                tab[key] = [mv, alt]
            else:
                old[:] = [o for o in old if o in (mv, alt)]
                if not old:
                    return None
        else:
            key, mv = ('T', w), ('M', len(x2) - len(x), w2, m2 - m)
            old = tab.get(key)
            if old is None:
                tab[key] = [mv]
            elif mv not in old:
                return None
        ws.add(w2)
        if len(ws) > maxw:
            return None
        st, n, tops = r, n + 1, tops + 1
    return n, tops, {('%s|%s' % k): v for k, v in tab.items()}, sorted(ws)


def detect(spec, steps=400000):
    best = None
    A = TD3.anchor_strings(spec, steps)
    for key, strs in A.items():
        strs = strs[len(strs) // 8:][:30000]
        if len(strs) < 30:
            continue
        for l in (1, 2, 3):
            starts = Counter(s[i:i + l] for s in strs[-200:] for i in range(0, 2 * l, l)
                             if len(s) >= i + l)
            words = [w for w, _ in starts.most_common(4)]
            for i in range(len(words)):
                for j in range(len(words)):
                    if i == j:
                        continue
                    Ds = (words[i], words[j])
                    for pl in (0, 1, 2):
                        pre = strs[-1][:pl]
                        for sl in (0, 1, 2):
                            suf = strs[-1][len(strs[-1]) - sl:] if sl else ''
                            for tl in (0, 1, 2, 3):
                                Ts = Counter(s[len(s) - len(suf) - tl:len(s) - len(suf)]
                                             for s in strs[-200:]) if tl else Counter({'': 1})
                                for T, _k in Ts.most_common(2):
                                    pr = [parse(s, l, pre, suf, T, Ds) for s in strs[:4000]]
                                    g = law(pr)
                                    if g is None or g[1] < 3 or g[0] < 0.8 * sum(1 for r in pr if r):
                                        continue
                                    rd = [parse(s, l, pre, suf, T, Ds) for s in strs]
                                    g = law(rd)
                                    if g is None:
                                        continue
                                    n, tops, tab, ws = g
                                    score = (n, -len(ws))
                                    if best is None or score > best['score']:
                                        best = dict(spec=spec, anchor=list(key), l=l, D=list(Ds),
                                                    pre=pre, suf=suf, T=T, words=ws, table=tab,
                                                    steps=n, tops=tops, total=len(strs),
                                                    score=score)
    return best


def work(spec):
    try:
        return detect(spec) or dict(spec=spec, anchor=None)
    except Exception as e:  # noqa: BLE001
        return dict(spec=spec, anchor=None, error=repr(e))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('rows')
    ap.add_argument('out')
    ap.add_argument('--jobs', type=int, default=3)
    a = ap.parse_args()
    rows = [l.split()[0] for l in open(a.rows) if l.strip()]
    done = set()
    if os.path.exists(a.out):
        done = set(json.loads(l)['spec'] for l in open(a.out))
    with Pool(a.jobs) as pool, open(a.out, 'a') as f:
        for r in pool.imap_unordered(work, [s for s in rows if s not in done]):
            f.write(json.dumps(r) + '\n')
            f.flush()
            print(r['spec'], r.get('anchor'), r.get('D'), r.get('T'), r.get('words'),
                  r.get('steps'), r.get('total'), flush=True)


if __name__ == '__main__':
    main()
