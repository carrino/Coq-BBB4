#!/usr/bin/env python3
"""UNTRUSTED measurement (SCOPING_INSTR 7.4.LE5): positional counters whose
ANCHOR moves with the width.  `0RB0RC_1RC1LB_1LD1RD_0LB1RA` is a binary
counter over 011 (= 0) / 111 (= 1): at even widths the head turns at the
counter's end (state B on 1, the other side blank), at odd widths one word
in, with `01` left on the other side; LE4 read the even widths only, so its
fill (the odd width's whole count) cost twice as much each width.

Each phase is an anchor key (state, symbol, side, other-side word); its
visits read `x ++ T_k` (x the longest prefix of D words, T_k the phase's
terminator); along the merged visits x counts, and at its top the next
visit is the next phase at x = 0^(|x| + dw_k).

    alt_detect.py ROWS OUT.jsonl [--jobs 3]
"""
import argparse
import json
import os
import sys
from collections import Counter
from multiprocessing import Pool

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'le3'))
import termrun_detect as TD  # noqa: E402


def merged_visits(spec, steps=600000, K=3):
    """[(key, counter-side string)] in time order, for every key"""
    tm = TD.parse(spec)
    tape, h, q = {}, 0, 0
    lo, hi = 0, -1
    out = []
    for _t in range(steps):
        s = tape.get(h, 0)
        tr = tm[(q, s)]
        if tr is None:
            return out
        while lo <= hi and not tape.get(lo, 0):
            lo += 1
        while hi >= lo and not tape.get(hi, 0):
            hi -= 1
        if hi >= lo:
            if lo >= h - K:
                o = ''.join(str(tape.get(i, 0)) for i in range(h - 1, lo - 1, -1)) if lo < h else ''
                out.append(((q, s, 'R', o), ''.join(str(tape.get(i, 0)) for i in range(h + 1, hi + 1))))
            if hi <= h + K:
                o = ''.join(str(tape.get(i, 0)) for i in range(h + 1, hi + 1)) if hi > h else ''
                out.append(((q, s, 'L', o), ''.join(str(tape.get(i, 0)) for i in range(h - 1, lo - 1, -1))))
        w, d, nq = tr
        tape[h] = w
        if w:
            if hi < lo:
                lo = hi = h
            else:
                lo, hi = min(lo, h), max(hi, h)
        h += d
        q = nq
    return out


def parse(s, l, Ds):
    x = []
    i = 0
    while i + l <= len(s) and s[i:i + l] in Ds:
        x.append(0 if s[i:i + l] == Ds[0] else 1)
        i += l
    return tuple(x), s[i:]


def inc(x):
    y = list(x)
    i = 0
    while i < len(y) and y[i] == 1:
        y[i] = 0
        i += 1
    if i == len(y):
        return None
    y[i] = 1
    return tuple(y)


def follow(vis, keys, l, Ds, terms):
    """steps along the merged visits of `keys` under the laws, the fill
    table {key: (dw, next key)}"""
    st = None
    n = fills = 0
    tab = {}
    for k, s in vis:
        if k not in keys:
            continue
        x, t = parse(s, l, Ds)
        if t != terms[k]:
            continue
        cur = (k, x)
        if st is None:
            st = cur
            continue
        if cur == st:
            continue
        k0, x0 = st
        nx = inc(x0)
        if nx is not None:
            if cur == (k0, nx):
                st, n = cur, n + 1
            continue
        if any(x):
            continue
        mv = (len(x) - len(x0), k)
        if tab.setdefault(k0, mv) != mv:
            return None
        st, n, fills = cur, n + 1, fills + 1
    return n, fills, tab


def detect(spec):
    vis = merged_visits(spec)
    if not vis:
        return None
    vis = vis[len(vis) // 8:]
    cnt = Counter(k for k, _s in vis)
    keys = [k for k, c in cnt.most_common(16) if c >= 30]
    if not keys:
        return None
    byk = {k: [] for k in keys}
    for k, s in vis:
        if k in byk:
            byk[k].append(s)
    best = None
    # the main anchor: the busiest key with a blank far side
    mains = [k for k in keys if k[3] == ''][:2]
    for k0 in mains:
        others = [k for k in keys if k != k0 and k[2] == k0[2]]
        subs = {k: [] for k in others}
        for k, s in vis:
            if k == k0:
                for k2 in others:
                    subs[k2].append((k, s))
            elif k in subs:
                subs[k].append((k, s))
        for l in (1, 2, 3):
            strs = byk[k0][-300:]
            words = [w for w, _ in Counter(s[i:i + l] for s in strs for i in range(0, 4 * l, l)
                                           if len(s) >= i + l).most_common(3)]
            for i in range(len(words)):
                for j in range(len(words)):
                    if i == j:
                        continue
                    Ds = (words[i], words[j])
                    terms = {}
                    for k in [k0] + others:
                        ts = Counter(parse(s, l, Ds)[1] for s in byk[k][-3000:])
                        t, c = ts.most_common(1)[0]
                        if c >= 0.5 * sum(ts.values()) and len(t) <= 8:
                            terms[k] = t
                    if k0 not in terms:
                        continue
                    # one anchor: a positional counter whose top widens x
                    sub0 = [(k0, s) for s in byk[k0]]
                    g = follow(sub0, {k0}, l, Ds, terms)
                    if g is not None and g[1] >= 2 and g[0] >= 0.8 * len(sub0) \
                            and all(v[0] >= 1 for v in g[2].values()):
                        cand = dict(spec=spec, keys=[list(k0)], l=l, D=list(Ds),
                                    terms={json.dumps(list(k0)): terms[k0]},
                                    table={json.dumps(list(k)): [v[0], list(v[1])]
                                           for k, v in g[2].items()},
                                    steps=g[0], fills=g[1], total=len(sub0))
                        if best is None or (g[0], g[1]) > (best['steps'], best['fills']):
                            best = cand
                    for k1 in others:
                        if k1 not in terms:
                            continue
                        sel = [k0, k1]
                        sub = subs[k1]
                        g = follow(sub[:4000], set(sel), l, Ds, terms)
                        if g is None or g[0] < 0.6 * len(sub[:4000]):
                            continue
                        g = follow(sub, set(sel), l, Ds, terms)
                        if g is None or g[1] < 2 or len(g[2]) < 2:
                            continue
                        if g[0] < 0.8 * len(sub):
                            continue
                        cand = dict(spec=spec, keys=[list(k) for k in sel], l=l, D=list(Ds),
                                    terms={json.dumps(list(k)): terms[k] for k in sel},
                                    table={json.dumps(list(k)): [v[0], list(v[1])]
                                           for k, v in g[2].items()},
                                    steps=g[0], fills=g[1], total=len(sub))
                        if best is None or (g[0], g[1]) > (best['steps'], best['fills']):
                            best = cand
    return best


def work(spec):
    try:
        return detect(spec) or dict(spec=spec, keys=None)
    except Exception as e:  # noqa: BLE001
        return dict(spec=spec, keys=None, error=repr(e))


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
            print(r['spec'], r.get('keys'), r.get('D'), r.get('terms'), r.get('table'),
                  r.get('steps'), r.get('total'), flush=True)


if __name__ == '__main__':
    main()
