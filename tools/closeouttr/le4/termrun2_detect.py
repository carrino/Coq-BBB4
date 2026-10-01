#!/usr/bin/env python3
"""UNTRUSTED measurement (SCOPING_INSTR 7.4.LE4): terminator-run counters with
a MARKER, `LadderCheckRun2Tr`'s shape: at an anchor the counter side reads

    pre ++ x ++ M ++ T^m ++ suf

with `x` over two words D0 != D1 (either may equal T), the run `T^m`
possibly empty, and

    (x, m) -> (x + 1, m)                           inside a width
    (D1^j, m) -> (D0^(j-1), m + 1)   j >= 1         the top narrows x
    (empty, m) -> (D0^(m+a), c)                    and x refills

`0RB0LC_1LC0RD_1LA1LD_0LA1RB` is `[A0] (10|11)^j 01 (11)^m 1`: M = 01, T = 11,
suf = 1.  LE3's `termrun_detect.py` is the case M = T, m >= 1.

    termrun2_detect.py ROWS OUT.jsonl [--jobs 4]
"""
import argparse
import json
import os
import sys
from collections import Counter
from multiprocessing import Pool

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'le3'))
import termrun_detect as TD  # noqa: E402


def read(st, l, pre, suf, T, M):
    """(x words, m) or None: the run is the LONGEST suffix of T's that leaves
    `x ++ M` with x a whole number of words"""
    if not st.startswith(pre) or not st.endswith(suf):
        return None
    body = st[len(pre):len(st) - len(suf)] if suf else st[len(pre):]
    best, k = None, 0
    while True:
        if body.endswith(M) and (len(body) - len(M)) % l == 0:
            best = (body[:len(body) - len(M)], k)
        if not T or not body.endswith(T):
            break
        body, k = body[:len(body) - len(T)], k + 1
    if best is None:
        return None
    xs, m = best
    return [xs[i:i + l] for i in range(0, len(xs), l)], m


def succ(x, m, a):
    if not x:
        return None   # a refill: (0^(m+a), c), a and c read off the run
    if all(v == 1 for v in x):
        return [0] * (len(x) - 1), m + 1
    y = list(x)
    i = 0
    while y[i] == 1:
        y[i] = 0
        i += 1
    y[i] = 1
    return y, m


def lawful(ok, words):
    """(steps, narrowings, refills) along the readings, following the laws
    and skipping readings that are not the next state (transient visits),
    for the better of the two digit assignments"""
    best = (0, 0, 0)
    for d0, d1 in (words, words[::-1]):
        st = None
        n = nn = nr = 0
        for ws, m in ok:
            cur = ([0 if w == d0 else 1 for w in ws], m)
            if st is None:
                st = cur
                continue
            if cur == st:
                continue
            x, pm = st
            if not x:
                if cur[0] and all(v == 0 for v in cur[0]):
                    st, n, nr = cur, n + 1, nr + 1
                continue
            if cur == succ(x, pm, 0):
                st, n = cur, n + 1
                nn += all(v == 1 for v in x)
        if (n, nn, nr) > best:
            best = (n, nn, nr)
    return best


def detect(spec):
    best = None
    for key, strs in TD.anchor_strings(spec).items():
        strs = strs[len(strs) // 4:][:3000]
        if len(strs) < 30:
            continue
        for l in (1, 2, 3):
            for pl in range(0, 3):
                for sl in range(0, 3):
                    pre = strs[-1][:pl]
                    suf = strs[-1][len(strs[-1]) - sl:] if sl else ''
                    bodies = [s[len(pre):len(s) - len(suf)] if suf else s[len(pre):]
                              for s in strs if s.startswith(pre) and s.endswith(suf)]
                    tails = Counter(b[-l:] for b in bodies if len(b) >= l)
                    for T, _n in tails.most_common(2):
                        for ml in (1, 2, 3, 4):
                            Ms = Counter()
                            for b in bodies:
                                bb = b
                                while bb.endswith(T) and len(bb) > len(T):
                                    bb = bb[:len(bb) - len(T)]
                                if len(bb) >= ml:
                                    Ms[bb[-ml:]] += 1
                            for M, _k in Ms.most_common(2):
                                rd = [read(s, l, pre, suf, T, M) for s in strs]
                                ok = [r for r in rd if r]
                                if len(ok) < 0.5 * len(strs):
                                    continue
                                words = Counter(w for ws, _m in ok for w in ws)
                                ms = Counter(m for _ws, m in ok)
                                if len(words) != 2 or len(ms) < 3:
                                    continue
                                law = lawful(ok, sorted(words))
                                if law[0] < 40 or law[1] < 2 or law[2] < 1:
                                    continue
                                cand = dict(spec=spec, anchor=list(key), l=l, pre=pre,
                                            suf=suf, T=T, M=M, words=sorted(words),
                                            parsed=len(ok), total=len(strs),
                                            mmax=max(ms), lawful=law)
                                if best is None or (cand['lawful'], cand['parsed']) > \
                                        (best['lawful'], best['parsed']):
                                    best = cand
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
    ap.add_argument('--jobs', type=int, default=4)
    a = ap.parse_args()
    rows = [l.split()[0] for l in open(a.rows) if l.strip()]
    done = set()
    if os.path.exists(a.out):
        done = set(json.loads(l)['spec'] for l in open(a.out))
    with Pool(a.jobs) as pool, open(a.out, 'a') as f:
        for r in pool.imap_unordered(work, [s for s in rows if s not in done]):
            f.write(json.dumps(r) + '\n')
            f.flush()
            print(r['spec'], r.get('anchor'), r.get('M'), r.get('T'), r.get('words'),
                  r.get('mmax'), '%s/%s' % (r.get('parsed'), r.get('total')), flush=True)


if __name__ == '__main__':
    main()
