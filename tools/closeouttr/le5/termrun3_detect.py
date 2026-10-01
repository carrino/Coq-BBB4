#!/usr/bin/env python3
"""UNTRUSTED measurement (SCOPING_INSTR 7.4.LE5): terminator-run counters
whose TOP digit has its own spelling.  At an anchor the counter side reads

    pre ++ x ++ e ++ T^m ++ suf

with `x` over two words D0 != D1, `e` over two words E0 != E1 (the top
digit of the counter x ++ [e]), the run `T^m` possibly empty, and

    (x, e, m) -> (x, e) + 1                         inside a width
    (D1^j, E1, m) -> (D0^(j-1), E0, m + 1)  j >= 1  the top narrows x
    (empty, E1, m) -> (D0^(m+a), E0, c)             and x refills

`0RB1LA_1LC1RD_0RB0LD_1RB0LA` is `[A1] (11|01)^j (10|00) (01)^m`, digits
11 = 0, 01 = 1, E0 = 10, E1 = 00, T = 01.  LE4's `termrun2_detect.py` is
the case E0 = E1 (a marker); `pos_detect.py` reads these rows with the
terminator `E0 T` and a fill whose cost doubles (§7.4.LE4 item 3).

    termrun3_detect.py ROWS OUT.jsonl [--jobs 4]
"""
import argparse
import json
import os
import sys
from collections import Counter
from multiprocessing import Pool

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'le3'))
import termrun_detect as TD  # noqa: E402


def read(st, l, pre, suf, T, Es):
    """(x words, e word, m) or None: the longest run that leaves `x ++ e`
    with e in Es and x a whole number of words"""
    if not st.startswith(pre) or not st.endswith(suf):
        return None
    body = st[len(pre):len(st) - len(suf)] if suf else st[len(pre):]
    best, k = None, 0
    while True:
        for E in Es:
            if body.endswith(E) and (len(body) - len(E)) % l == 0:
                best = (body[:len(body) - len(E)], E, k)
        if not T or not body.endswith(T):
            break
        body, k = body[:len(body) - len(T)], k + 1
    if best is None:
        return None
    xs, e, m = best
    return [xs[i:i + l] for i in range(0, len(xs), l)], e, m


def succ(x, e, m):
    """the successor, or None at a refill"""
    if all(v == 1 for v in x):
        if e == 0:
            return [0] * len(x), 1, m
        if not x:
            return None
        return [0] * (len(x) - 1), 0, m + 1
    y = list(x)
    i = 0
    while y[i] == 1:
        y[i] = 0
        i += 1
    y[i] = 1
    return y, e, m


def lawful(ok, words, ews):
    """(steps, narrowings, refills) along the readings that follow the laws
    (transient visits skipped), for the best digit assignment; and the
    refill law (a, c) if one is seen"""
    best = ((0, 0, 0), None, None)
    for d0, d1 in (words, words[::-1]):
        for e0, e1 in (ews, ews[::-1]):
            st = None
            n = nn = nr = 0
            law = set()
            for ws, ew, m in ok:
                cur = ([0 if w == d0 else 1 for w in ws], 0 if ew == e0 else 1, m)
                if st is None:
                    st = cur
                    continue
                if cur == st:
                    continue
                x, e, pm = st
                nx = succ(x, e, pm)
                if nx is None:
                    if cur[0] and all(v == 0 for v in cur[0]) and cur[1] == 0:
                        law.add((len(cur[0]) - pm, cur[2]))
                        st, n, nr = cur, n + 1, nr + 1
                    continue
                if cur == nx:
                    st, n = cur, n + 1
                    nn += all(v == 1 for v in x) and e == 1
            if (n, nn, nr) > best[0]:
                best = ((n, nn, nr), (d0, d1, e0, e1), sorted(law))
    return best


def anchor_strings(spec, steps):
    """`termrun_detect.anchor_strings`, with the nonblank extent kept
    incrementally (blanks are never written back past it in a counter, and
    a stale extent only makes a string longer by blanks, which no reading
    accepts)"""
    tm = TD.parse(spec)
    tape, h, q = {}, 0, 0
    lo, hi = 0, -1
    out = {}
    for _t in range(steps):
        s = tape.get(h, 0)
        tr = tm[(q, s)]
        if tr is None:
            return out
        if hi >= lo:
            while lo <= hi and not tape.get(lo, 0):
                lo += 1
            while hi >= lo and not tape.get(hi, 0):
                hi -= 1
        if hi >= lo:
            if lo >= h:
                out.setdefault((q, s, 'R'), []).append(
                    ''.join(str(tape.get(i, 0)) for i in range(h + 1, hi + 1)))
            elif hi <= h:
                out.setdefault((q, s, 'L'), []).append(
                    ''.join(str(tape.get(i, 0)) for i in range(h - 1, lo - 1, -1)))
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


def detect(spec, steps=400000):
    best = None
    for key, strs in anchor_strings(spec, steps).items():
        strs = strs[len(strs) // 8:][:30000]
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
                        for el in (1, 2, 3, 4):
                            Ms = Counter()
                            for b in bodies:
                                bb = b
                                while bb.endswith(T) and len(bb) > len(T):
                                    bb = bb[:len(bb) - len(T)]
                                if len(bb) >= el:
                                    Ms[bb[-el:]] += 1
                            # E0 may also end in T (the run then eats it): add
                            # the words seen just before the run's start
                            cands = [w for w, _k in Ms.most_common(4)]
                            for i in range(len(cands)):
                                for j in range(i + 1, len(cands)):
                                    Es = (cands[i], cands[j])
                                    pr = [read(s, l, pre, suf, T, Es) for s in strs[:3000]]
                                    pok = [r for r in pr if r]
                                    if len(pok) < 0.5 * len(pr):
                                        continue
                                    pw = Counter(w for ws, _e, _m in pok for w in ws)
                                    if len(pw) != 2 or lawful(pok, sorted(pw), list(Es))[0][1] < 2:
                                        continue
                                    rd = [read(s, l, pre, suf, T, Es) for s in strs]
                                    ok = [r for r in rd if r]
                                    if len(ok) < 0.5 * len(strs):
                                        continue
                                    words = Counter(w for ws, _e, _m in ok for w in ws)
                                    ms = Counter(m for _ws, _e, m in ok)
                                    if len(words) != 2 or len(ms) < 3:
                                        continue
                                    law, asg, rl = lawful(ok, sorted(words), list(Es))
                                    if law[0] < 40 or law[1] < 2 or law[2] < 1:
                                        continue
                                    cand = dict(spec=spec, anchor=list(key), l=l, pre=pre,
                                                suf=suf, T=T, E=list(asg[2:]),
                                                D=list(asg[:2]), refill=rl,
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
            print(r['spec'], r.get('anchor'), r.get('D'), r.get('E'), r.get('T'),
                  r.get('refill'), r.get('lawful'), '%s/%s' % (r.get('parsed'), r.get('total')),
                  flush=True)


if __name__ == '__main__':
    main()
