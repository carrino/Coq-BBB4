#!/usr/bin/env python3
"""UNTRUSTED (SCOPING_INSTR 7.4.LE5): `phrun_detect.py`'s reading, but with
every parse of a visit kept: x over D words, a phase word W of at most
WMAX cells (it may begin with a D word or end with T), the run T^m.  A
beam of hypotheses (state, move table) is followed along the visits; an
interior step must be x + 1, a top move must be the same for each phase
word every time; visits that match no successor are skipped (transients).

    phrun2.py ROWS OUT.jsonl [--jobs 3]
"""
import argparse
import json
import os
import sys
from collections import Counter
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import termrun3_detect as TD3  # noqa: E402

WMAX = 10


VMAX = 3


def parses(st, l, pre, suf, T, Ds):
    """every (x, W|V, m): the phase is the pair of words around the run"""
    if not st.startswith(pre) or (suf and not st.endswith(suf)):
        return []
    body0 = st[len(pre):len(st) - len(suf)] if suf else st[len(pre):]
    out = []
    for vl in range(0, min(VMAX, len(body0)) + 1):
        V = body0[len(body0) - vl:] if vl else ''
        body = body0[:len(body0) - vl]
        bodies = [(body, 0)]
        if T:
            b, m = body, 0
            while b.endswith(T):
                b, m = b[:len(b) - len(T)], m + 1
                bodies.append((b, m))
        for b, m in bodies[-2:]:
            for x, w in _xw(b, l, Ds):
                out.append((x, w + '|' + V, m))
    return out


def _xw(b, l, Ds):
    out = []
    if True:
        for k in range(0, min(len(b), WMAX) + 1):
            if (len(b) - k) % l:
                continue
            xs = b[:len(b) - k]
            x = []
            ok = True
            for i in range(0, len(xs), l):
                w = xs[i:i + l]
                if w == Ds[0]:
                    x.append(0)
                elif w == Ds[1]:
                    x.append(1)
                else:
                    ok = False
                    break
            if ok:
                out.append((tuple(x), b[len(b) - k:]))
    return out


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


def follow(strs, l, pre, suf, T, Ds, beam=40, maxw=8, maxskip=8):
    P = [parses(s, l, pre, suf, T, Ds) for s in strs]
    hyps = [(p, {}, 0, 0, 0) for p in P[0]]      # state, table, steps, tops, skips
    for i in range(1, len(P)):
        nxt = set(P[i])
        new = []
        for st, tab, n, tp, sk in hyps:
            x, w, m = st
            if st in nxt:
                new.append((st, tab, n, tp, sk))
                continue
            nx = inc(x)
            if nx is not None:
                if (nx, w, m) in nxt:
                    new.append(((nx, w, m), tab, n + 1, tp, 0))
                elif sk < maxskip:
                    new.append((st, tab, n, tp, sk + 1))
                continue
            got = False
            for x2, w2, m2 in nxt:
                if any(x2):
                    continue
                mv = ('M', len(x2) - len(x), w2, m2 - m)
                alts = [mv] + ([('R', len(x2) - m, w2, m2)] if not x else [])
                key = ('E|' if not x else 'T|') + w
                old = tab.get(key)
                if old is None:
                    keep = alts
                else:
                    keep = [o for o in old if o in alts]
                    if not keep:
                        continue
                t2 = dict(tab)
                t2[key] = keep
                ws = set(k[2:] for k in t2) | set(v[0][2] for v in t2.values())
                if len(ws) > maxw:
                    continue
                new.append(((x2, w2, m2), t2, n + 1, tp + 1, 0))
                got = True
            if not got and sk < maxskip:
                new.append((st, tab, n, tp, sk + 1))
        if not new:
            return None
        # dedupe and prune: more steps first, then fewer phase words
        seen = {}
        for h in new:
            k = (h[0], tuple(sorted((a, tuple(map(tuple, b))) for a, b in h[1].items())))
            if k not in seen or h[2] > seen[k][2]:
                seen[k] = h
        hyps = sorted(seen.values(), key=lambda h: (-h[2], len(h[1])))[:beam]
    return hyps[0] if hyps else None


def detect(spec, steps=400000):
    best = None
    A = TD3.anchor_strings(spec, steps)
    for key, strs in A.items():
        strs = strs[len(strs) // 8:][:20000]
        if len(strs) < 30:
            continue
        for l in (1, 2, 3):
            starts = Counter(s[i:i + l] for s in strs[-300:] for i in range(0, 4 * l, l)
                             if len(s) >= i + l)
            words = [w for w, _ in starts.most_common(3)]
            for i in range(len(words)):
                for j in range(len(words)):
                    if i == j:
                        continue
                    Ds = (words[i], words[j])
                    for pl in (0, 1):
                        pre = strs[-1][:pl]
                        for sl in (0,):
                            suf = strs[-1][len(strs[-1]) - sl:] if sl else ''
                            for tl in (1, 2, 3):
                                Ts = Counter(s[len(s) - len(suf) - tl:len(s) - len(suf)]
                                             for s in strs[-300:])
                                for T, _k in Ts.most_common(2):
                                    h = follow(strs[:1500], l, pre, suf, T, Ds, beam=12)
                                    if h is None or h[3] < 3 or h[2] < 0.7 * 1500:
                                        continue
                                    h = follow(strs, l, pre, suf, T, Ds)
                                    if h is None:
                                        continue
                                    st, tab, n, tp, _sk = h
                                    ws = set(k[2:] for k in tab) | set(v[0][2] for v in tab.values())
                                    score = (n, -len(ws))
                                    if best is None or score > best['score']:
                                        best = dict(spec=spec, anchor=list(key), l=l, D=list(Ds),
                                                    pre=pre, suf=suf, T=T, words=sorted(ws),
                                                    table=tab, steps=n, tops=tp,
                                                    total=len(strs), score=score)
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
