#!/usr/bin/env python3
"""LE7 (UNTRUSTED probe): how each increment of a mirrored counter reading
splits.  Between consecutive anchor visits x -> x+1, look for a step where
the head is back on the anchor cell with ONE side already final and the
other still original.  Prints the (order, state, symbol) sets seen per
increment kind (interior / top).

    python3 mirror_split.py SPEC DETECT.jsonl [steps]
"""
import json
import os
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'le3'))
import mirror_detect as MD  # noqa: E402
import termrun_detect as TD  # noqa: E402


def sides(tape, h, lo, hi):
    L = ''.join(str(tape.get(i, 0)) for i in range(h - 1, lo - 1, -1)).rstrip('0')
    R = ''.join(str(tape.get(i, 0)) for i in range(h + 1, hi + 1)).rstrip('0')
    return L, R


WIN = 3


def probe(spec, det, steps):
    tm = TD.parse(spec)
    q0, s0 = det['anchor']
    aL = (det['L']['pre'], det['L']['l'], det['L']['words'], det['L']['suf'])
    aR = (det['R']['pre'], det['R']['l'], det['R']['words'], det['R']['suf'])
    tape, h, q = {}, 0, 0
    lo = hi = 0
    log = []
    last = None
    res = Counter()
    for _t in range(steps):
        s = tape.get(h, 0)
        if q == q0 and s == s0:
            L, R = sides(tape, h, lo, hi)
            d = MD.decode(L, *aL)
            if d and MD.decode(R, *aR) == d:
                if last is not None and h == last[0] and d == MD.inc(last[1]):
                    kind = 'top' if all(v == 1 for v in last[1]) else 'int'
                    hits = set()
                    for (qq, ss, LL, RR) in log:
                        if LL == L and RR == last[3]:
                            hits.add(('L', qq, ss))
                        if RR == R and LL == last[2]:
                            hits.add(('R', qq, ss))
                    res[(kind, tuple(sorted(hits)))] += 1
                last = (h, d, L, R)
                log = []
        elif last is not None and abs(h - last[0]) <= WIN:
            h0 = last[0]
            # the two regions about the anchor cell h0, the head anywhere near it
            L = ''.join(str(tape.get(i, 0)) for i in range(h0 - 1, lo - 1, -1)).rstrip('0')
            R = ''.join(str(tape.get(i, 0)) for i in range(h0 + 1, hi + 1)).rstrip('0')
            log.append(((h - h0, q, tape.get(h0, 0)), s, L, R))
        w, dd, nq = tm[(q, s)]
        tape[h] = w
        h += dd
        q = nq
        lo, hi = min(lo, h), max(hi, h)
    return res


if __name__ == '__main__':
    spec = sys.argv[1]
    det = None
    for l in open(sys.argv[2]):
        r = json.loads(l)
        if r['spec'] == spec:
            det = r
    for k, v in probe(spec, det, int(sys.argv[3]) if len(sys.argv) > 3 else 100000).most_common():
        print(v, k)


def split_of(spec, det, steps=60000):
    """{lf, qI, hI, qT, hT}: a split ON the anchor cell seen at EVERY
    increment of its kind, the same order for both kinds; or None"""
    res = probe(spec, det, steps)
    common = {}
    for (kind, hits), _n in res.items():
        hs = set((o, k[1], s) for o, k, s in hits if k[0] == 0)
        common[kind] = hs if kind not in common else common[kind] & hs
    if 'int' not in common or 'top' not in common:
        return None
    for o in ('L', 'R'):
        ci = sorted((q, s) for oo, q, s in common['int'] if oo == o)
        ct = sorted((q, s) for oo, q, s in common['top'] if oo == o)
        if ci and ct:
            return dict(lf=(o == 'L'), qI=ci[0][0], hI=ci[0][1], qT=ct[0][0], hT=ct[0][1])
    return None
