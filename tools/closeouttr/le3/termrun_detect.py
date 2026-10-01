#!/usr/bin/env python3
"""UNTRUSTED measurement (SCOPING_INSTR 7.4.LE3): which open rows are
TERMINATOR-RUN counters -- the counter side at an anchor reads
`pre ++ x ++ T^m ++ suf` with `x` a binary string over two words `D0 != D1`
(neither equal to `T`), and the run `T^m` growing as the counter laps:

    (x, m) -> (x + 1, m)                           inside a width
    (D1^j, m) -> (D0^(j-1), m + 1)   j >= 1         the top narrows x
    (empty, m) -> (D0^(m+1), 1)                    and x refills

`0RB1LA_1RC0LA_0LD1RB_1LB0RC` is `[B1] (11|10)^j (01)^m`.  valfam reads
these at small widths as multi-phase families with narrowing fills whose
terminators (`01`, `0101`) are the run itself, which LE2 found no respell
for.  Usage: termrun_detect.py ROWS OUT.jsonl
"""
import json
import sys
from collections import Counter


def parse(spec):
    tm = {}
    for i, p in enumerate(spec.split('_')):
        for r in (0, 1):
            t = p[3 * r:3 * r + 3]
            tm[(i, r)] = None if t[0] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
    return tm


def anchor_strings(spec, steps=150000):
    """per (state, sym, side): the counter-side strings at visits where the
    other side is blank, in order"""
    tm = parse(spec)
    tape, h, q = {}, 0, 0
    lo = hi = 0
    out = {}
    for t in range(steps):
        s = tape.get(h, 0)
        tr = tm[(q, s)]
        if tr is None:
            return out
        cells = [i for i, v in tape.items() if v]
        if True:
            if cells and min(cells) >= h:
                st = ''.join(str(tape.get(i, 0)) for i in range(h + 1, max(cells) + 1))
                out.setdefault((q, s, 'R'), []).append(st)
            elif cells and max(cells) <= h:
                st = ''.join(str(tape.get(i, 0)) for i in range(h - 1, min(cells) - 1, -1))
                out.setdefault((q, s, 'L'), []).append(st)
        w, d, nq = tr
        tape[h] = w
        h += d
        q = nq
        lo, hi = min(lo, h), max(hi, h)
    return out


def read(st, l, pre, suf, T):
    """(x words, m) or None"""
    if not st.startswith(pre) or not st.endswith(suf):
        return None
    body = st[len(pre):len(st) - len(suf)] if suf else st[len(pre):]
    if len(body) % l:
        return None
    ws = [body[i:i + l] for i in range(0, len(body), l)]
    m = 0
    while ws and ws[-1] == T:
        ws.pop()
        m += 1
    if m == 0 or T in ws:
        return None
    return ws, m


def detect(spec):
    best = None
    for key, strs in anchor_strings(spec).items():
        strs = strs[len(strs) // 4::max(1, len(strs) // 500)]
        if len(strs) < 30:
            continue
        for l in (1, 2, 3, 4):
            for pl in range(0, 3):
                for sl in range(0, 3):
                    pre = strs[-1][:pl]
                    suf = strs[-1][len(strs[-1]) - sl:] if sl else ''
                    tails = Counter()
                    for s in strs:
                        b = s[len(pre):len(s) - len(suf)] if suf else s[len(pre):]
                        if len(b) >= l and len(b) % l == 0:
                            tails[b[-l:]] += 1
                    for T, _n in tails.most_common(2):
                        rd = [read(s, l, pre, suf, T) for s in strs]
                        ok = [r for r in rd if r]
                        if len(ok) < 0.9 * len(strs):
                            continue
                        words = Counter(w for ws, _m in ok for w in ws)
                        ms = Counter(m for _ws, m in ok)
                        if len(words) != 2 or len(ms) < 3:
                            continue
                        cand = dict(spec=spec, anchor=list(key), l=l, pre=pre,
                                    suf=suf, T=T, words=sorted(words),
                                    parsed=len(ok), total=len(strs),
                                    mmax=max(ms))
                        if best is None or cand['parsed'] > best['parsed']:
                            best = cand
    return best


def main():
    rows = [l.split()[0] for l in open(sys.argv[1]) if l.strip()]
    with open(sys.argv[2], 'w') as f:
        for spec in rows:
            r = detect(spec) or dict(spec=spec, anchor=None)
            f.write(json.dumps(r) + '\n')
            f.flush()
            print(spec, r.get('anchor'), r.get('T'), r.get('words'), r.get('mmax'),
                  '%s/%s' % (r.get('parsed'), r.get('total')), flush=True)


if __name__ == '__main__':
    main()
