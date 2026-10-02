#!/usr/bin/env python3
"""LE7 UNTRUSTED reader: MIRRORED binary counters (LE6's sqrt(2) rows).  At
an anchor (state, head symbol) with both sides written, each side read
OUTWARD from the head is

    preL ++ flat_map DL x ++ sufL        preR ++ flat_map DR x ++ sufR

for ONE digit string x (LSB at the head), with its own two words per side
(`1RB0RA_1LC1RA_1LD0LC_1LA1LD`: left `1000 (00|11)^n`, right `(00|01)^n`).
Consecutive readings must be x + 1, the overflow widening x by a digit on
both sides (all-top -> 0^n 1).  Each side's string ends at its last nonzero
cell, so a reading may pad it with up to l blanks.

    python3 tools/closeouttr/le7/mirror_detect.py ROWS OUT.jsonl [--jobs 4] [--steps N]
"""
import argparse
import json
import os
import sys
from collections import Counter
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'le3'))
import termrun_detect as TD  # noqa: E402

STEPS = [400000]


def both_strings(spec, steps):
    """per (state, sym): [(left outward, right outward)] at every visit"""
    tm = TD.parse(spec)
    W = 1 << 16
    tape = bytearray(2 * W)
    h, q = W, 0
    lo, hi = W, W
    out = {}
    for t in range(steps):
        s = tape[h]
        tr = tm[(q, s)]
        if tr is None:
            break
        # the written span [lo, hi] (cells ever visited)
        L = tape[lo:h][::-1]
        R = tape[h + 1:hi + 1]
        out.setdefault((q, s), []).append((t, L.decode('latin1').translate(TR),
                                           R.decode('latin1').translate(TR)))
        w, d, nq = tr
        tape[h] = w
        h += d
        q = nq
        if h < lo:
            lo = h
        if h > hi:
            hi = h
    return out


TR = {0: '0', 1: '1'}


def strip0(s):
    return s.rstrip('0')


def decode(s, pre, l, words, suf):
    """digit list or None: s (trailing blanks stripped) = pre ++ words ++ suf,
    padded with up to l blanks"""
    s = strip0(s)
    if not s.startswith(pre):
        return None
    body = s[len(pre):]
    for k in range(0, l + len(suf) + 1):
        b = body + '0' * k
        if suf:
            if not b.endswith(suf):
                continue
            b = b[:len(b) - len(suf)]
        if len(b) % l:
            continue
        ws = [b[i:i + l] for i in range(0, len(b), l)]
        try:
            return [words.index(w) for w in ws]
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


def lawful(xs):
    """(steps, overflows) along the readings, skipping non-successors"""
    st = None
    n = no = 0
    for x in xs:
        if st is None:
            st = x
            continue
        if x == st:
            continue
        if x == inc(st):
            n += 1
            no += all(v == 1 for v in st)
            st = x
    return n, no


def side_params(strs, maxpre=4):
    """candidate (pre, l, words, suf) for one side from its strings"""
    out = []
    last = strip0(strs[-1])
    for pl in range(0, maxpre + 1):
        pre = last[:pl]
        for l in (1, 2, 3):
            for sl in (0, 1, 2):
                suf = last[len(last) - sl:] if sl else ''
                ws = Counter()
                for s in strs[-200:]:
                    s = strip0(s)
                    if not s.startswith(pre):
                        continue
                    b = s[len(pre):]
                    if suf and b.endswith(suf):
                        b = b[:len(b) - len(suf)]
                    b += '0' * ((-len(b)) % l)
                    for i in range(0, len(b) - l + 1, l):
                        ws[b[i:i + l]] += 1
                top = [w for w, _ in ws.most_common(2)]
                if len(top) == 2:
                    out.append((pre, l, top, suf))
                    out.append((pre, l, top[::-1], suf))
    return out


KEEP = 12


def detect(spec):
    """the best reading, with every lawful reading in `cands` (best first)"""
    cands = detect_all(spec)
    if not cands:
        return None
    return dict(cands[0], cands=cands[:KEEP])


def detect_all(spec):
    out = []
    for key, vis in both_strings(spec, STEPS[0]).items():
        vis = [v for v in vis[len(vis) // 4:] if strip0(v[1]) and strip0(v[2])][:20000]
        if len(vis) < 40:
            continue
        Ls = [v[1] for v in vis]
        Rs = [v[2] for v in vis]
        pL = side_params(Ls)
        pR = side_params(Rs)
        smp = vis[::max(1, len(vis) // 300)]
        for a in pL:
            dl = [decode(v[1], *a) for v in smp]
            if sum(1 for d in dl if d) < 0.2 * len(smp):
                continue
            for b in pR:
                hit = sum(1 for v, d in zip(smp, dl) if d and decode(v[2], *b) == d)
                if hit < 0.2 * len(smp):
                    continue
                xs = []
                for v in vis:
                    d = decode(v[1], *a)
                    if d and decode(v[2], *b) == d:
                        xs.append(d)
                law = lawful(xs)
                if law[0] < 40 or law[1] < 2:
                    continue
                cand = dict(spec=spec, anchor=[key[0], key[1]],
                            L=dict(pre=a[0], l=a[1], words=a[2], suf=a[3]),
                            R=dict(pre=b[0], l=b[1], words=b[2], suf=b[3]),
                            parsed=len(xs), total=len(vis), lawful=law,
                            wmax=max(len(x) for x in xs))
                out.append(cand)
    out.sort(key=lambda c: (-c['lawful'][0], -c['lawful'][1], -c['parsed']))
    return out


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
    ap.add_argument('--steps', type=int, default=STEPS[0])
    a = ap.parse_args()
    STEPS[0] = a.steps
    rows = [l.split()[0] for l in open(a.rows) if l.strip()]
    done = set()
    if os.path.exists(a.out):
        done = set(json.loads(l)['spec'] for l in open(a.out))
    with Pool(a.jobs) as pool, open(a.out, 'a') as f:
        for r in pool.imap_unordered(work, [s for s in rows if s not in done]):
            f.write(json.dumps(r) + '\n')
            f.flush()
            print(r['spec'], r.get('anchor'), r.get('L'), r.get('R'), r.get('lawful'),
                  r.get('error', ''), flush=True)


if __name__ == '__main__':
    main()
