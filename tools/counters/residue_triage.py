#!/usr/bin/env python3
"""UNTRUSTED triage: cluster the unboarded residue by MEASURED signature.

Wave-13 §9 established that the "no interior chain" bucket was not one class
but at least four, and that one of them (quadratic laps) is outside the
certificate model entirely.  The lesson: measure cost-vs-j before templating.
This does that for every machine at once, so a human tape-reading is spent on
a CLASS rather than on a machine.

Per machine it reports:

  decode  how the anchor's word decodes as an index sequence --
          BIN (plain binary, consecutive) / GRAY (reflected binary) / none.
          Gray is detected via gray^-1 and accepts a PERIODIC difference
          pattern, not just a constant one: an anchor predicate that catches
          two phases per period yields 4,5,8,9,12,13,... and a
          constant-difference test scores that as "none".
  degree  the degree of the interior lap cost as a function of the carry
          index j: AFFINE (in the certificate model), QUAD (out of it --
          one widening round trip per carry bit), or HIGHER/irregular.
  anchor  whether emit_lapcert's Ip/Jp/Kp/Dp/Mp anchor search fires.

Everything here is measurement only; nothing it says is trusted by any proof.
"""
import collections
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from emit_interleave import parse                                  # noqa: E402
import lapcert as LC                                               # noqa: E402


def ginv(v):
    n = 0
    while v:
        n ^= v
        v >>= 1
    return n


def trail1(n):
    j = 0
    while (n >> j) & 1:
        j += 1
    return j


def snapshots(spec, T=200000):
    """(state, side) -> [(t, value)] at configurations whose FAR side is empty
    and whose head is blank -- the shape every counter anchor has."""
    tab = parse(spec)
    out = collections.defaultdict(list)
    cfg = (0, (), 0, ())
    for t in range(T):
        q, l, h, r = cfg
        if h == 0:
            if not l and r:
                out[('R', q)].append((t, sum(b << i for i, b in enumerate(r))))
            if not r and l:
                out[('L', q)].append((t, sum(b << i for i, b in enumerate(l))))
        try:
            cfg = LC.wstep(tab, False, False, cfg)
        except LC.Halt:
            break
    return out


def periodic_run(seq, maxper=4):
    """Longest run whose successive differences repeat with some period <= 4
    and are all positive.  Returns (length, period)."""
    best = (0, 0)
    if len(seq) < 3:
        return best
    d = [seq[i + 1] - seq[i] for i in range(len(seq) - 1)]
    for per in range(1, maxper + 1):
        i = 0
        while i < len(d):
            if d[i] <= 0:
                i += 1
                continue
            k = 1
            while (i + k < len(d) and d[i + k] > 0
                   and d[i + k] == d[i + (k % per)]):
                k += 1
            if k + 1 > best[0]:
                best = (k + 1, per)
            i += max(k, 1)
    return best


def classify(spec):
    snaps = snapshots(spec)
    best = None                       # (score, kind, key, index_of)
    for key, rows in snaps.items():
        vals = [v for _, v in rows]
        if len(vals) < 8:
            continue
        for kind, f in (('BIN', lambda v: v), ('GRAY', ginv)):
            seq = [f(v) for v in vals]
            n, per = periodic_run(seq)
            if n >= 10 and (best is None or n > best[0]):
                best = (n, kind, key, f)
    if best is None:
        return dict(decode='none', degree='-', per=0)
    _, kind, key, f = best
    rows = snaps[key]
    # lap cost as a function of the carry index j of the INDEX (not the word)
    at = {}
    for t, v in rows:
        at.setdefault(f(v), t)
    gaps = collections.defaultdict(set)
    for n in sorted(at):
        if n + 1 in at and at[n + 1] > at[n]:
            gaps[trail1(n)].add(at[n + 1] - at[n])
    pts = [(j, next(iter(gaps[j]))) for j in sorted(gaps)
           if len(gaps[j]) == 1 and j <= 7]
    deg = '-'
    if len(pts) >= 4:
        d1 = [pts[i + 1][1] - pts[i][1] for i in range(len(pts) - 1)]
        d2 = [d1[i + 1] - d1[i] for i in range(len(d1) - 1)]
        if len(set(d1)) == 1:
            deg = 'AFFINE'
        elif len(set(d2)) == 1:
            deg = 'QUAD'
        else:
            deg = 'HIGHER'
    return dict(decode=kind, degree=deg, per=0)


def main():
    specs = [l.strip() for l in open(sys.argv[1]) if l.strip()]
    if len(sys.argv) > 2:
        specs = specs[:int(sys.argv[2])]
    c = collections.Counter()
    ex = collections.defaultdict(list)
    for s in specs:
        try:
            r = classify(s)
            k = '%s/%s' % (r['decode'], r['degree'])
        except Exception as e:                                # noqa: BLE001
            k = 'error:%s' % type(e).__name__
        c[k] += 1
        ex[k].append(s)
        print('%-40s %s' % (s, k), flush=True)
    print('\n=== clusters ===')
    for k, v in c.most_common():
        print('%5d  %-16s  e.g. %s' % (v, k, '  '.join(ex[k][:3])))


if __name__ == '__main__':
    main()
