#!/usr/bin/env python3
"""UNTRUSTED counter fingerprinter, v2 -- the generalized anchor test.

v1 (fingerprint.py) recognized only 181 of the 2,480 counter-core machines.
Two bugs, both found by hand-checking a machine the human identified as an
obvious interleaved counter (0RB0LD_0RC1RC_1LD1RC_0RC1LA):

 1. THE BLANK-vs-EMPTY BUG (the big one).  v1 required the far side to be an
    EMPTY LIST.  A machine that writes S0 cells beyond the head has a far side
    like [S0;S0] -- denotationally blank (lift strips trailing blanks) but not
    an empty python list -- so every such machine was rejected.  v2 strips
    trailing blanks before the test.
 2. INTERLEAVE PARITY.  v1 tried only marker-first (1,d0,1,d1,... = Ip/Jp).
    Counters also appear data-first (d0,1,d1,1,...), i.e. the same encoding
    read from an anchor one cell over.  v2 tries both parities.

v2 also decodes generically (walk the list in period-2 pairs) instead of
matching a precomputed Ip/Jp table, so it is not bounded by a table size, and
it reports the parity + polarity the emitter needs.
"""
import sys, os, json
from concurrent.futures import ProcessPoolExecutor

def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3*yi:3*yi+3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab

def strip_blanks(l):
    i = len(l)
    while i > 0 and l[i-1] == 0:
        i -= 1
    return l[:i]

def decode(lst, parity, polarity):
    """Decode a nearest-first half-tape as an interleaved binary counter.

    parity 0 = marker-first (1,d0,1,d1,...); parity 1 = data-first (d0,1,d1,1,...)
    polarity 0 = data bit is the digit; 1 = data bit is the complement.
    Returns the value (LSB nearest the head) or None if the markers do not
    all hold S1.
    """
    l = strip_blanks(list(lst))
    if parity:
        data_idx = range(0, len(l), 2)
        mark_idx = range(1, len(l), 2)
    else:
        data_idx = range(1, len(l), 2)
        mark_idx = range(0, len(l), 2)
    marks = [l[i] for i in mark_idx]
    if not marks or any(x != 1 for x in marks):
        return None
    bits = [l[i] for i in data_idx]
    if not bits:
        return None
    if polarity:
        bits = [1 - b for b in bits]
    v = 0
    for k, b in enumerate(bits):
        v |= b << k
    return v + (1 << len(bits))      # implicit leading 1 (the counter's MSB)

VARIANTS = [(p, q) for p in (0, 1) for q in (0, 1)]

def fingerprint(spec, T=40000, minhits=12):
    tab = parse(spec)
    q, l, h, r = 0, [], 0, []
    from collections import defaultdict
    seq = defaultdict(list)
    for t in range(T):
        e = tab[(q, h)]
        if e is None:
            return {'m': spec, 'cls': 'HALT'}
        # generalized anchor: the FAR side is blank (after stripping), the
        # counter rides the near side.  Try both sides, both parities.
        for side, near, far in (('L', l, r), ('R', r, l)):
            if strip_blanks(list(far)):
                continue
            for (par, pol) in VARIANTS:
                v = decode(near, par, pol)
                if v is not None and v > 2:
                    seq[("ABCD"[q], side, par, pol, h)].append(v)
        w, d, ns = e
        if d > 0:
            q, l, h, r = ns, [w] + l, (r[0] if r else 0), r[1:]
        else:
            q, l, h, r = ns, l[1:], (l[0] if l else 0), [w] + r
    best = None
    for k, vals in seq.items():
        if len(vals) < minhits:
            continue
        runs = sum(1 for a, b in zip(vals, vals[1:]) if b == a + 1)
        frac = runs / max(1, len(vals) - 1)
        # a real counter increments monotonically; a run of ones decodes as a
        # constant/erratic sequence and is rejected here
        if frac < 0.75:
            continue
        score = frac * len(vals)
        if best is None or score > best[0]:
            best = (score, k, len(vals), round(frac, 3), vals[0])
    if best is None:
        return {'m': spec, 'cls': 'NOFIT'}
    _, (st, side, par, pol, hd), n, frac, p0 = best
    return {'m': spec, 'cls': 'COUNTER', 'edge': st, 'growth': side,
            'parity': par, 'polarity': pol, 'head': hd,
            'nanchor': n, 'frac': frac, 'p0': p0}

def main():
    src, out = sys.argv[1], sys.argv[2]
    ms = [x.strip() for x in open(src) if x.strip()]
    n = int(os.environ.get('FP_LIMIT', len(ms)))
    ms = ms[:n]
    with open(out, 'w') as f, ProcessPoolExecutor(max_workers=3) as ex:
        for i, r in enumerate(ex.map(fingerprint, ms, chunksize=8)):
            f.write(json.dumps(r) + '\n')
            if (i + 1) % 250 == 0:
                f.flush(); sys.stderr.write('%d/%d\n' % (i + 1, len(ms)))
    sys.stderr.write('DONE %d\n' % len(ms))

if __name__ == '__main__':
    main()
