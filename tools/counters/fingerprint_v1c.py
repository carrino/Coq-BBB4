#!/usr/bin/env python3
"""v1-COMPATIBLE fingerprints with the v2 blank-strip fix.

The emitters (emit_interleave.py / emit_mirror.py) consume the v1 record shape
{m, cls, enc: Ip|Jp, growth: L|R, edge, p0} -- enc is a MARKER-FIRST encoding
(1,d0,1,d1,...), which is what the Coq templates' Ip/Jp lemmas need.

v1's fingerprinter missed ~92% of the counter core purely because it tested
whether the far side was an EMPTY LIST rather than BLANK (a machine writing S0
past the head has far side [S0;S0]).  This tool keeps the v1 output shape and
the marker-first requirement, but strips trailing blanks -- recovering the
machines v1 rejected on that technicality, in a form the emitters can use.

(Data-first anchors are not emitted: such a machine's counter list is
d0,1,d1,1,... which is not an Ip/Jp term.  Its marker-first anchor, one cell
over, is found here when one exists.)
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

def decode_marker_first(lst, polarity):
    """Decode nearest-first list as 1,d0,1,d1,... (markers at even indices).
    polarity 0 -> data bit is the digit (Ip); 1 -> complement (Jp)."""
    l = strip_blanks(list(lst))
    if len(l) < 3 or len(l) % 2 == 0:
        return None
    if any(l[i] != 1 for i in range(0, len(l), 2)):
        return None
    bits = [l[i] for i in range(1, len(l), 2)]
    if polarity:
        bits = [1 - b for b in bits]
    v = 0
    for k, b in enumerate(bits):
        v |= b << k
    return v + (1 << len(bits))

def fingerprint(spec, T=40000, minhits=12):
    tab = parse(spec)
    q, l, h, r = 0, [], 0, []
    from collections import defaultdict
    seq = defaultdict(list)
    for t in range(T):
        e = tab[(q, h)]
        if e is None:
            return {'m': spec, 'cls': 'HALT'}
        for side, near, far in (('L', l, r), ('R', r, l)):
            if strip_blanks(list(far)):
                continue
            for pol, enc in ((0, 'Ip'), (1, 'Jp')):
                v = decode_marker_first(near, pol)
                if v is not None and v > 2:
                    seq[("ABCD"[q], side, enc)].append(v)
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
        if frac < 0.75:
            continue
        score = frac * len(vals)
        if best is None or score > best[0]:
            best = (score, k, len(vals), round(frac, 3), vals[0])
    if best is None:
        return {'m': spec, 'cls': 'NOFIT'}
    _, (st, side, enc), n, frac, p0 = best
    return {'m': spec, 'cls': 'COUNTER', 'enc': enc, 'growth': side,
            'edge': st, 'p0': p0, 'nsnap': n, 'ndec': n, 'frac': frac}

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
