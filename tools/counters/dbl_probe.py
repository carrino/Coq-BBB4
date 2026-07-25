#!/usr/bin/env python3
"""UNTRUSTED: the DOUBLED-BIT interleave encoding.

Human read (2026-07-25) of 1RB1RD_1LC0LB_1RA1LC_0RD1LB: "right wall and 2
copies of each bit".  Confirmed exactly -- at (state D, head S1, far side
blank) the near side reads

    b0 b0 b1 b1 ... bk bk        (LSB nearest the head, every bit DOUBLED)

and decodes to 1,2,3,...,7503 with no gaps.  This is a THIRD encoding family:
Ip/Jp put a marker cell between the bits, this one puts a COPY of the bit.
Every decoder in this project tests that the marker cells all hold S1, so a
doubled-bit tape (whose "markers" are the data) is rejected outright -- which
is why these machines report "no anchor family".

In Coq it is the Ip recursion with the marker replaced by a copy:

    Dp xH      = [S1;S1]
    Dp (xO q)  = S0 :: S0 :: Dp q
    Dp (xI q)  = S1 :: S1 :: Dp q

so the decomposition lemmas have the same shape as ILCounter's:
    cview p = (j, Some q)  ->  Dp p = rep [S1;S1] j ++ S0::S0::Dp q
                               Dp (succ p) = rep [S0;S0] j ++ S1::S1::Dp q
    cview p = (S j, None)  ->  Dp p = rep [S1;S1] (S j)
                               Dp (succ p) = rep [S0;S0] (S j) ++ [S1;S1]
"""
import json
import sys
from concurrent.futures import ProcessPoolExecutor

LAB = "ABCD"


def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab


def mirror_spec(spec):
    out = []
    for part in spec.split('_'):
        t = ''
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            t += e if e == '---' else e[0] + ('L' if e[1] == 'R' else 'R') + e[2]
        out.append(t)
    return '_'.join(out)


def Dp(m):
    """Nearest-first: every bit of m doubled, LSB first, MSB included."""
    out = []
    while m:
        out += [m & 1, m & 1]
        m >>= 1
    return out


def dec(near):
    if not near or len(near) % 2:
        return None
    bits = []
    for i in range(0, len(near), 2):
        if near[i] != near[i + 1]:
            return None
        bits.append(near[i])
    if bits[-1] != 1:
        return None
    return sum(b << i for i, b in enumerate(bits))


def strip0(l):
    i = len(l)
    while i > 0 and l[i - 1] == 0:
        i -= 1
    return list(l[:i])


def step(tab, cfg):
    q, l, h, r = cfg
    e = tab[(q, h)]
    if e is None:
        return None
    w, d, ns = e
    if d > 0:
        return (ns, [w] + l, r[0] if r else 0, r[1:])
    return (ns, l[1:], l[0] if l else 0, [w] + r)


def carry(m):
    j = 0
    while (m >> j) & 1:
        j += 1
    return j, (m == (1 << j) - 1)


def scan(spec, T=120000):
    """Best (edge, head, tail) key whose doubled-bit decode marches by 1."""
    tab = parse(spec)
    cfg = (0, [], 0, [])
    hits = {}
    for t in range(T):
        q, l, h, r = cfg
        far = strip0(r)
        if len(far) <= 6:
            near = strip0(l)
            for tl in range(0, 3):
                body = near[:len(near) - tl] if tl else near
                v = dec(body)
                if v is not None and v > 1:
                    key = (LAB[q], h, tuple(near[len(near) - tl:]) if tl else ())
                    hits.setdefault(key, []).append((t, v, tuple(far)))
        cfg = step(tab, cfg)
        if cfg is None:
            return None
    best = None
    for key, evs in hits.items():
        first = {}
        for t, v, far in evs:
            if v not in first:
                first[v] = (t, far)
        vs = sorted(first)
        run, bestrun, start = 1, 0, None
        for i in range(1, len(vs)):
            if vs[i] == vs[i - 1] + 1 and first[vs[i]][0] > first[vs[i - 1]][0]:
                run += 1
            else:
                if run > bestrun:
                    bestrun, start = run, vs[i - run]
                run = 1
        if run > bestrun:
            bestrun, start = run, vs[len(vs) - run]
        if bestrun < 12:
            continue
        fars = [first[v][1] for v in range(start, start + min(bestrun, 40))]
        wall = list(fars[0]) if all(f == fars[0] for f in fars) else None
        if best is None or bestrun > best[0]:
            best = (bestrun, {'edge': key[0], 'head': key[1],
                              'tail': list(key[2]), 'run': bestrun,
                              'p0': start, 'wall': wall})
    return best[1] if best else None


def lap_len(spec, E, head, tail, far, m, maxsteps=200000):
    tab = parse(spec)
    cfg = (E, Dp(m) + list(tail), head, list(far))
    tgt = (E, Dp(m + 1) + list(tail), head, list(far))
    for n in range(1, maxsteps):
        cfg = step(tab, cfg)
        if cfg is None:
            return None
        if cfg == tgt:
            return n
    return None


def affine(pts):
    js = sorted(pts)
    if len(js) < 2 or any(pts[j] is None for j in js):
        return None
    b = (pts[js[1]] - pts[js[0]]) // (js[1] - js[0]) if (
        (pts[js[1]] - pts[js[0]]) % (js[1] - js[0]) == 0) else None
    if b is None or b <= 0:
        return None
    a = pts[js[0]] - b * js[0]
    return (a, b) if all(pts[j] == a + b * j for j in js) else None


def m_int(j):
    return (1 << (j + 1)) + (1 << j) - 1 if j else 2


def analyse(spec):
    out = {'m': spec}
    for side, sp in (('L', spec), ('R', mirror_spec(spec))):
        r = scan(sp)
        if not r:
            continue
        E = LAB.index(r['edge'])
        for far in ([r['wall']] if r['wall'] is not None else []) + [[], [0]]:
            ints = {j: lap_len(sp, E, r['head'], r['tail'], far, m_int(j))
                    for j in range(4)}
            ovs = {j: lap_len(sp, E, r['head'], r['tail'], far, (1 << j) - 1)
                   for j in range(2, 5)}
            ai, ao = affine(ints), affine(ovs)
            if ai and ao:
                out.update(dict(r, cls='DBL', side=side, far=far,
                                int_affine=ai, ov_affine=ao, both=True))
                return out
        out.update(dict(r, cls='DBL', side=side, both=False))
        return out
    out['cls'] = 'NOFIT'
    return out


def main():
    ms = [x.strip() for x in open(sys.argv[1]) if x.strip()]
    with open(sys.argv[2], 'w') as f, ProcessPoolExecutor(max_workers=4) as ex:
        for i, r in enumerate(ex.map(analyse, ms, chunksize=1)):
            f.write(json.dumps(r) + '\n')
            f.flush()
            sys.stderr.write('%d/%d %s %s both=%s\n'
                             % (i + 1, len(ms), r['m'], r.get('cls'),
                                r.get('both')))


if __name__ == '__main__':
    main()
