#!/usr/bin/env python3
"""UNTRUSTED wide anchor search + two-branch lap profile.

The emitter's derive_tail only ever looked for  enc(p) ++ tail ++ [S0]  at a
BLANK head under a single encoding.  This searches the real run for an anchor
family

    Cc p = (edge, (enc(p) ++ tail, head, far))

over edge in ABCD, enc in {Ip,Jp}, head in {S0,S1}, tail an arbitrary short
suffix READ OFF THE RUN (not assumed blank-terminated), and far side blank.

Then it measures BOTH lap branches -- interior (cview p = (j,Some q)) and
overflow (p = 2^k - 1) -- and reports whether each is AFFINE in j.  The Coq
template can only clone a machine whose BOTH branches are affine; the wave-8
docs only ever checked the interior.
"""
import json
import sys
from collections import defaultdict
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
        s = ''
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            s += e if e == '---' else e[0] + ('L' if e[1] == 'R' else 'R') + e[2]
        out.append(s)
    return '_'.join(out)


def Ip(m):
    out = []
    while m > 1:
        out += [1, m & 1]
        m >>= 1
    return out + [1]


def Jp(m):
    out = []
    while m > 1:
        out += [1, 1 - (m & 1)]
        m >>= 1
    return out + [1]


ENC = {'Ip': Ip, 'Jp': Jp}
MAXTAIL = 4


def carry(m):
    j = 0
    while (m >> j) & 1:
        j += 1
    return j, (m == (1 << j) - 1)


def strip0(l):
    i = len(l)
    while i > 0 and l[i - 1] == 0:
        i -= 1
    return list(l[:i])


def enc_tables(bound=1 << 14):
    """(enc,tail) -> {tuple(list): value} for every short tail."""
    tabs = {}
    for name, f in ENC.items():
        for tl in range(MAXTAIL + 1):
            for tv in range(1 << tl):
                tail = [(tv >> i) & 1 for i in range(tl)]
                d = {}
                m = 1
                while m < bound:
                    d[tuple(f(m) + tail)] = m
                    m += 1
                tabs[(name, tuple(tail))] = d
    return tabs


TABS = None


def scan(spec, T=200000):
    """One run; per (edge,head,enc,tail) key collect (step, value)."""
    global TABS
    if TABS is None:
        TABS = enc_tables()
    tab = parse(spec)
    q, l, h, r = 0, [], 0, []
    hits = defaultdict(list)
    for t in range(T):
        e = tab[(q, h)]
        if e is None:
            return None
        if not strip0(r):
            key0 = strip0(l)
            # try every (enc,tail) decode of this exact left list
            for (name, tail), d in TABS.items():
                v = d.get(tuple(key0))
                if v is not None and v > 1:
                    hits[(LAB[q], h, name, tail)].append((t, v))
        w, d, ns = e
        if d > 0:
            q, l, h, r = ns, [w] + l, (r[0] if r else 0), r[1:]
        else:
            q, l, h, r = ns, l[1:], (l[0] if l else 0), [w] + r
    return hits


def affine(pts):
    """pts: list of (j, steps).  Return (a,b) if steps = a + b*j, else None."""
    byj = defaultdict(set)
    for j, n in pts:
        byj[j].add(n)
    if any(len(v) > 1 for v in byj.values()):
        return None
    js = sorted(byj)
    if len(js) < 2:
        return None
    p = [(j, list(byj[j])[0]) for j in js]
    (j0, n0), (j1, n1) = p[0], p[1]
    if (n1 - n0) % (j1 - j0):
        return None
    b = (n1 - n0) // (j1 - j0)
    a = n0 - b * j0
    if b <= 0 or a + b * js[0] <= 0:
        return None                  # a lap cannot take <= 0 steps
    if all(n == a + b * j for j, n in p):
        return (a, b)
    return None


def profile(spec, T=200000):
    out = {'m': spec}
    hits = scan(spec, T)
    if hits is None:
        out['cls'] = 'HALT'
        return out
    best = None
    for key, evs in hits.items():
        first = {}
        for t, v in evs:
            if v not in first:
                first[v] = t
        vs = sorted(first)
        # Consecutive values ONLY where the machine reaches v+1 AFTER v.  The
        # same tape decodes under both Ip and Jp -- one ascending, one
        # descending -- so without the time check the descending reading scores
        # just as well and the affine fit comes back with a NEGATIVE slope.
        laps = [(v, first[v + 1] - first[v]) for v in vs
                if v + 1 in first and first[v + 1] > first[v]]
        if len(laps) < 8:
            continue
        inter = [(carry(v)[0], n) for v, n in laps if not carry(v)[1]]
        ovs = [(carry(v)[0], n) for v, n in laps if carry(v)[1]]
        ai = affine(inter)
        ao = affine(ovs) if len(set(j for j, _ in ovs)) >= 2 else None
        score = (2 if (ai and ao) else 1 if ai else 0, len(laps))
        rec = {'edge': key[0], 'head': key[1], 'enc': key[2],
               'tail': list(key[3]), 'nlaps': len(laps), 'p0': vs[0],
               'int_affine': ai, 'ov_affine': ao,
               'ov_pts': sorted(set(ovs))[:8]}
        if best is None or score > best[0]:
            best = (score, rec)
    if best is None:
        out['cls'] = 'NOANCHOR'
        return out
    out['cls'] = 'COUNTER'
    out.update(best[1])
    out['both'] = bool(best[1]['int_affine'] and best[1]['ov_affine'])
    return out


def analyse(spec):
    """Try the machine and its mirror; prefer a both-affine fit."""
    a = profile(spec)
    a['side'] = 'L'
    if a.get('both'):
        return a
    b = profile(mirror_spec(spec))
    b['side'] = 'R'
    b['m'] = spec
    b['mspec'] = mirror_spec(spec)
    if b.get('both'):
        return b
    # neither both-affine: return whichever got further
    ra = (a.get('cls') == 'COUNTER', bool(a.get('int_affine')))
    rb = (b.get('cls') == 'COUNTER', bool(b.get('int_affine')))
    return b if rb > ra else a


def main():
    src, dst = sys.argv[1], sys.argv[2]
    ms = [x.strip() for x in open(src) if x.strip()]
    if len(sys.argv) > 3:
        ms = ms[:int(sys.argv[3])]
    with open(dst, 'w') as f, ProcessPoolExecutor(max_workers=3) as ex:
        for i, r in enumerate(ex.map(analyse, ms, chunksize=2)):
            f.write(json.dumps(r) + '\n')
            if (i + 1) % 25 == 0:
                f.flush()
                sys.stderr.write('%d/%d\n' % (i + 1, len(ms)))
    sys.stderr.write('DONE %d\n' % len(ms))


if __name__ == '__main__':
    main()
