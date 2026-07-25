#!/usr/bin/env python3
"""UNTRUSTED comb-family probe for the (4,2) BBB residue.

Tests the NOFIT counter machines (the ones fingerprint.py could not fit to the
comb-free anchor  Cc p = (edge, (Jp p ++ [S0], S0, [])) ) against COMB-style
anchors, i.e. the shape already boarded by

    theories/Machines/Counters/Interleave_18.v   1RB0RD_1LB0LC_1LD1LB_1RA1RD
    theories/Machines/Counters/Interleave_35.v   1RB1RA_0RC0RA_1LC0LD_1LA1LC

whose anchor is

    Cc p = (StA, (S1 :: rep [S0;S1;S1] (2 * Pos.to_nat p) ++ Ip p, S0, []))

read on the LEFT list nearest-cell-first:  prefix [S1], then k = 2p copies of
the period-3 comb block [S0;S1;S1], then the interleaved counter Ip p, blank
head, EMPTY right list.

The probe generalises that to

    <prefix P>  <block B>^k  <counter E(p)>      (+ trailing blanks)

with |P| in 0..PREMAX, |B| in 1..DMAX, E in {Ip, Jp} (or an extended
2-cell interleave family with --wide), and reports the fitted linear relation
k = a*p + b together with the anchor state / head symbol / side.

It also measures the LAP GEOMETRY between consecutive anchors: the number of
head-direction turnarounds (2 per sweep) and where they sit, which is what
distinguishes the one-sweep comb-free template (Interleave_TGT.v) from the
two-sweep comb lap (Interleave_18.v / _35.v).

NOTHING HERE IS TRUSTED -- the Coq kernel re-checks every board this feeds.
"""
import sys, os, json, argparse
from concurrent.futures import ProcessPoolExecutor

# ---------------------------------------------------------------- machines

def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab

# ---------------------------------------------------------------- encodings
# generic 2-cell interleave: every low bit contributes one pad cell and one
# data cell (possibly complemented), closed by a terminator.
#   Ip (ILCounter) = pad 1 first,  data = bit,        term [1]
#   Jp (JpCounter) = pad 1 first,  data = 1 - bit,    term [1]

def mk_enc(pad, padfirst, inv, term):
    def f(m):
        out = []
        while m > 1:
            b = (m & 1) ^ inv
            out += ([pad, b] if padfirst else [b, pad])
            m >>= 1
        return out + list(term)
    return f

ENC_NARROW = {
    'Ip': mk_enc(1, True, 0, [1]),
    'Jp': mk_enc(1, True, 1, [1]),
}

def mk_enc3(pad, padfirst, inv):
    """3-cell-per-bit interleave: a 2-cell pad block plus the data cell."""
    def f(m):
        out = []
        while m > 1:
            b = (m & 1) ^ inv
            out += (list(pad) + [b] if padfirst else [b] + list(pad))
            m >>= 1
        return out
    return f

def enc_wide():
    d = dict(ENC_NARROW)
    for pad in (0, 1):
        for pf in (True, False):
            for inv in (0, 1):
                for term in ([1], [0], [], [1, 1], [1, 0], [0, 1]):
                    n = 'P%d%s%dT%s' % (pad, 'F' if pf else 'B', inv,
                                        ''.join(map(str, term)) or 'e')
                    d.setdefault(n, mk_enc(pad, pf, inv, term))
    if WIDE3:
        for pad in ((0, 0), (0, 1), (1, 0), (1, 1)):
            for pf in (True, False):
                for inv in (0, 1):
                    d.setdefault('T%d%d%s%d' % (pad[0], pad[1],
                                                'F' if pf else 'B', inv),
                                 mk_enc3(pad, pf, inv))
    return d

def build_table(encs, bound=1 << 13):
    """tuple(cells) -> list of (encname, value); shortest-first per encoding."""
    tab = {}
    for name, f in encs.items():
        for m in range(1, bound):
            t = tuple(f(m))
            tab.setdefault(t, [])
            if not any(n == name for n, _ in tab[t]):
                tab[t].append((name, m))
    return tab

WIDE3 = False
TAB = None
RMAX = 44          # longest residue (counter) we will consider
PREMAX = 4
SUBN = 60          # anchors used per (key, gap): the last SUBN, biggest counters
DMAX = 6

def strip_tail0(t):
    i = len(t)
    while i and t[i - 1] == 0:
        i -= 1
    return t[:i]

# ---------------------------------------------------------------- simulator

GAPMAX = 2       # anchors keep the head within GAPMAX blanks of the data
DEBRIS = 0       # cells of leftover junk tolerated on the far side of the head

def sim_snaps(spec, T, cap=3000, N=1 << 15):
    """Run from blank; collect anchor snapshots.

    An anchor candidate is a configuration where one side of the head is
    entirely blank and the other is not.  Key = (state, head symbol, side)
    where side 'L' = data on the left list (right blank), 'R' = mirror.
    Snapshot = the data side as a nearest-cell-first tuple.
    Also records the head-position trace for lap geometry.
    """
    tab = parse(spec)
    tape = bytearray(N)
    pos = N // 2
    lmin = rmax = None          # extent of the currently-nonblank cells
    q = 0
    snaps = {}
    trace = []                  # (t, pos) sampled every step (bounded)
    for t in range(T):
        h = tape[pos]
        e = tab[(q, h)]
        if e is None:
            return None, 'HALT', None
        if rmax is not None:
            if rmax - pos <= DEBRIS and lmin < pos:
                key = (q, h, 'L', bytes(tape[pos + 1:rmax + 1]))
                lst = snaps.setdefault(key, [])
                if len(lst) < cap:
                    s = bytes(tape[lmin:pos])[::-1]
                    g = 0
                    while g < len(s) and s[g] == 0:
                        g += 1
                    if g <= GAPMAX and (
                            not lst or lst[-1][1] != s[g:] or lst[-1][2] != g):
                        lst.append((t, s[g:], g))
            elif pos - lmin <= DEBRIS and rmax > pos:
                key = (q, h, 'R', bytes(tape[lmin:pos])[::-1])
                lst = snaps.setdefault(key, [])
                if len(lst) < cap:
                    s = bytes(tape[pos + 1:rmax + 1])
                    g = 0
                    while g < len(s) and s[g] == 0:
                        g += 1
                    if g <= GAPMAX and (
                            not lst or lst[-1][1] != s[g:] or lst[-1][2] != g):
                        lst.append((t, s[g:], g))
        w, d, ns = e
        if w != h:
            tape[pos] = w
        if w:
            if rmax is None:
                lmin = rmax = pos
            else:
                if pos > rmax:
                    rmax = pos
                if pos < lmin:
                    lmin = pos
        elif h:                                  # erased a 1
            if pos == rmax and pos == lmin:
                lmin = rmax = None
            elif pos == rmax:
                rmax = tape.rfind(1, lmin, pos)
            elif pos == lmin:
                lmin = tape.find(1, pos + 1, rmax + 1)
        q = ns
        pos += d
        if len(trace) < T:
            trace.append(pos)
        if pos <= 8 or pos >= N - 8:
            return snaps, 'OOB', trace
    return snaps, 'OK', trace

# ---------------------------------------------------------------- matching

K0 = False        # also accept comb-free (k = 0) anchors: prefix ++ counter

def cands_from(s):
    """All (prelen, d, block, encname, k, value) parses of one snapshot."""
    out = []
    n = len(s)
    for prelen in range(0, PREMAX + 1):
        if n < prelen + 2:
            break
        if K0 and n - prelen <= RMAX:
            res = strip_tail0(tuple(s[prelen:]))
            for name, v in TAB.get(res, ()):
                out.append((prelen, 0, (), name, 0, v))
        for d in range(1, DMAX + 1):
            if n < prelen + 2 * d + 1:
                continue
            B = s[prelen:prelen + d]
            kmax = 1
            while s[prelen + kmax * d:prelen + (kmax + 1) * d] == B:
                kmax += 1
            if kmax < 2:
                continue
            for k in range(kmax, 1, -1):
                r = n - prelen - k * d
                if r > RMAX:
                    break
                res = strip_tail0(tuple(s[prelen + k * d:]))
                for name, v in TAB.get(res, ()):
                    out.append((prelen, d, tuple(B), name, k, v))
    return out


def apply_tpl(s, tpl):
    """(k, value) for a fixed template, largest comb that leaves a counter."""
    P, d, B, name = tpl
    prelen = len(P)
    n = len(s)
    if tuple(s[:prelen]) != P:
        return None
    if d == 0:
        if n - prelen > RMAX or n <= prelen:
            return None
        res = strip_tail0(tuple(s[prelen:]))
        for nm, v in TAB.get(res, ()):
            if nm == name:
                return (0, v)
        return None
    if n < prelen + 2 * d + 1 or tuple(s[prelen:prelen + d]) != B:
        return None
    kmax = 1
    while tuple(s[prelen + kmax * d:prelen + (kmax + 1) * d]) == B:
        kmax += 1
    for k in range(kmax, 1, -1):
        r = n - prelen - k * d
        if r > RMAX:
            break
        res = strip_tail0(tuple(s[prelen + k * d:]))
        for nm, v in TAB.get(res, ()):
            if nm == name:
                return (k, v)
    return None


def score_tpl(snaps, tpl, gap):
    P, d, B, name = tpl
    ks, vs, ts, hits = [], [], [], 0
    sub = [x for x in snaps if x[2] == gap][-SUBN:]
    for (t, s, g) in sub:
        r = apply_tpl(s, tpl)
        if r is None:
            continue
        hits += 1
        ks.append(r[0]); vs.append(r[1]); ts.append(t)
    if len(vs) < 6:
        return None
    inc = sum(1 for a, b in zip(vs, vs[1:]) if b == a + 1)
    frac = inc / (len(vs) - 1)
    hit = hits / max(1, len(sub))
    if frac < 0.75 or hit < 0.4:
        return None
    # comb growth: fit k = a*p + b on the incrementing part
    pts = [(v, k) for v, k in zip(vs, ks)]
    a = b = None
    exact = False
    if len(pts) >= 2 and pts[-1][0] != pts[0][0]:
        a = (pts[-1][1] - pts[0][1]) / (pts[-1][0] - pts[0][0])
        b = pts[0][1] - a * pts[0][0]
        exact = all(abs(a * v + b - k) < 1e-9 for v, k in pts)
    return {'pre': list(P), 'gap': gap, 'd': d, 'block': list(B), 'enc': name,
            'frac': round(frac, 3), 'hit': round(hit, 3), 'n': len(vs),
            'p0': vs[0], 'k0': ks[0], 'pk': vs[-1], 'kk': ks[-1],
            'a': a, 'b': b, 'exact': exact, 'ts': ts[:6],
            'score': frac * hit * len(vs)}


def all_for_key(snaps):
    """snaps = list of (t, bytes, gap).  Every template that fits, best-first."""
    if len(snaps) < 8:
        return []
    import collections
    bygap = collections.Counter(x[2] for x in snaps)
    out = []
    for gap, cnt in bygap.most_common(3):
        if cnt < 8:
            continue
        sub = [x for x in snaps if x[2] == gap][-SUBN:]
        refs = [sub[-1], sub[len(sub) * 3 // 4], sub[len(sub) // 2]]
        seen = set()
        for (_, s, _g) in refs:
            for (prelen, d, B, name, k, v) in cands_from(s):
                tpl = (tuple(s[:prelen]), d, B, name)
                if tpl in seen:
                    continue
                seen.add(tpl)
                r = score_tpl(snaps, tpl, gap)
                if r:
                    out.append(r)
    out.sort(key=lambda r: -r['score'])
    return out

# ---------------------------------------------------------------- geometry

def lap_geometry(trace, ts):
    """Turnaround structure of one lap, between two consecutive anchor times."""
    if len(ts) < 3:
        return None
    out = []
    for i in (len(ts) - 3, len(ts) - 2):
        t0, t1 = ts[i], ts[i + 1]
        if t1 <= t0 or t1 >= len(trace):
            continue
        seg = trace[t0:t1 + 1]
        lo, hi = min(seg), max(seg)
        turns = []
        for j in range(1, len(seg) - 1):
            if (seg[j] - seg[j - 1]) * (seg[j + 1] - seg[j]) < 0:
                where = ('R' if seg[j] >= hi - 1 else
                         'L' if seg[j] <= lo + 1 else 'M')
                turns.append(where)
        out.append({'steps': t1 - t0, 'span': hi - lo,
                    'turns': len(turns), 'sweeps': (len(turns) + 1) // 2,
                    'pat': ''.join(turns)})
    return out

# ---------------------------------------------------------------- per-machine

def probe(spec, T=30000):
    snaps, st, trace = sim_snaps(spec, T)
    if snaps is None:
        return {'m': spec, 'cls': st}
    fits = []
    for key, lst in snaps.items():
        q, h, side, deb = key
        for r in all_for_key(lst)[:6]:
            ts = r.pop('ts')
            r['geo'] = lap_geometry(trace, ts)
            r.update({'edge': 'ABCD'[q], 'head': h, 'growth': side,
                      'debris': list(deb)})
            fits.append(r)
    if not fits:
        return {'m': spec, 'cls': 'NOCOMB', 'sim': st,
                'nkeys': len(snaps),
                'maxsnap': max((len(v) for v in snaps.values()), default=0)}
    fits.sort(key=lambda r: -r['score'])
    for r in fits:
        r.pop('score')
    return {'m': spec, 'cls': 'COMB', 'sim': st, 'nfit': len(fits),
            'best': fits[0], 'fits': fits[:8]}

# ---------------------------------------------------------------- driver

def _init(wide, k0=False, debris=0, wide3=False):
    global TAB, K0, DEBRIS, WIDE3
    WIDE3 = wide3
    K0 = k0
    DEBRIS = debris
    TAB = build_table(enc_wide() if wide else ENC_NARROW)

_STEPS = 30000

def _initw(wide, steps, k0, debris, wide3):
    global _STEPS
    _STEPS = steps
    _init(wide, k0, debris, wide3)

def _work(spec):
    return probe(spec, _STEPS)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('src')
    ap.add_argument('out')
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--offset', type=int, default=0)
    ap.add_argument('--steps', type=int, default=30000)
    ap.add_argument('--wide', action='store_true')
    ap.add_argument('--k0', action='store_true',
                    help='also accept comb-free (k=0) prefix++counter anchors')
    ap.add_argument('--wide3', action='store_true',
                    help='also try 3-cell-per-bit interleave encodings')
    ap.add_argument('--debris', type=int, default=0,
                    help='tolerate this many junk cells on the far side')
    ap.add_argument('--jobs', type=int, default=4)
    a = ap.parse_args()
    ms = [x.strip() for x in open(a.src) if x.strip()]
    ms = ms[a.offset:]
    if a.limit:
        ms = ms[:a.limit]
    global _STEPS
    _STEPS = a.steps
    _init(a.wide, a.k0, a.debris, a.wide3)
    fn = _work
    with open(a.out, 'w') as f:
        if a.jobs > 1:
            with ProcessPoolExecutor(max_workers=a.jobs,
                                     initializer=_initw,
                                     initargs=(a.wide, a.steps, a.k0, a.debris, a.wide3)) as ex:
                for i, r in enumerate(ex.map(fn, ms, chunksize=4)):
                    f.write(json.dumps(r) + '\n')
                    if (i + 1) % 100 == 0:
                        f.flush(); sys.stderr.write('%d/%d\n' % (i + 1, len(ms)))
        else:
            for i, s in enumerate(ms):
                f.write(json.dumps(fn(s)) + '\n')
    sys.stderr.write('DONE %d\n' % len(ms))

if __name__ == '__main__':
    main()
