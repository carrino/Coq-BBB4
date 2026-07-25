#!/usr/bin/env python3
"""UNTRUSTED anchor-variant probe for the NOFIT counter cores.

fingerprint.py accepts only the *narrowest* anchor:

    (q, (enc(m) [++ 0*], S0, []))     or its right-side mirror

i.e. one side EMPTY, head BLANK, counter side EXACTLY Ip(m)/Jp(m) modulo
trailing blanks.  2299 of the 2480 counter cores fail that test.  This
probe relaxes the anchor along six independent axes and MEASURES how much
each relaxation buys:

    head1     head symbol is S1 instead of S0
    wall      the far side is a non-empty CONSTANT list (a wall)
    wallgrow  the far side is  pre ++ (G2)^(a2*m+b2) ++ tail  (growing comb)
    pre       the counter side carries a constant PREFIX before enc(m)
              (a=1 is exactly the "opposite parity / odd offset" reading)
    tail      the counter side carries a constant SUFFIX after enc(m)
              that is not the bare [S1] terminator
    comb      the counter side carries (G)^(alpha*m+beta) between the
              prefix and enc(m) -- the Interleave_18 "comb" families
    k3/k4/..  the digit block has period != 2
    code      the digit blocks are not the Ip/Jp pair {(1,0),(1,1)}
    rev       the counter reads MSB-nearest instead of LSB-nearest

The model that is fitted, for a group of anchor snapshots sharing a state
q and a head symbol h:

    counter side  X(m) = PRE ++ G^(alpha*m+beta) ++ B_{b0} B_{b1} .. B_{b(j-1)} ++ TAIL
    far side      W(m) = PRE2 ++ G2^(alpha2*m+beta2) ++ TAIL2
    with m = v0 + t  (t = index of the snapshot inside its group),
         j = bitlen(m)-1,  b_i = bit i of m,  |B_0| = |B_1| = k.

NOTHING here is trusted: it only tells the emitter what shape to aim the
Coq template at.  The kernel re-checks every board.
"""
import sys, os, json, random
from collections import defaultdict, Counter
from concurrent.futures import ProcessPoolExecutor

# ---------------------------------------------------------------- machine

def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab


def simulate(spec, T=40000, cap=400):
    """Run from the blank tape; snapshot every visit of every (state,head)
    up to `cap` visits.  Sides are returned nearest-cell-first with the
    far blanks stripped."""
    tab = parse(spec)
    N = 2 * T + 16
    tape = bytearray(N)
    pos = T + 8
    lo, hi = pos, pos + 1
    q = 0
    snaps = defaultdict(list)
    for t in range(T):
        h = tape[pos]
        e = tab[(q, h)]
        if e is None:
            return snaps, 'HALT'
        lst = snaps[(q, h)]
        if len(lst) < cap:
            L = bytes(tape[lo:pos])[::-1].rstrip(b'\0')
            R = bytes(tape[pos + 1:hi]).rstrip(b'\0')
            lst.append((t, L, R))
        w, d, ns = e
        tape[pos] = w
        q = ns
        pos += d
        if pos < lo:
            lo = pos
        if pos >= hi:
            hi = pos + 1
    return snaps, 'RUN'


# ---------------------------------------------------------------- helpers

def ispow2(x):
    return x > 0 and (x & (x - 1)) == 0


def divisors(n, cap=12):
    return [g for g in range(1, min(n, cap) + 1) if n % g == 0]


def infer_values(lengths, maxv0=1 << 14):
    """From the length sequence of the counter side, recover (v0, d, k):
    len_t = c + d*(v0+t) + k*(bitlen(v0+t)-1).  Returns a list of
    (v0, d, k) candidates."""
    n = len(lengths)
    if n < 8:
        return []
    diffs = [lengths[i + 1] - lengths[i] for i in range(n - 1)]
    ds = sorted(set(diffs))
    if len(ds) != 2:
        return []
    d, dk = ds
    k = dk - d
    if d < 0 or k <= 0 or k > 8 or d > 40:
        return []
    J = [i for i, x in enumerate(diffs) if x == dk]
    cand = []
    if len(J) >= 2:
        gap = J[1] - J[0]
        if ispow2(gap):
            e = gap.bit_length() - 1
            v0 = (1 << e) - J[0] - 1
            if v0 >= 1:
                cand.append(v0)
    else:
        for e in range(1, 24):
            v0 = (1 << e) - J[0] - 1
            if 1 <= v0 <= maxv0:
                cand.append(v0)
    out = []
    Js = set(J)
    for v0 in cand:
        ok = True
        for i in range(n - 1):
            if ispow2(v0 + i + 1) != (i in Js):
                ok = False
                break
        if not ok:
            continue
        c0 = lengths[0] - d * v0 - k * ((v0).bit_length() - 1)
        for i in range(n):
            v = v0 + i
            if lengths[i] - d * v - k * (v.bit_length() - 1) != c0:
                ok = False
                break
        if ok:
            out.append((v0, d, k))
    return out


def affine(us, vs):
    """u_t = alpha*v_t + beta with integer alpha>=0 -- or None."""
    if len(set(vs)) < 2:
        return None
    v0, u0 = vs[0], us[0]
    for i in range(1, len(vs)):
        if vs[i] != v0:
            num, den = us[i] - u0, vs[i] - v0
            if den == 0 or num % den:
                return None
            alpha = num // den
            break
    else:
        return None
    if alpha < 0:
        return None
    beta = u0 - alpha * v0
    for u, v in zip(us, vs):
        if u != alpha * v + beta:
            return None
    return alpha, beta


def greedy_reps(Y, a, G):
    g = len(G)
    r = 0
    while Y[a + r * g: a + (r + 1) * g] == G:
        r += 1
    return r


AMAX = 8

# ---------------------------------------------------------------- fitting

def fit_counter(Xs, vs, d, k):
    """All structural fits of the counter side.  Yields dicts."""
    out = []
    js = [v.bit_length() - 1 for v in vs]
    for orient in ('dir', 'rev'):
        Ys = Xs if orient == 'dir' else [X[::-1] for X in Xs]
        Y0 = Ys[0]
        gopts = [0] if d == 0 else divisors(d)
        for g in gopts:
            for a in range(0, AMAX + 1):
                if any(len(Y) < a + g for Y in Ys):
                    continue
                pre = Y0[:a]
                if any(Y[:a] != pre for Y in Ys):
                    continue
                if g == 0:
                    us = [0] * len(Ys)
                    G = b''
                    alpha, beta = 0, 0
                else:
                    G = Y0[a:a + g]
                    if len(G) < g:
                        continue
                    us = [greedy_reps(Y, a, G) for Y in Ys]
                    ab = affine(us, vs)
                    if ab is None or ab[0] != d // g:
                        continue
                    alpha, beta = ab
                Zs = [Ys[i][a + g * us[i]:] for i in range(len(Ys))]
                B = {}
                bad = False
                for i, Z in enumerate(Zs):
                    if len(Z) < k * js[i]:
                        bad = True
                        break
                    for bi in range(js[i]):
                        blk = Z[bi * k:(bi + 1) * k]
                        bit = (vs[i] >> bi) & 1
                        if bit in B:
                            if B[bit] != blk:
                                bad = True
                                break
                        else:
                            B[bit] = blk
                    if bad:
                        break
                if bad or 0 not in B or 1 not in B or B[0] == B[1]:
                    continue
                tails = set(Zs[i][k * js[i]:] for i in range(len(Zs)))
                if len(tails) != 1:
                    continue
                tail = tails.pop()
                out.append(dict(orient=orient, a=a, pre=pre, g=g, G=G,
                                alpha=alpha, beta=beta, k=k,
                                B0=B[0], B1=B[1], tail=tail))
    return out


def fit_wall(Ws, vs):
    """far side = PRE2 ++ G2^(alpha2*v+beta2) ++ TAIL2 (alpha2 may be 0)."""
    L = [len(W) for W in Ws]
    if len(set(L)) == 1 and len(set(Ws)) == 1:
        return dict(kind='const', W=Ws[0])
    v0 = vs[0]
    if len(set(vs)) < 2:
        return None
    num, den = L[1] - L[0], vs[1] - vs[0]
    if den == 0 or num % den or num < 0:
        return None
    A2 = num // den
    if A2 == 0:
        return None
    c2 = L[0] - A2 * v0
    if any(L[i] - A2 * vs[i] != c2 for i in range(len(Ws))):
        return None
    for g2 in divisors(A2):
        for a2 in range(0, AMAX + 1):
            if any(len(W) < a2 + g2 for W in Ws):
                continue
            pre2 = Ws[0][:a2]
            if any(W[:a2] != pre2 for W in Ws):
                continue
            G2 = Ws[0][a2:a2 + g2]
            us = [greedy_reps(W, a2, G2) for W in Ws]
            ab = affine(us, vs)
            if ab is None or ab[0] != A2 // g2:
                continue
            tails = set(Ws[i][a2 + g2 * us[i]:] for i in range(len(Ws)))
            if len(tails) != 1:
                continue
            return dict(kind='comb', pre=pre2, g=g2, G=G2,
                        alpha=ab[0], beta=ab[1], tail=tails.pop())
    return None


IPJP = {(b'\x01\x00', b'\x01\x01'), (b'\x01\x01', b'\x01\x00')}


def flags_of(fit):
    f = set()
    if fit['head'] == 1:
        f.add('head1')
    wk = fit['wall']
    if wk['kind'] == 'const':
        if wk['W']:
            f.add('wall')
    else:
        f.add('wallgrow')
    if fit['a'] > 0:
        f.add('pre')
    if fit['g'] > 0:
        f.add('comb')
    if fit['orient'] == 'rev':
        f.add('rev')
    if fit['k'] != 2:
        f.add('k%d' % fit['k'])
    if (fit['B0'], fit['B1']) not in IPJP:
        f.add('code')
    if fit['tail'] != b'\x01':
        f.add('tail')
    return f


COST = {'head1': 1, 'wall': 2, 'pre': 2, 'tail': 2, 'code': 3, 'rev': 4,
        'k3': 5, 'k4': 5, 'k5': 6, 'k6': 6, 'k7': 6, 'k8': 6,
        'comb': 8, 'wallgrow': 9}


def cost(fs):
    return sum(COST.get(x, 7) for x in fs)


def show(b):
    return '[' + ';'.join('S%d' % c for c in b) + ']'


def anchor_formula(fit):
    """Human/Coq-ish rendering of the anchor."""
    st = 'St' + 'ABCD'[fit['state']]
    k = fit['k']
    B0, B1 = fit['B0'], fit['B1']
    if (B0, B1) == (b'\x01\x00', b'\x01\x01'):
        enc = 'Ip m'
    elif (B0, B1) == (b'\x01\x01', b'\x01\x00'):
        enc = 'Jp m'
    else:
        enc = 'E m  (xO->%s, xI->%s, xH->%s)' % (show(B0), show(B1),
                                                 show(fit['tail']))
    parts = []
    if fit['a']:
        parts.append(show(fit['pre']))
    if fit['g']:
        parts.append('rep %s (%d*m%+d)' % (show(fit['G']), fit['alpha'],
                                           fit['beta']))
    parts.append(enc)
    if fit['tail'] != b'\x01' and enc.startswith(('Ip', 'Jp')):
        parts.append(show(fit['tail'][1:]) if fit['tail'][:1] == b'\x01'
                     else '<<tail %s>>' % show(fit['tail']))
    cs = ' ++ '.join(p for p in parts if p != '[]')
    wk = fit['wall']
    if wk['kind'] == 'const':
        ws = show(wk['W'])
    else:
        ws = ' ++ '.join([show(wk['pre'])] * bool(wk['pre']) +
                         ['rep %s (%d*m%+d)' % (show(wk['G']), wk['alpha'],
                                                wk['beta'])] +
                         [show(wk['tail'])])
    hd = 'S%d' % fit['head']
    if fit['side'] == 'L':
        return '(%s, (%s, %s, %s))' % (st, cs, hd, ws)
    return '(%s, (%s, %s, %s))' % (st, ws, hd, cs)


def struct_key(fit):
    """Canonical structure descriptor used for clustering."""
    wk = fit['wall']
    w = ('W' + show(wk['W'])) if wk['kind'] == 'const' else \
        ('Wcomb%s^%dm%+d%s' % (show(wk['G']), wk['alpha'], wk['beta'],
                               show(wk['tail'])))
    return '|'.join([
        'side=' + fit['side'], 'head=S%d' % fit['head'], 'or=' + fit['orient'],
        'pre=' + show(fit['pre']),
        'comb=' + ('-' if not fit['g'] else '%s^%dm%+d' % (show(fit['G']),
                                                           fit['alpha'],
                                                           fit['beta'])),
        'k=%d' % fit['k'], 'B0=' + show(fit['B0']), 'B1=' + show(fit['B1']),
        'tail=' + show(fit['tail']), w])


# ---------------------------------------------------------------- per machine

MINSNAP = 10
OFFSETS = (0, 1, 2, 3, 4, 6, 8, 12, 16)
STRIDES = (1, 2, 3)
WINDOW = 48
VERIFY = 220


def predict(fit, v):
    """Reconstruct the predicted (counter side, far side) at counter value v."""
    j = v.bit_length() - 1
    blocks = b''.join(fit['B1'] if (v >> i) & 1 else fit['B0']
                      for i in range(j))
    Y = (fit['pre'] + fit['G'] * (fit['alpha'] * v + fit['beta'])
         + blocks + fit['tail'])
    if fit['orient'] == 'rev':
        Y = Y[::-1]
    wk = fit['wall']
    if wk['kind'] == 'const':
        W = wk['W']
    else:
        W = wk['pre'] + wk['G'] * (wk['alpha'] * v + wk['beta']) + wk['tail']
    return Y, W


def verify(fit, seg):
    """How many leading snapshots of `seg` the model reproduces exactly."""
    n = 0
    for i, (t, cs, ws) in enumerate(seg):
        Y, W = predict(fit, fit['v0'] + i)
        if Y != cs or W != ws:
            break
        n += 1
    return n


def runlengths(words):
    """[(word length, how many consecutive snapshots had it)] """
    runs = []
    for w in words:
        L = len(w)
        if runs and runs[-1][0] == L:
            runs[-1][1] += 1
        else:
            runs.append([L, 1])
    return runs


def residual_class(spec, T=400000, cap=400):
    """Coarse taxonomy of the machines no anchor variant fits: which
    state-space does the anchor family actually enumerate?"""
    snaps, status = simulate(spec, T=T, cap=cap)
    best = ('OTHER', None, 0)
    for (q, h), lst in snaps.items():
        for side in ('L', 'R'):
            grp = defaultdict(list)
            for (t, L, R) in lst:
                cs, ws = (L, R) if side == 'L' else (R, L)
                grp[ws].append((t, cs))
            for ws, g in grp.items():
                if len(g) < 12:
                    continue
                words = [c for (_, c) in g]
                ts = [t for (t, _) in g]
                runs = runlengths(words)
                mid = [r[1] for r in runs[1:-1]]
                distinct = len(set(words)) == len(words)
                tag = None
                if len(mid) >= 3 and max(mid) > 1:
                    for c in (2, 3, 4, 5):
                        if all(mid[i + 1] == c * mid[i]
                               for i in range(len(mid) - 1)):
                            tag = 'BASE%dSPACE' % c
                            break
                    if tag is None and all(
                            mid[i + 1] == mid[i] + mid[i - 1]
                            for i in range(1, len(mid) - 1)) and mid[-1] > mid[0]:
                        tag = 'FIBSPACE'
                if tag is None and len(ts) >= 8 and max(r[1] for r in runs) == 1:
                    gr = [ts[i + 1] / max(1, ts[i]) for i in range(4, len(ts) - 1)]
                    tag = ('EXPONENTIAL' if gr and min(gr) > 1.4
                           else 'LINEARSWEEP')
                if tag is None:
                    continue
                score = len(g) + 1000 * (tag != 'OTHER') + 500 * distinct
                if score > best[2]:
                    best = (tag, dict(state='ABCD'[q], head=h, side=side,
                                      n=len(g), distinct=distinct,
                                      runs=[r[1] for r in runs[:12]]), score)
    return {'residual': best[0], 'rdetail': best[1]}


def probe(spec):
    snaps, status = simulate(spec)
    rec = {'m': spec, 'status': status}
    if status == 'HALT':
        rec['cls'] = 'HALT'
        return rec
    allfits = []
    for (q, h), lst in snaps.items():
        for side in ('L', 'R'):
            # group snapshots by the far side (constant-wall pass) and also
            # take the ungrouped stream (growing-wall pass)
            groups = defaultdict(list)
            for (t, L, R) in lst:
                cs, ws = (L, R) if side == 'L' else (R, L)
                groups[ws].append((t, cs, ws))
            streams = [g for g in groups.values() if len(g) >= MINSNAP]
            allst = [(t, (L if side == 'L' else R), (R if side == 'L' else L))
                     for (t, L, R) in lst]
            if len(allst) >= MINSNAP and len(groups) > 1:
                streams.append(allst)
            for stream0 in streams:
                for stride in STRIDES:
                    got = False
                    for off in OFFSETS:
                        stream = stream0[off::stride]
                        if len(stream) < MINSNAP:
                            break
                        seg = stream[:WINDOW]
                        Xs = [x[1] for x in seg]
                        Ws = [x[2] for x in seg]
                        for (v0, d, k) in infer_values([len(X) for X in Xs]):
                            vs = [v0 + i for i in range(len(Xs))]
                            wf = fit_wall(Ws, vs)
                            if wf is None:
                                continue
                            for f in fit_counter(Xs, vs, d, k):
                                f.update(state=q, head=h, side=side, wall=wf,
                                         v0=v0, nsnap=len(seg), t0=seg[0][0],
                                         stride=stride)
                                f['nver'] = verify(f, stream[:VERIFY])
                                if f['nver'] < len(seg):
                                    continue
                                allfits.append(f)
                                got = True
                        if got:
                            break
                    if got:
                        break
    if not allfits:
        rec['cls'] = 'UNSTRUCTURED'
        rec['keys'] = len(snaps)
        rec.update(residual_class(spec))
        return rec
    scored = sorted(allfits, key=lambda f: (cost(flags_of(f)), -f['nsnap'],
                                            f['a'], f['t0']))
    best = scored[0]
    rec['cls'] = 'FIT'
    rec['flags'] = sorted(flags_of(best))
    rec['cost'] = cost(flags_of(best))
    rec['anchor'] = anchor_formula(best)
    rec['struct'] = struct_key(best)
    rec['v0'] = best['v0']
    rec['nsnap'] = best['nsnap']
    rec['nver'] = best['nver']
    rec['stride'] = best['stride']
    rec['state'] = 'ABCD'[best['state']]
    rec['head'] = best['head']
    rec['side'] = best['side']
    rec['k'] = best['k']
    # every distinct relaxation-set achievable, for leave-one-out counting
    rec['flagsets'] = sorted(set('+'.join(sorted(flags_of(f)))
                                 for f in allfits))
    return rec


# ---------------------------------------------------------------- driver

AXES = ['head1', 'wall', 'pre', 'tail', 'code', 'rev', 'comb', 'wallgrow',
        'k1', 'k3', 'k4', 'k5', 'k6']


def report(path):
    rs = [json.loads(l) for l in open(path)]
    n = len(rs)
    cls = Counter(r['cls'] for r in rs)
    print('sample %d   %s' % (n, dict(cls)))
    fits = [r for r in rs if r['cls'] == 'FIT']
    print('\n== minimal relaxation set per machine (best fit) ==')
    for fs, c in Counter('+'.join(r['flags']) or '(none)'
                         for r in fits).most_common():
        print('%6d  %s' % (c, fs))
    print('\n== single-axis coverage: machines fittable using ONLY this axis ==')
    base = sum(1 for r in fits if any(f == '' for f in r['flagsets']))
    print('%6d  (baseline: exact fingerprint.py anchor)' % base)
    for ax in AXES:
        c = sum(1 for r in fits
                if any(set(f.split('+')) - {''} <= {ax} for f in r['flagsets']))
        print('%6d  +%s' % (c, ax))
    print('\n== cumulative ladder (axes enabled left to right) ==')
    order = ['head1', 'wall', 'tail', 'pre', 'code', 'k1', 'k3', 'k4', 'k5',
             'k6', 'rev', 'comb', 'wallgrow']
    en = set()
    print('%6d  %s' % (base, 'baseline'))
    for ax in order:
        en.add(ax)
        c = sum(1 for r in fits
                if any(set(f.split('+')) - {''} <= en for f in r['flagsets']))
        print('%6d  +%s' % (c, ax))
    print('\n== leave-one-out: machines LOST if this axis is forbidden ==')
    full = set(AXES)
    tot = len(fits)
    for ax in AXES:
        en = full - {ax}
        c = sum(1 for r in fits
                if any(set(f.split('+')) - {''} <= en for f in r['flagsets']))
        print('%6d  -%s' % (tot - c, ax))
    un = [r for r in rs if r['cls'] == 'UNSTRUCTURED']
    print('\n== digit codes needed (k, B0, B1, terminator convention) ==')
    codes, walls = Counter(), Counter()
    for r in fits:
        d = dict(p.split('=', 1) for p in r['struct'].split('|') if '=' in p)
        b0, b1, tl = (x[1:-1].split(';') if x != '[]' else []
                      for x in (d['B0'], d['B1'], d['tail']))
        if tl[:len(b1)] == b1:
            term, suf = 'FULL', tl[len(b1):]
        else:
            cp = []
            for a, b in zip(b0, b1):
                if a != b:
                    break
                cp.append(a)
            if cp and tl[:len(cp)] == cp:
                term, suf = 'TRUNC', tl[len(cp):]
            else:
                term, suf = 'RAW' + d['tail'], []
        codes[(int(d['k']), d['B0'], d['B1'], term, ';'.join(suf))] += 1
        walls[r['struct'].split('|')[-1]] += 1
    for (k, B0, B1, term, suf), c in codes.most_common(24):
        print('%6d  k=%d xO->%s xI->%s top=%s%s' %
              (c, k, B0, B1, term, ('  +suffix[%s]' % suf) if suf else ''))
    print('\n== far-side wall values ==')
    for w, c in walls.most_common(14):
        print('%6d  %s' % (c, w))
    print('\n== residual taxonomy (%d machines no variant fits) ==' % len(un))
    for t, c in Counter(r.get('residual', '?') for r in un).most_common():
        print('%6d  %s' % (c, t))
        for r in un:
            if r.get('residual') == t:
                print('        eg %s  %s' % (r['m'], r.get('rdetail')))
                break
    print('\n== structure clusters (best fit), top 40 ==')
    cl = defaultdict(list)
    for r in fits:
        cl[r['struct']].append(r)
    for st, g in sorted(cl.items(), key=lambda x: -len(x[1]))[:40]:
        ex = sorted(g, key=lambda r: -r['nver'])[0]
        print('%5d  %s' % (len(g), st))
        print('        eg %s   %s  v0=%d nver=%d' %
              (ex['m'], ex['anchor'], ex['v0'], ex['nver']))
    print('\n== anchor-form clusters (state-agnostic), top 30 ==')
    cl2 = defaultdict(list)
    for r in fits:
        cl2[r['anchor'].split(', ', 1)[1]].append(r)
    for st, g in sorted(cl2.items(), key=lambda x: -len(x[1]))[:30]:
        print('%5d  %s   eg %s' % (len(g), st, g[0]['m']))


def main():
    if sys.argv[1] == 'report':
        return report(sys.argv[2])
    src = sys.argv[1]
    out = sys.argv[2]
    n = int(sys.argv[3]) if len(sys.argv) > 3 else 300
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 12345
    ms = [x.strip() for x in open(src) if x.strip()]
    if 0 < n < len(ms):
        random.Random(seed).shuffle(ms)
        ms = ms[:n]
    with open(out, 'w') as f, ProcessPoolExecutor(max_workers=4) as ex:
        for i, r in enumerate(ex.map(probe, ms, chunksize=4)):
            f.write(json.dumps(r) + '\n')
            if (i + 1) % 50 == 0:
                f.flush()
                sys.stderr.write('%d/%d\n' % (i + 1, len(ms)))
    sys.stderr.write('DONE %d\n' % len(ms))


if __name__ == '__main__':
    main()
