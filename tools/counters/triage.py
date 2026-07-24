#!/usr/bin/env python3
"""UNTRUSTED dynamics triage for the (4,2) BBB residue counter core.

For every machine in a spec list, simulate <= T steps from the blank tape
and measure DYNAMICS (not encoding):

  * halting;
  * exact in-place cycle (Brent, absolute configuration equality);
  * TRANSLATED cycle -- the sound "shifted window" criterion:
        state(t1) = state(t2),  d = pos(t2) - pos(t1),
        [lo,hi] = head range over [t1,t2],
        tape_{t2}(x+d) = tape_{t1}(x)  for all x in [lo,hi]
    (during [t1,t2] the head never leaves [lo,hi], so the run from t2 is
    the run from t1 shifted by d, forever);
  * tape-extent growth law: extent(t) fitted against log t / sqrt t / t,
    plus the scale-free exponent alpha = log(E(T)/E(T/4)) / log 4
    (LOG ~ 0.10, SQRT ~ 0.50, LIN ~ 1.00);
  * per-state visit profile: v_q(T)/v_q(T/4) (4.0 = linear, ~1.1 = log-rare);
  * "anchor-like" recurring configurations: steps at which one side of the
    tape is entirely blank (the counter-anchor shape the Jp/Ip template
    needs), classified by (state, side, head symbol);
  * the binary-odometer ruler signature of the anchor gaps
    (gap frequencies 1/2, 1/4, 1/8, ... <=> a carry-propagating counter)
    and the cells-per-digit slope of the anchor list length.

NOTHING here is trusted: the Coq kernel re-checks every board this routes.

Usage:
  python3 tools/counters/triage.py <specs.txt> <out.jsonl> [--workers N]
                                   [--steps T] [--limit N] [--summary]
"""
import sys, os, json, math
from collections import Counter
from concurrent.futures import ProcessPoolExecutor

T_DEFAULT = 100_000
WIN_R     = 256      # half-width of the record window kept for the TC test
SCAN      = 96       # how far back (in records) the TC test looks
REC_KEEP  = 1024     # cap on retained records
BRENT_MAX = 20_000   # skip exact-cycle detection above this extent


# ---------------------------------------------------------------- parsing

def parse_flat(spec):
    """spec 'ARB---_...' -> list of 8 entries indexed 2*state+sym."""
    tab = [None] * 8
    parts = spec.split('_')
    for si, part in enumerate(parts):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            if e == '---' or e == 'HHH' or len(e) < 3:
                tab[2 * si + yi] = None
            else:
                tab[2 * si + yi] = (int(e[0]),
                                    1 if e[1] == 'R' else -1,
                                    ord(e[2]) - ord('A'))
    return tab


# ---------------------------------------------------------------- fitting

def _lsq_r2(xs, ys):
    n = len(xs)
    if n < 3:
        return 0.0
    mx = sum(xs) / n
    my = sum(ys) / n
    sxx = sum((x - mx) ** 2 for x in xs)
    syy = sum((y - my) ** 2 for y in ys)
    sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    if sxx <= 0 or syy <= 0:
        return 0.0
    return (sxy * sxy) / (sxx * syy)


def growth_fit(samples):
    """samples: [(t, extent)] -> dict of R^2 per model + exponent."""
    pts = [(t, e) for (t, e) in samples if t >= 200 and e > 0]
    if len(pts) < 6:
        return None
    ts = [p[0] for p in pts]
    es = [float(p[1]) for p in pts]
    return {
        'r2_log':  round(_lsq_r2([math.log(t) for t in ts], es), 4),
        'r2_sqrt': round(_lsq_r2([math.sqrt(t) for t in ts], es), 4),
        'r2_lin':  round(_lsq_r2(ts, es), 4),
        'r2_pow':  round(_lsq_r2([math.log(t) for t in ts],
                                 [math.log(e) for e in es]), 4),
    }


# ------------------------------------------------- generalized anchor decode

def _Ip(m):
    out = []
    while m > 1:
        out += [1, m & 1]
        m >>= 1
    return out + [1]


def _Jp(m):
    out = []
    while m > 1:
        out += [1, 1 - (m & 1)]
        m >>= 1
    return out + [1]


def _tables(bound=1 << 15):
    ti, tj = {}, {}
    for m in range(1, bound):
        ti[''.join(map(str, _Ip(m)))] = m
        tj[''.join(map(str, _Jp(m)))] = m
    return ti, tj


TI, TJ = _tables()


def decode_probe(samples):
    """Which (encoding, head-side junk prefix, orientation) makes the anchor
    lists decode to an arithmetic progression?  Reports the generalization
    the Jp/Ip template would need.  None = no binary reading found."""
    if len(samples) < 6:
        return None
    best = None
    for orient in (0, 1):                       # 0 = nearest-first, 1 = reversed
        strs = [s[::-1] if orient else s for (_, s) in samples]
        for lstrip in range(0, 5):              # junk cells next to the head
            for rstrip in range(0, 3):          # junk cells at the far end
                vals, ok = [], 0
                for s in strs:
                    c = s[lstrip:len(s) - rstrip] if rstrip else s[lstrip:]
                    c = c.rstrip('0')
                    vals.append((TJ.get(c), TI.get(c)))
                for ei, nm in ((0, 'Jp'), (1, 'Ip')):
                    vv = [v[ei] for v in vals]
                    got = [v for v in vv if v is not None]
                    if len(got) < max(5, int(0.6 * len(vv))):
                        continue
                    # a counter's anchor values must actually GROW; a constant
                    # or shrinking read is a spurious decode of a fixed word
                    if got[-1] <= got[0] or len(set(got)) < 4:
                        continue
                    diffs = [b - a for a, b in zip(got, got[1:])]
                    step = Counter(diffs).most_common(1)[0][0]
                    if step < 1:
                        continue
                    frac = sum(1 for d in diffs if d == step) / len(diffs)
                    hit = len(got) / len(vv)
                    if frac < 0.7 or hit < 0.6:
                        continue
                    score = frac * hit - 0.02 * (lstrip + rstrip + orient)
                    if best is None or score > best['_s']:
                        best = {'enc': nm, 'lstrip': lstrip, 'rstrip': rstrip,
                                'rev': orient, 'step': step,
                                'frac': round(frac, 3), 'hit': round(hit, 3),
                                'p0': got[0], '_s': score}
    if best:
        best.pop('_s', None)
    return best


# --------------------------------------------- enumerated encoding families
#
# The landed modules cover exactly two points of a larger lattice:
#   Ip (ILCounter):  xO q = S1::S0::Ip q   xI q = S1::S1::Ip q   xH = [S1]
#   Jp (JpCounter):  xO q = S1::S1::Jp q   xI q = S1::S0::Jp q   xH = [S1]
# i.e. 2-cell digits, marker cell S1 first, bit plain / complemented,
# terminator [S1].  This enumerates the whole neighbourhood: 1-cell digits
# (dense binary), either marker symbol, either cell order, and any short
# terminator -- the terminator absorbs a far-end "wall" cell, and lpad
# absorbs junk cells sitting between the head and the counter word.
#
# Anchor words are recorded trailing-blank-stripped, so only terminators
# ending in S1 are observable.

TERMS = ['1', '01', '11', '001', '011', '101', '111']
LPADS = ['', '0', '1', '00', '01', '10', '11']


def enc_combos():
    out = []
    for c in (0, 1):
        out.append(('1cell', c, None, None))
    for c in (0, 1):
        for mk in (0, 1):
            for order in ('mb', 'bm'):
                out.append(('2cell', c, mk, order))
    return out


def enc_word(p, kind, c, mk, order, term, lpad):
    o = []
    while p > 1:
        b = (p & 1) ^ c
        if kind == '1cell':
            o.append(b)
        elif order == 'mb':
            o.append(mk)
            o.append(b)
        else:
            o.append(b)
            o.append(mk)
        p >>= 1
    return lpad + ''.join(map(str, o)) + term


_ENC_CACHE = {}


def enc_table(key, bound=1200):
    t = _ENC_CACHE.get(key)
    if t is None:
        kind, c, mk, order, term, lpad = key
        t = {}
        for v in range(1, bound):
            t.setdefault(enc_word(v, kind, c, mk, order, term, lpad), v)
        _ENC_CACHE[key] = t
    return t


def rep_fit(samples):
    """Is the anchor word [rep U k ++ W] (or [W ++ rep U k]) with k advancing
    by a constant?  That is the WTape.rep anchor shape -- no binary counter
    reading at all, and a far cheaper Coq lap (cycL/cycR over one unit)."""
    if len(samples) < 6:
        return None
    ws = [s for (_, s) in samples]
    best = None
    for side in ('pre', 'suf'):
        for plen in (1, 2, 3, 4):
            longest = max(ws, key=len)
            u = longest[:plen] if side == 'pre' else longest[-plen:]
            if not u:
                continue
            ks, tails = [], []
            for w in ws:
                k = 0
                if side == 'pre':
                    while w.startswith(u):
                        w = w[plen:]
                        k += 1
                else:
                    while w.endswith(u):
                        w = w[:-plen]
                        k += 1
                ks.append(k)
                tails.append(w)
            if len(set(tails)) != 1 or len(set(ks)) < 4:
                continue
            d = [b - a for a, b in zip(ks, ks[1:])]
            st = Counter(d).most_common(1)[0][0]
            if st < 1:
                continue
            frac = sum(1 for x in d if x == st) / len(d)
            if frac < 0.85:
                continue
            score = frac - 0.05 * plen - 0.02 * len(tails[0])
            if best is None or score > best['_s']:
                best = {'unit': u, 'tail': tails[0], 'side': side,
                        'k0': ks[0], 'kstep': st, 'frac': round(frac, 3),
                        '_s': score}
    if best:
        best.pop('_s')
    return best


def encfit(samples):
    """Best (encoding family, terminator, head pad, orientation) that reads
    the anchor words as an arithmetic progression.  None if no reading."""
    if len(samples) < 6:
        return None
    best = None
    for orient in (0, 1):
        ws = [(s[::-1] if orient else s) for (_, s) in samples]
        if orient:
            ws = [w.lstrip('0') for w in ws]
        for (kind, c, mk, order) in enc_combos():
            for term in TERMS:
                for lpad in LPADS:
                    tbl = enc_table((kind, c, mk, order, term, lpad))
                    got = [tbl.get(w) for w in ws]
                    vv = [v for v in got if v is not None]
                    if len(vv) < max(5, int(0.7 * len(got))):
                        continue
                    if vv[-1] <= vv[0] or len(set(vv)) < 4:
                        continue
                    diffs = [b - a for a, b in zip(vv, vv[1:])]
                    step = Counter(diffs).most_common(1)[0][0]
                    frac = sum(1 for d in diffs if d == step) / len(diffs) \
                        if step >= 1 else 0.0
                    # a counter whose comb-free anchor only recurs at
                    # OVERFLOW is a geometric progression, not arithmetic
                    rats = [b // a for a, b in zip(vv, vv[1:]) if a and b % a == 0]
                    mode, mstep, mfrac = 'add', step, frac
                    if len(rats) == len(vv) - 1:
                        rr = Counter(rats).most_common(1)[0][0]
                        rf = sum(1 for d in rats if d == rr) / len(rats)
                        if rr >= 2 and rf > frac:
                            mode, mstep, mfrac = 'mul', rr, rf
                    if mfrac < 0.8 or mstep < 1:
                        continue
                    score = (mfrac * len(vv) / len(got)
                             - 0.03 * (len(term) + len(lpad) + orient)
                             - (0.05 if kind == '1cell' else 0.0))
                    if best is None or score > best['_s']:
                        best = {'kind': kind, 'cmpl': c, 'marker': mk,
                                'order': order, 'term': term, 'lpad': lpad,
                                'rev': orient, 'mode': mode, 'step': mstep,
                                'p0': vv[0], 'frac': round(mfrac, 3),
                                'hit': round(len(vv) / len(got), 3), '_s': score}
    if best:
        best.pop('_s')
        # name the landed modules where they apply
        nm = 'other'
        if best['kind'] == '2cell' and best['marker'] == 1 and best['order'] == 'mb':
            nm = 'Jp' if best['cmpl'] == 1 else 'Ip'
        elif best['kind'] == '1cell':
            nm = 'dense'
        elif best['kind'] == '2cell' and best['marker'] == 0:
            nm = ('Jp0' if best['cmpl'] == 1 else 'Ip0') + \
                 ('' if best['order'] == 'mb' else 'r')
        elif best['kind'] == '2cell':
            nm = ('Jp1r' if best['cmpl'] == 1 else 'Ip1r')
        best['fam'] = nm
    return best


# ---------------------------------------------------------------- core sim

def analyse(spec, T=T_DEFAULT):
    tab = parse_flat(spec)
    R = WIN_R
    OFF = T + R + 4
    tape = bytearray(2 * T + 2 * R + 9)
    hist = bytearray(T)                 # state per step (for the cycle window)

    pos = OFF
    q = 0
    lo = hi = pos
    nzL = nzR = 0                       # nonblank cells strictly left / right
    visits = [0, 0, 0, 0]
    vquart = None

    # extent samples on a geometric schedule
    sched = sorted(set(
        [int(round(100 * (T / 100.0) ** (i / 79.0))) for i in range(80)]
        + [T // 16, T // 4, T // 2, T - 1]))
    sched = [s for s in sched if 0 < s < T]
    si = 0
    nxt = sched[0]
    samples = []

    # anchor-like configurations
    anch = Counter()                    # (state, side, headsym) -> count
    anch_times = {}                     # key -> [t...]  (capped)
    anch_lens = {}                      # key -> [span...] (capped)
    anch_tape = {}                      # key -> [(t, "0110..")] (capped)

    # records (extent-breaking configurations) for the translated-cycle test
    recs = []                           # (t, q, pos, side, seg_lo, seg_hi, win)
    base = 0                            # index offset after trimming
    seg_lo = seg_hi = pos
    cyc = None

    # Brent exact-cycle state
    b_t = b_q = b_pos = b_lo = b_hi = -1
    b_bytes = None
    b_next = 8

    halt_t = None
    tsim = T

    for t in range(T):
        hist[t] = q
        visits[q] += 1
        if t == T // 4:
            vquart = list(visits)
        h = tape[pos]
        e = tab[2 * q + h]
        if e is None:
            halt_t = t
            tsim = t
            break

        # ---- anchor-like config: one side entirely blank
        if nzR == 0 or nzL == 0:
            if nzR == 0 and nzL > 0:
                key = (q, 'L', h)
            elif nzL == 0 and nzR > 0:
                key = (q, 'R', h)
            elif nzL == 0 and nzR == 0:
                key = (q, '0', h)
            else:
                key = None
            if key is not None:
                anch[key] += 1
                lst = anch_times.setdefault(key, [])
                if len(lst) < 4000:
                    lst.append(t)
                ll = anch_lens.setdefault(key, [])
                if len(ll) < 600:
                    # counter-list span: head -> outermost nonblank cell,
                    # NEAREST-FIRST (the [Jp p ++ [S0]] orientation)
                    if key[1] == 'L':
                        cl = tape[lo:pos]
                        cl.reverse()
                    elif key[1] == 'R':
                        cl = tape[pos + 1:hi + 1]
                    else:
                        cl = bytearray()
                    while cl and cl[-1] == 0:
                        cl.pop()
                    ll.append(len(cl))
                    tl = anch_tape.setdefault(key, [])
                    if len(tl) < 16:
                        tl.append([t, ''.join(chr(48 + c) for c in cl)])

        # ---- step
        w, d, ns = e
        if d > 0:
            npos = pos + 1
            if w:
                nzL += 1
            if tape[npos]:
                nzR -= 1
        else:
            npos = pos - 1
            if w:
                nzR += 1
            if tape[npos]:
                nzL -= 1
        tape[pos] = w
        pos = npos
        q = ns

        # ---- extent record / segment tracking
        newrec = 0
        if pos > seg_hi:
            seg_hi = pos
            if pos > hi:
                hi = pos
                newrec = 1
        elif pos < seg_lo:
            seg_lo = pos
            if pos < lo:
                lo = pos
                newrec = -1

        if newrec and cyc is None:
            win = bytes(tape[pos - R:pos + R + 1])
            recs.append((t + 1, q, pos, newrec, seg_lo, seg_hi, win))
            i = len(recs) - 1
            # walk back looking for the same (state, side) with a matching
            # shifted window over the whole interval head-range
            mn, mx = recs[i][4], recs[i][5]
            stop = max(-1, i - 1 - SCAN)
            for j in range(i - 1, stop, -1):
                rj = recs[j]
                if rj[3] == newrec and rj[1] == q:
                    dd = pos - rj[2]
                    if dd != 0:
                        a = mn if mn < rj[2] else rj[2]
                        b = mx if mx > rj[2] else rj[2]
                        k1 = a - rj[2]
                        k2 = b - rj[2]
                        if k1 >= -R and k2 <= R:
                            if rj[6][R + k1:R + k2 + 1] == win[R + k1:R + k2 + 1]:
                                cyc = {'kind': 'TRANS', 't0': rj[0],
                                       'period': (t + 1) - rj[0], 'shift': dd,
                                       'reach': max(rj[2] - a, b - rj[2])}
                                break
                if rj[4] < mn:
                    mn = rj[4]
                if rj[5] > mx:
                    mx = rj[5]
            seg_lo = seg_hi = pos
            if len(recs) > REC_KEEP:
                del recs[:REC_KEEP // 2]

        # ---- Brent exact in-place cycle
        if cyc is None and hi - lo < BRENT_MAX:
            if b_bytes is not None and q == b_q and pos == b_pos \
               and lo == b_lo and hi == b_hi \
               and tape[lo:hi + 1] == b_bytes:
                cyc = {'kind': 'INPLACE', 't0': b_t, 'period': (t + 1) - b_t,
                       'shift': 0, 'reach': hi - lo + 1}
            if t + 1 == b_next:
                b_t, b_q, b_pos, b_lo, b_hi = t + 1, q, pos, lo, hi
                b_bytes = bytes(tape[lo:hi + 1])
                b_next *= 2

        if si < len(sched) and t + 1 == nxt:
            samples.append((t + 1, hi - lo + 1))
            si += 1
            nxt = sched[si] if si < len(sched) else T + 1

    if vquart is None:
        vquart = list(visits)
    extent = hi - lo + 1
    rec = {'m': spec, 'steps': tsim, 'extent': extent}

    if halt_t is not None:
        rec['cls'] = 'HALT'
        rec['halt_t'] = halt_t
        return rec

    # ---------------- cycle classification
    if cyc is not None:
        t0, p = cyc['t0'], cyc['period']
        loop = set(hist[t0:t0 + p]) if t0 + p <= T else set(hist[t0:T])
        pre = set(hist[0:t0])
        allst = set(hist[0:T])
        cyc['loop_states'] = ''.join("ABCD"[s] for s in sorted(loop))
        cyc['run_states'] = ''.join("ABCD"[s] for s in sorted(allst))
        cyc['nqh_ok'] = pre.issubset(loop) and allst.issubset(loop)
        rec['cls'] = 'CYC_' + cyc['kind']
        rec['cyc'] = cyc

    # ---------------- growth law
    fit = growth_fit(samples)
    e_q = e_h = e_f = None
    for (t, ee) in samples:
        if t <= T // 16:
            e_h = ee
        if t <= T // 4:
            e_q = ee
        e_f = ee
    alpha = None
    if e_q and e_f and e_q > 0:
        alpha = math.log(max(e_f, 1) / e_q) / math.log(4.0)
    alpha2 = None
    if e_h and e_q and e_h > 0:
        alpha2 = math.log(max(e_q, 1) / e_h) / math.log(4.0)
    rec['alpha'] = None if alpha is None else round(alpha, 3)
    rec['alpha2'] = None if alpha2 is None else round(alpha2, 3)
    rec['fit'] = fit
    rec['ext_q'] = e_q
    rec['ext_T'] = e_f

    if alpha is None:
        growth = 'NA'
    elif e_f is not None and e_f <= 64 and alpha <= 0.02:
        growth = 'BOUNDED'
    elif alpha < 0.25:
        growth = 'LOG'
    elif alpha < 0.72:
        growth = 'SQRT'
    elif alpha >= 0.72:
        growth = 'LIN'
    else:
        growth = 'AMBIG'
    # cross-check with the least-squares fits
    if fit and growth in ('LOG', 'SQRT', 'LIN'):
        best = max(('LOG', fit['r2_log']), ('SQRT', fit['r2_sqrt']),
                   ('LIN', fit['r2_lin']), key=lambda z: z[1])[0]
        rec['fit_best'] = best
        rec['fit_agree'] = (best == growth)
    rec['growth'] = growth

    # ---------------- visit profile
    ratios = {}
    nlog = 0
    for s in range(4):
        nm = "ABCD"[s]
        if visits[s] == 0:
            ratios[nm] = None
            continue
        r = visits[s] / max(1, vquart[s])
        ratios[nm] = round(r, 3)
        if r < 1.8 and visits[s] > 0:
            nlog += 1
    rec['visits'] = {"ABCD"[s]: visits[s] for s in range(4)}
    rec['vratio'] = ratios
    rec['n_log_rare'] = nlog
    rec['n_silent'] = sum(1 for s in range(4) if visits[s] == 0)

    # ---------------- anchor-like configurations
    cls_all = sorted(anch.items(), key=lambda kv: -kv[1])
    rec['anchor_classes'] = [
        ["ABCD"[k[0]], k[1], k[2], c] for k, c in cls_all[:8]]
    rec['n_anchor_cls'] = sum(1 for _, c in cls_all if c >= 8)
    rec['n_anchor_cls_blank'] = sum(
        1 for k, c in cls_all if c >= 8 and k[2] == 0 and k[1] in 'LR')
    rec['n_anchor_hits'] = sum(anch.values())

    # ruler signature + cells-per-digit + generalized decode.  Try EVERY
    # recurring anchor class (fingerprint.py did the same) and keep the class
    # whose counter reading is an arithmetic progression.
    rec['ruler'] = None
    rec['cells_per_digit'] = None
    domi = None
    dec = None
    for k, c in cls_all:
        if c < 8 or k[1] not in 'LR':
            continue
        d = decode_probe(anch_tape.get(k, []))
        if d is not None and (dec is None or d['frac'] * d['hit'] > dec['frac'] * dec['hit']):
            dec, domi = d, k
    if domi is None:
        for k, c in cls_all:
            if c >= 8 and k[2] == 0 and k[1] in 'LR':
                domi = k
                break
    if domi is None:
        for k, c in cls_all:
            if c >= 8 and k[1] in 'LR':
                domi = k
                break
    if domi is not None:
        ts = anch_times[domi]
        gaps = [b - a for a, b in zip(ts, ts[1:])]
        if len(gaps) >= 8:
            cg = Counter(gaps).most_common(4)
            n = len(gaps)
            rec['ruler'] = {
                'dom': ["ABCD"[domi[0]], domi[1], domi[2]],
                'ngaps': n,
                'top': [[g, round(c / n, 3)] for g, c in cg],
            }
        ll = anch_lens[domi]
        if len(ll) >= 8:
            xs = [math.log(i + 1.0) for i in range(len(ll))]
            ys = [float(v) for v in ll]
            n = len(xs)
            mx = sum(xs) / n
            my = sum(ys) / n
            sxx = sum((x - mx) ** 2 for x in xs)
            sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
            if sxx > 0:
                # length grows as slope*ln(k) = slope*ln2 per binary digit
                rec['cells_per_digit'] = round(sxy / sxx * math.log(2.0), 3)
        rec['anchor_samples'] = anch_tape.get(domi, [])[:16]
        rec['anchor_dom'] = ["ABCD"[domi[0]], domi[1], domi[2]]
        rec['decode'] = dec

    if 'cls' not in rec:
        rec['cls'] = growth
    return rec


def verify_cycle(spec, t0, p):
    """Independent re-simulation check of a claimed translated cycle, and the
    TCycler certificate parameters (side / anchor_step / period / reach).

    Replays 4 laps and demands cfg(t0 + k*p) = cfg(t0) shifted by k*shift on
    the whole visited window, plus the never-QH side condition (every state
    seen in [0,t0) recurs inside the lap window)."""
    tab = parse_flat(spec)
    N = t0 + 5 * p + 16
    OFF = N + 8
    tape = bytearray(2 * N + 32)
    pos, q = OFF, 0
    seen_pre, seen_lap = set(), set()
    snaps = []
    lapmin = lapmax = None
    for t in range(t0 + 4 * p + 1):
        if t < t0:
            seen_pre.add(q)
        else:
            seen_lap.add(q)
            if lapmin is None or pos < lapmin:
                lapmin = pos
            if lapmax is None or pos > lapmax:
                lapmax = pos
        if t >= t0 and (t - t0) % p == 0:
            snaps.append((q, pos, bytes(tape)))
            if len(snaps) == 2:
                lap1min, lap1max = lapmin, lapmax
        e = tab[2 * q + tape[pos]]
        if e is None:
            return {'ok': False, 'why': 'halts'}
        w, d, ns = e
        tape[pos] = w
        pos += d
        q = ns
    d0 = snaps[1][1] - snaps[0][1]
    ok = True
    for k in range(1, len(snaps)):
        if snaps[k][0] != snaps[0][0] or snaps[k][1] - snaps[0][1] != k * d0:
            ok = False
            break
        # only the cells the lap actually touches have to be a shifted copy;
        # the trail left behind outside that window is irrelevant to the future
        a, b = snaps[0][2], snaps[k][2]
        sh = k * d0
        if a[lap1min:lap1max + 1] != b[lap1min + sh:lap1max + sh + 1]:
            ok = False
            break
    a0 = snaps[0][1]
    return {'ok': ok, 'shift': d0, 'side': 'R' if d0 > 0 else 'L',
            'anchor_step': t0, 'period': p,
            'left_excursion': a0 - lap1min, 'right_excursion': lap1max - a0,
            'reach': (a0 - lap1min) if d0 > 0 else (lap1max - a0),
            'lap_states': ''.join("ABCD"[s] for s in sorted(seen_lap)),
            'pre_states': ''.join("ABCD"[s] for s in sorted(seen_pre)),
            'neverqh_ok': seen_pre.issubset(seen_lap)}


def worker(spec):
    try:
        return analyse(spec, T=int(os.environ.get('TRIAGE_STEPS', T_DEFAULT)))
    except Exception as ex:            # never let one machine kill the sweep
        return {'m': spec, 'cls': 'ERROR', 'err': '%s: %s' % (type(ex).__name__, ex)}


# ---------------------------------------------------------------- reporting

def summarize(recs, out=sys.stdout):
    by = Counter(r['cls'] for r in recs)
    out.write('total %d\n' % len(recs))
    for k, v in by.most_common():
        out.write('  %-14s %5d\n' % (k, v))
    cyc = [r for r in recs if r['cls'].startswith('CYC_')]
    if cyc:
        ok = [r for r in cyc if r['cyc']['nqh_ok']]
        out.write('cyclers %d (never-QH-boardable %d, quasihalting %d)\n'
                  % (len(cyc), len(ok), len(cyc) - len(ok)))
    for cl in ('LOG', 'SQRT', 'LIN', 'BOUNDED', 'AMBIG', 'NA'):
        g = [r for r in recs if r.get('growth') == cl and not r['cls'].startswith('CYC_')]
        if g:
            out.write('  growth %-8s %5d  ex: %s\n' % (cl, len(g), g[0]['m']))


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    flags = {a.split('=')[0]: (a.split('=')[1] if '=' in a else True)
             for a in sys.argv[1:] if a.startswith('--')}
    if '--encfit' in flags:
        # post-pass over a triage jsonl: no re-simulation, just fit the
        # recorded anchor words against the whole encoding lattice
        cen = Counter()
        rows = []
        for l in open(args[0]):
            r = json.loads(l)
            if r['cls'] != 'LOG':
                continue
            sm = r.get('anchor_samples') or []
            f = encfit(sm)
            if f is None:                      # anchor hit twice per lap?
                for ph in (0, 1):
                    g = encfit(sm[ph::2])
                    if g is not None:
                        g['phase'] = '2/%d' % ph
                        f = g
                        break
            r['encfit'] = f
            r['repfit'] = rep_fit(sm)
            rows.append(r)
            if f is None and r['repfit']:
                rf = r['repfit']
                key = ('rep', 'U=%s' % rf['unit'], 'W=%s' % (rf['tail'] or '.'),
                       rf['side'], 'dk%d' % rf['kstep'])
                cen[key] += 1
                continue
            key = ('none',) if f is None else (
                f['fam'], f['kind'], 'mk%s' % f['marker'], f['order'] or '-',
                'c%d' % f['cmpl'], 'T%s' % f['term'], 'P%s' % f['lpad'],
                'rev%d' % f['rev'], '%s%d' % (f['mode'], f['step']),
                'ph' + f.get('phase', '1'))
            cen[key] += 1
        if len(args) > 1:
            with open(args[1], 'w') as f:
                for r in rows:
                    f.write(json.dumps(r) + '\n')
        for k, v in cen.most_common(40):
            print('%6d  %s' % (v, ' '.join(k)))
        print('TOTAL %d   unread %d' % (len(rows), cen[('none',)]))
        return
    if '--verify-cyclers' in flags:
        # args[0] is a triage jsonl; re-check every CYC_* record from scratch
        bad = 0
        for l in open(args[0]):
            r = json.loads(l)
            if not r['cls'].startswith('CYC_'):
                continue
            v = verify_cycle(r['m'], r['cyc']['t0'], r['cyc']['period'])
            bad += 0 if v.get('ok') else 1
            print(json.dumps({'m': r['m'], **v}))
        sys.stderr.write('verify: %d FAILED\n' % bad)
        return
    src, out = args[0], args[1]
    ms = [x.strip() for x in open(src) if x.strip()]
    if '--limit' in flags:
        ms = ms[:int(flags['--limit'])]
    if '--steps' in flags:
        os.environ['TRIAGE_STEPS'] = str(flags['--steps'])
    nw = int(flags.get('--workers', 4))
    recs = []
    with open(out, 'w') as f, ProcessPoolExecutor(max_workers=nw) as ex:
        for i, r in enumerate(ex.map(worker, ms, chunksize=4)):
            recs.append(r)
            f.write(json.dumps(r) + '\n')
            if (i + 1) % 200 == 0:
                f.flush()
                sys.stderr.write('%d/%d\n' % (i + 1, len(ms)))
    summarize(recs, sys.stderr)


if __name__ == '__main__':
    main()
