#!/usr/bin/env python3
"""Bouncer + counter hybrids whose counter is any positional numeration ->
closeout batches (UNTRUSTED finder + batch writer, SCOPING_INSTR.md 7.4.HY2).

    python3 tools/closeouttr/hy2_batch.py find ROWS.txt OUT.jsonl [--jobs 4]
    python3 tools/closeouttr/hy2_batch.py batch OUT.jsonl [...] --tag HY2 [--chunk 50]

HY's finder (hy_batch.py) reads the counter end as a binary word
E p = digits in {A, B} under a top word C.  Its residue is mostly the same
lap under a counter E cannot write (base 3 and 4, a top word longer than 6
cells, a digit under the MSB written differently).  Here the counter is a
pair (low, tv): low digits in base b, one word per digit (D_0 .. D_{b-1}),
and a top window of value lo <= tv < b * lo read through a word table T,

    hcE (low, tv) = concat (map D low) ++ T tv,

which theories/Counters/HybridCtrTr.v decides ([hc_check_nqh]).  `find`:

  1. runs the row (and its mirror) for N steps and collects HY's anchor
     sequences (one instruction at one cell; the k-th visit of a cell
     after each sweep), sub-sampled every S sweeps;
  2. reads the family: a common prefix, a digit width d, a base b whose
     low digit cycles with period b, and the value v0 of the first anchor
     such that every anchor's word is Lpre ++ hcE (v0 + k) with ONE top
     word per top value (the top table, partially observed);
  3. reads the block and each phase's mid off the simulation (HY's), fills
     the rest of the top table by running the machine from a constructed
     anchor over each top step (the top word the carry leaves behind);
  4. derives one carry chain per digit below b - 1, one per top value (the
     last is the overflow), and the sweep chain, with
     tools/counters/lapcert.derive_chain; the boot; a chain prefix firing
     each unpinned instruction, with the value family reaching it.

Everything is re-checked by the kernel.  Only rows still in
closeouttr_remaining.txt are written.  Compile each batch before
committing (--skip SPEC drops a row), then run gen_closeout_tr.py.
"""
import argparse
import collections
import itertools
import json
import os
import signal
import sys
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'counters'))
import hy_batch as H                           # noqa: E402
from cbt import REPO, next_free, write_batch  # noqa: E402
import lapcert as LC                           # noqa: E402

N_STEPS = 400000
BOOT_CAP = 200000
V0_CAP = 1 << 20          # anchor values stay small: the checker computes them in nat
TOP_MAX = 40              # top words longer than this are not a counter's top
MAX_WORD = 200
TIME_BUDGET = int(os.environ.get('HY2_BUDGET', 240))
ST, SYM = H.ST, H.SYM
rstrip0, lpad_eq, sflat = H.rstrip0, H.lpad_eq, H.sflat


# ----------------------------------------------------------- the numeration --
#
# HybridCtrTr's counter (low digits in base b, top value tv in [lo, hi)) is
# written here with lo = 0 and hi = H, the length of the TOP CYCLE: the top
# words the counter steps through before an overflow widens it.  Positional
# counters have H = b - 1 (a top digit) or b (b - 1) (two top digits); a
# counter with only a terminator has H = 1.  Values are RANKS, the checker's
# [cval]: H G(k) + vl low + b^k tv, G(k) = 1 + b + ... + b^(k-1).

def G(b, k):
    return (b ** k - 1) // (b - 1)


def ctr_of(r, b, H):
    """rank -> (low digits LSB first, top index)"""
    k = 0
    while H * G(b, k + 1) <= r:
        k += 1
    rem = r - H * G(b, k)
    x, low = rem % b ** k, []
    for _ in range(k):
        low.append(x % b)
        x //= b
    return low, rem // b ** k


def fword(F, r):
    """F's word of rank r, or None when its top word is unknown"""
    low, tv = ctr_of(r, F['b'], F['H'])
    if tv not in F['T']:
        return None
    out = []
    for d in low:
        out += F['D'][d]
    return tuple(out) + tuple(F['T'][tv])


def fdecode(F, word):
    """a word -> its rank (up to trailing blanks), or None"""
    word = rstrip0(word)
    D, b, H = F['D'], F['b'], F['H']
    idx = {tuple(D[i]): i for i in range(b)}
    wd = len(D[0])
    i, low = 0, []
    while True:
        rest = word[i:]
        for tv, t in F['T'].items():
            if rest == rstrip0(t):
                k = len(low)
                v = 0
                for dgt in reversed(low):
                    v = v * b + dgt
                return H * G(b, k) + v + b ** k * tv
        ch = word[i:i + wd]
        if len(ch) < wd or ch not in idx:
            return None
        low.append(idx[ch])
        i += wd


def family(Ls, step=1, maxd=6, bases=(2, 3, 4)):
    """Ls: left sides at consecutive anchors whose rank grows by [step].
    -> (Lpre, F, r0) with Ls[k] = Lpre ++ hcE (r0 + step k) up to trailing
    blanks, F = dict(b, H, D, T (partial)), or None"""
    if min(len(rstrip0(x)) for x in Ls[-3:]) > MAX_WORD:
        return None
    N = len(Ls)
    first = min(len(x) for x in Ls)
    for lp in range(0, 5):
        if lp > first:
            break
        pre = tuple(Ls[0][:lp])
        if any(tuple(x[:lp]) != pre for x in Ls):
            break
        W = [tuple(x[lp:]) for x in Ls]
        for d in range(1, maxd + 1):
            lows = [w[:d] + (0,) * (d - len(w[:d])) for w in W]
            for b in bases:
                if __import__('math').gcd(b, step) != 1:
                    continue
                if any(lows[k] != lows[k + b] for k in range(N - b)):
                    continue
                if len(set(lows[:b])) != b:
                    continue
                for Hc in sorted(set([b - 1, 1, b * (b - 1), 2, 3])):
                    got = _fit(W, lows, b, d, Hc, step)
                    if got:
                        F, r0 = got
                        return pre, F, r0
    return None


def _fit(W, lows, b, d, Hc, step):
    N = len(W)
    for r in range(b):
        # the anchor at rank r0 + step k shows low digit (r + step k) mod b
        # (the low digit of a rank is (rank - H G(k)) mod b; fitted below)
        D = [None] * b
        for k in range(b):
            D[(r + step * k) % b] = lows[k]
        if None in D:
            continue
        idx = {D[i]: i for i in range(b)}
        wl = W[-1]
        parses, i, lowv, mul = [(0, 0, 1)], 0, 0, 1
        while i + d <= len(wl) and wl[i:i + d] in idx and len(parses) < 48:
            lowv += idx[wl[i:i + d]] * mul
            mul *= b
            i += d
            parses.append((i, lowv, mul))
        for kk, (i, lowv, mul) in reversed(list(enumerate(parses))):
            if kk < 2:
                continue
            for tv in range(Hc):
                rlast = Hc * G(b, kk) + lowv + mul * tv
                r0 = rlast - step * (N - 1)
                if r0 < 0 or r0 > V0_CAP or ctr_of(r0, b, Hc)[0][:1] == []:
                    continue
                T, ok = {}, True
                for k in [N - 1, N - 2, N - 3, 0] + list(range(1, N - 3)):
                    low, top = ctr_of(r0 + step * k, b, Hc)
                    if len(low) < 2:
                        ok = False
                        break
                    lw = ()
                    for x in low:
                        lw += D[x]
                    wk = W[k]
                    if wk[:len(lw)] != lw:
                        ok = False
                        break
                    rest = rstrip0(wk[len(lw):])
                    if len(rest) > TOP_MAX or (top in T and T[top] != rest):
                        ok = False
                        break
                    T[top] = rest
                # distinct top values must read as distinct words
                if ok and len(set(T.values())) == len(T):
                    return dict(b=b, H=Hc, D=[tuple(x) for x in D], T=T), r0
    return None


def first_exit(tab, anc, x_r):
    """run one lap's counter half from [anc] to the first step right past
    relative cell x_r: (state, head, left side), or None"""
    mc = H.mid_of(tab, anc, x_r)
    if mc is None:
        return None
    return mc[0], mc[2], tuple(mc[1])


def split_exit(L2, L3, D0, pref=None):
    """L2, L3: the left sides after the same carry at j = 2 and 3:
    P ++ D0^(2 + o) ++ R and P ++ D0^(3 + o) ++ R.  -> (P, R), preferring
    the exit prefix [pref]"""
    d = len(D0)
    cands = []
    for plen in range(0, len(L2) + 1):
        P = L2[:plen]
        if L3[:plen] != P:
            break
        if L2[plen:plen + 2 * d] == D0 * 2 and L3[plen:plen + 3 * d] == D0 * 3 \
                and rstrip0(L2[plen + 2 * d:]) == rstrip0(L3[plen + 3 * d:]):
            cands.append((P, rstrip0(L2[plen + 2 * d:])))
    if not cands:
        return None
    for P, R in cands:
        if pref is not None and P == tuple(pref):
            return P, R
    return cands[0]


def learn_cycle(tab, F, q, h, Lpre, Rpre, w, Rpost, m, ex0):
    """the top cycle by simulation: from an observed top word X, one lap's
    counter half from [Dm^j ++ X] leaves [D0^j ++ X'] (a top step to X') or
    [D0^(j+1) ++ X''] with X'' a word already met (the overflow), at the
    main exit [ex0] or another one.
    -> (H, [top words from the post-overflow word on]) or None"""
    b, D = F['b'], F['D']
    Dm, D0 = tuple(D[b - 1]), tuple(D[0])
    x_r = len(Rpre) + m * len(w)
    seq = [tuple(F['T'][min(F['T'])])]
    for _ in range(b * b + 2):
        X = seq[-1]
        outs = []
        for j in (2, 3):
            anc = (q, tuple(Lpre) + Dm * j + X, h,
                   tuple(Rpre) + tuple(w) * (m + 8) + tuple(Rpost))
            ex = first_exit(tab, anc, x_r)
            if ex is None:
                return None
            outs.append(ex)
        if outs[0][:2] != outs[1][:2]:
            return None
        pref = ex0[2] if outs[0][:2] == tuple(ex0[:2]) else None
        sp = split_exit(outs[0][2], outs[1][2], D0, pref)
        if sp is None:
            return None
        Y = sp[1]
        if len(Y) > TOP_MAX + len(D0):
            return None
        for c, Xc in enumerate(seq):
            if Y == rstrip0(D0 + Xc):
                cyc = seq[c:]
                return len(cyc), cyc
        seq.append(Y)
    return None


def refit(F, W, step):
    """the rank of the first of the words W (Lpre stripped) under F, or None"""
    r = fdecode(F, W[-1])
    if r is None:
        return None
    r0 = r - step * (len(W) - 1)
    if r0 < 0:
        return None
    for k, x in enumerate(W):
        wk = fword(F, r0 + step * k)
        if wk is None or not lpad_eq(wk, x):
            return None
    return r0


# --------------------------------------------------------------- the laps ---

def phase_mid(tab, cls, Lpre, F, v0, L, i, blk, m):
    """HY's phase_mid over F: (q2, h2, Mpre) read off every snapshot"""
    Rpre, w, Rpost, ns = blk
    x_r = len(Rpre) + m * len(w)
    Mlen = x_r + len(Lpre)
    got = None
    ks = sorted(set(list(range(min(6, len(cls)))) + list(range(0, len(cls), max(1, len(cls) // 6)))))
    for k in ks:
        t, q, h, Ls, Rs = cls[k]
        p = v0 + i + L * k
        n = ns[k]
        if n < m + 1:
            return None
        mc = H.mid_of(tab, (q, Ls, h, Rs), x_r)
        if mc is None:
            return None
        mq, mL, mh, mR = mc
        if got is None:
            got = (mq, mh, tuple(mL[:Mlen]))
        wn = fword(F, p + 1)
        if wn is None:
            continue
        if (mq, mh, tuple(mL[:Mlen])) != got or not lpad_eq(mL[Mlen:], wn) \
                or not lpad_eq(mR, w * (n - m) + Rpost):
            return None
    return got


def carry_case(tabw, q, h, Lpre, Rw, q2, h2, Mpre, Dm, D0, el, off, Ps, Pe):
    """one HybridCtrTr carry case: Dm^j ++ Ps -> D0^(j + off) ++ Pe"""
    Ps, Pe = tuple(Ps), tuple(Pe)
    for nu in (0, 1, 2):
        K0 = (q, (tuple(Lpre) + Dm * nu, Dm, 1, 0, Ps), h, sflat(Rw))
        c = nu + off
        tg = [(q2, (tuple(Mpre) + D0 * x, D0, 1, c - x, Pe), h2, sflat(()))
              for x in range(c + 1)]
        ch = H.derive(tabw, el, False, K0, tg,
                      lambda r: H.end_counter_ok(r[0], q2, h2, tuple(Mpre), D0, c, Pe, el))
        if ch is None:
            continue
        base = []
        for j in range(nu):
            S0 = (q, sflat(tuple(Lpre) + Dm * j + Ps), h, sflat(Rw))
            want = tuple(Mpre) + D0 * (j + off) + Pe
            bc = H.derive(tabw, el, False, S0, [(q2, sflat(want), h2, sflat(()))],
                          lambda r: H.end_cbase_ok(r[0], q2, h2, want, el))
            if bc is None:
                break
            base.append(bc)
        else:
            return dict(nu=nu, ch=ch, base=base, K0=K0, el=el)
    return None


def case_exit(tab, q, h, Lpre, Rpre, w, Rpost, m, F, Ps, tail):
    """the exit a carry case takes, by simulation: (q2, h2, Mpre) or None"""
    b, D = F['b'], F['D']
    Dm, D0 = tuple(D[b - 1]), tuple(D[0])
    x_r = len(Rpre) + m * len(w)
    outs = []
    for j in (2, 3):
        anc = (q, tuple(Lpre) + Dm * j + tuple(Ps) + tuple(tail), h,
               tuple(Rpre) + tuple(w) * (m + 8) + tuple(Rpost))
        ex = first_exit(tab, anc, x_r)
        if ex is None:
            return None
        outs.append(ex)
    if outs[0][:2] != outs[1][:2]:
        return None
    sp = split_exit(outs[0][2], outs[1][2], D0)
    if sp is None:
        return None
    return outs[0][0], outs[0][1], sp[0]


def phase_counter(tab, tabw, q, h, Lpre, F, Rpre, w, Rpost, m, ex0):
    """the carry cases of one phase, each on the main exit [ex0] or on its
    own: {'int', 'top', 'exits'}, or an error"""
    b, Hc, D, T = F['b'], F['H'], F['D'], F['T']
    Dm, D0 = tuple(D[b - 1]), tuple(D[0])
    Rw = tuple(Rpre) + tuple(w) * m
    exits = [tuple(ex0)]
    tail0 = tuple(D[0]) + tuple(T[0])

    def case(el, off, Ps, Pe, tail):
        for ex in list(exits):
            k = carry_case(tabw, q, h, Lpre, Rw, ex[0], ex[1], ex[2], Dm, D0, el, off, Ps, Pe)
            if k is not None:
                k['ex'] = exits.index(ex)
                return k
        ex = case_exit(tab, q, h, Lpre, Rpre, w, Rpost, m, F, Ps, tail)
        if ex is None or ex in exits:
            return None
        k = carry_case(tabw, q, h, Lpre, Rw, ex[0], ex[1], ex[2], Dm, D0, el, off, Ps, Pe)
        if k is None:
            return None
        exits.append(ex)
        k['ex'] = len(exits) - 1
        return k

    ints, tops = [], []
    for d in range(b - 1):
        k = case(False, 0, D[d], D[d + 1], tail0)
        if k is None:
            return 'no interior chain (digit %d)' % d
        ints.append(k)
    for e in range(Hc):
        if e + 1 < Hc:
            k = case(True, 0, T[e], T[e + 1], ())
        else:
            k = case(True, 1, T[e], T[0], ())
        if k is None:
            return 'no %s chain' % ('top' if e + 1 < Hc else 'overflow')
        tops.append(k)
    return dict(int=ints, top=tops, exits=exits)


def int_family(F, v0, i0, L, i, d, nu):
    """(j, H0): H G(j+1) + (b^j - 1) + b^j d + b^(j+1) (H0 + L s) lies in phase i"""
    b, Hc = F['b'], F['H']
    for j in range(nu, nu + 2 * L + 3):
        h0 = max(0, v0 // b ** (j + 1) - 1)
        for H0 in range(h0, h0 + 2 * L + 4):
            x = Hc * G(b, j + 1) + (b ** j - 1) + b ** j * d + b ** (j + 1) * H0
            if x >= v0 and (i0 + x - v0) % L == i:
                return j, H0
    return None


def top_family(F, v0, i0, L, i, e, nu):
    """(j0, T): the ranks ytop e (j0 + T s) - 1 lie in phase i"""
    b, Hc = F['b'], F['H']
    y = lambda j: Hc * G(b, j) + b ** j * (e + 1)  # noqa: E731
    for j0 in range(nu, nu + 64):
        x = y(j0) - 1
        if x > 64 * V0_CAP:
            break
        if x < v0 or (i0 + x - v0) % L != i:
            continue
        for T in range(1, 4 * L + 1):
            if y(j0 + T) % L == y(j0) % L:
                return j0, T
    return None


def block_family(Rs):
    """HY's block_family, with a block prefix of up to 12 cells"""
    out = []
    Rm = Rs[-1]
    for lp in range(0, 13):
        for a in (1, 2, 3, 4, 5, 6, 7, 8):
            u = Rm[lp:lp + a]
            if len(u) < a or not any(u):
                continue
            sp = [H.split_block(R, lp, u) for R in Rs]
            if any(s is None for s in sp):
                continue
            if len(set((s[0], s[2]) for s in sp)) != 1:
                continue
            ns = [s[1] for s in sp]
            if ns[-1] <= ns[0]:
                continue
            out.append((sp[0][0], u, sp[0][2], ns))
    return out


def try_phases(tab, tabw, pins, snaps, fam, L):
    """a certificate with L phases from consecutive-lap snapshots"""
    Lpre, F, v0 = fam
    Lpres = Lpre if isinstance(Lpre, list) else [Lpre] * L
    cls = [snaps[i::L] for i in range(L)]
    if min(len(c) for c in cls) < 6:
        return None, 'too few laps'
    qh_ = []
    for i in range(L):
        st = set((s[1], s[2]) for s in cls[i])
        if len(st) != 1:
            return None, 'state not periodic'
        qh_.append(st.pop())
    bls = [block_family([s[4] for s in cls[i]])[:4] for i in range(L)]
    if not all(bls):
        return None, 'no block'
    why = 'no block combination'
    for combo in itertools.product(*bls):
        if len(set(len(b[1]) for b in combo)) != 1:
            continue
        nlap = [combo[k % L][3][k // L] for k in range(len(snaps))
                if k // L < len(combo[k % L][3])]
        ds = [set() for _ in range(L)]
        for k in range(len(nlap) - 1):
            ds[k % L].add(nlap[k + 1] - nlap[k])
        if any(len(d) != 1 for d in ds):
            why = 'block growth not periodic'
            continue
        ds = [d.pop() for d in ds]
        if sum(ds) <= 0:
            why = 'block does not grow'
            continue
        F1 = None
        v1 = None
        phases = []
        for i in range(L):
            q, h = qh_[i]
            Rpre, w, Rpost, ns = combo[i]
            ph = None
            for m in (0, 1, 2):
                mid = phase_mid(tab, cls[i], Lpres[i], F, v0, L, i, combo[i], m)
                if mid is None:
                    why = 'no mid'
                    continue
                q2, h2, Mpre = mid
                if F1 is None:
                    cyc = learn_cycle(tab, F, q, h, Lpres[i], Rpre, w, Rpost, m, mid)
                    if cyc is None:
                        why = 'no top cycle'
                        continue
                    Fc = dict(b=F['b'], D=F['D'], H=cyc[0], T=dict(enumerate(cyc[1])))
                    r0s = [refit(Fc, [tuple(sn[3][len(Lpres[k]):]) for sn in cls[k]], L)
                           for k in range(L)]
                    if None in r0s or any(r0s[k] != r0s[0] + k for k in range(L)):
                        why = 'top cycle does not fit'
                        continue
                    F1, v1 = Fc, r0s[0]
                ctr = phase_counter(tab, tabw, q, h, Lpres[i], F1, Rpre, w, Rpost, m, mid)
                if isinstance(ctr, str):
                    why = ctr
                    continue
                j = (i + 1) % L
                nxt = (qh_[j][0], Lpres[j], qh_[j][1], combo[j][0], combo[j][1], combo[j][2])
                exits = []
                for xi, ex in enumerate(ctr['exits']):
                    sw = None
                    dds = (ds[i],) if xi == 0 else (ds[i], ds[i] - 1, ds[i] + 1, ds[i] - 2, ds[i] + 2)
                    for dd in dds:
                        sw = H.phase_sweep(tabw, ex[0], ex[1], ex[2], w, Rpost, m, dd, nxt)
                        if not isinstance(sw, str):
                            break
                    if isinstance(sw, str):
                        break
                    exits.append(dict(q2=ex[0], h2=ex[1], Mpre=list(ex[2]), **sw))
                else:
                    ph = dict(q=q, h=h, Lpre=Lpres[i], Rpre=Rpre, w=w, Rpost=Rpost, m=m,
                              int=ctr['int'], top=ctr['top'], exits=exits)
                    break
                why = 'no sweep chain'
            if ph is None:
                break
            phases.append(ph)
        else:
            def nmin(ph):
                return max([ph['m']] + [ph['m'] + x['na'] + x['nb'] for x in ph['exits']])
            if all(x['c'] >= nmin(phases[(i + 1) % L]) for i in range(L)
                   for x in phases[i]['exits']):
                return dict(F=F1, L=L, v0=v1, phases=phases), None
            why = 'block below a phase minimum'
    return None, why


def phase_fires(tabw, pins, c):
    L, F = c['L'], c['F']
    v0, i0 = c['boot'][1], c['boot'][2]
    fires = []
    for ins in sorted(tabw):
        if ins in pins:
            continue
        wit = None
        for i, ph in enumerate(c['phases']):
            cands = []
            for kind, cases in ((0, ph['int']), (1, ph['top'])):
                for idx, k in enumerate(cases):
                    cands.append((kind, idx, k['K0'], k['ch'], kind == 1, False, k))
                    ex = ph['exits'][k['ex']]
                    cands.append((kind + 2, idx, ex['S0'], ex['chs'], False, True, k))
            for kind, idx, c0, ch, el, er, k in cands:
                f = LC.reach_instr(tabw, el, er, c0, ch, ins)
                if f is None:
                    continue
                rr = LC.srun(tabw, el, er, f, c0)
                if not rr or (rr[0][0], rr[0][2]) != ins:
                    continue
                nu = k['nu'] if kind < 2 else 0
                if kind in (0, 2):
                    fam = int_family(F, v0, i0, L, i, idx, nu)
                else:
                    fam = top_family(F, v0, i0, L, i, idx, nu)
                if fam:
                    wit = (i, kind, idx, fam[0], fam[1], f)
                    break
            if wit:
                break
        if wit is None:
            return 'no fire witness for %s%d' % ('ABCD'[ins[0]], ins[1])
        fires.append(wit)
    return fires


def phase_boot(tab, c, cap):
    """the first anchor visit that is an anchor of its phase: (t, v, i, n)"""
    L, F, v0 = c['L'], c['F'], c['v0']
    for t, q, h, Ls, Rs in H.source_snaps(tab, c['src'], 0, cap + 1):
        for i, ph in enumerate(c['phases']):
            Lpre = ph['Lpre']
            if (q, h) != (ph['q'], ph['h']) or tuple(Ls[:len(Lpre)]) != tuple(Lpre):
                continue
            v = fdecode(F, tuple(Ls[len(Lpre):]))
            if v is None or (v - v0) % L != i:
                continue
            wv = fword(F, v)
            if wv is None or not lpad_eq(Ls, tuple(Lpre) + wv):
                continue
            sp = H.split_block(Rs, len(ph['Rpre']), tuple(ph['w']))
            if sp is None or sp[0] != tuple(ph['Rpre']) or sp[2] != rstrip0(ph['Rpost']):
                continue
            if sp[1] >= max([ph['m']] + [ph['m'] + x['na'] + x['nb'] for x in ph['exits']]):
                return (t, v, i, sp[1])
    return None


def find_dir(tab, N=N_STEPS):
    run = H.Run(tab, N)
    fires, cnt, _ = run.trace()
    if fires is None:
        return None, 'halts'
    pins = sorted(k for k in tab if tab[k] is None)
    tabw = dict(tab)
    keys = set(k for k, v in cnt.items() if v[0] >= 12 and v[1] >= 0.8 * v[0])
    xs = sorted(set(k[2] for k in keys))
    if not xs:
        return None, 'no anchor'
    tmin = N - N_STEPS // 2
    seqs = []
    _, _, ksn = H.Run(tab, N).trace(keep=keys, tmin=tmin)
    for key in sorted(keys):
        seqs.append((('key', key), [(t, key[0], key[1], L, R) for t, L, R in ksn[key]],
                     (1,)))
    vis = H.Run(tab, N).visits(xs, tmin=tmin)
    if vis is None:
        return None, 'halts'
    for (x, k), sn in sorted(vis.items()):
        seqs.append((('pos', (x, k)), sn, (1, 2, 3, 4)))
    why = collections.Counter()
    for src, sn, Ls in seqs:
        sn = sn[-96:]
        if len(sn) < 12:
            continue
        diffs = []
        for s1, s2 in zip(sn, sn[1:]):
            L1, L2 = s1[3], s2[3]
            i = 0
            while i < min(len(L1), len(L2)) and L1[i] == L2[i]:
                i += 1
            diffs.append(i)
        if min(diffs) > 8:
            continue
        tries = []
        for S in (1, 2, 3, 4, 6):
            for o in range(S):
                sub = sn[o::S]
                if len(sub) < 10:
                    continue
                fam = family([s[3] for s in sub])
                if fam is not None:
                    tries += [(sub, L, fam) for L in Ls]
                # the junction cells may rotate with the phase: one prefix per phase
                for L in Ls:
                    if L == 1:
                        continue
                    fams = [family([s[3] for s in sub[i::L]], L) for i in range(L)]
                    if None in fams or any(f[1]['b'] != fams[0][1]['b']
                                           or f[1]['D'] != fams[0][1]['D']
                                           or f[1]['H'] != fams[0][1]['H']
                                           or f[2] != fams[0][2] + i
                                           for i, f in enumerate(fams)) \
                            or len(set(f[0] for f in fams)) == 1:
                        continue
                    T = {}
                    if any(T.setdefault(tv, x) != x for f in fams for tv, x in f[1]['T'].items()):
                        continue
                    F = dict(fams[0][1], T=T)
                    tries.append((sub, L, ([f[0] for f in fams], F, fams[0][2])))
                if tries:
                    break
            if tries:
                break
        if not tries:
            why['no counter family'] += 1
            continue
        for sub, L, fam in tries:
            try:
                c, err = try_phases(tab, tabw, pins, sub, fam, L)
            except LC.Halt:
                c, err = None, 'halt in chain search'
            if c is None:
                why[err] += 1
                continue
            c['src'] = src
            boot = phase_boot(tab, c, BOOT_CAP)
            if boot is None:
                why['no boot'] += 1
                continue
            c['boot'] = boot
            fw = phase_fires(tabw, pins, c)
            if isinstance(fw, str):
                why[fw] += 1
                continue
            c['fires'] = fw
            c['pins'] = [list(p) for p in pins]
            for ph in c['phases']:
                for x in ph['exits']:
                    x.pop('S0', None)
                for k in ph['int'] + ph['top']:
                    k.pop('K0', None)
            return c, None
    return None, (why.most_common(1)[0][0] if why else 'no anchor')


def find(spec):
    base = H.parse(spec)
    errs = []
    for mir in (False, True):
        tab = H.mirror(base) if mir else base
        try:
            c, err = find_dir(tab)
        except LC.Halt:
            c, err = None, 'halt in chain search'
        if c:
            F = c.pop('F')
            c.update(spec=spec, mir=mir, b=F['b'], H=F['H'], D=[list(x) for x in F['D']],
                     T=[list(F['T'][e]) for e in range(F['H'])])
            return c
        errs.append(err)
    return dict(spec=spec, err=' / '.join(errs))


class Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise Timeout


def find_row(spec):
    signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(TIME_BUDGET)
    try:
        return find(spec)
    except Timeout:
        return dict(spec=spec, err='timeout')
    finally:
        signal.alarm(0)


# ------------------------------------------------------------------ render ---

def ccase(k):
    return '(mkHK %d %d %s %s)' % (k['ex'], k['nu'], H.cchain(k['ch']), H.cchains(k['base']))


def cexit(x):
    return '(mkHE %s %s %s %d %d %d %s)' % (ST[x['q2']], SYM[x['h2']], H.clist(x['Mpre']),
                                             x['c'], x['na'], x['nb'], H.cchain(x['chs']))


def render_phase(ph):
    return ('(mkHC %s %s %s %s %s %s %d\n        [%s]\n        [%s]\n        [%s])'
            % (ST[ph['q']], SYM[ph['h']], H.clist(ph['Lpre']), H.clist(ph['Rpre']),
               H.clist(ph['w']), H.clist(ph['Rpost']), ph['m'],
               '; '.join(ccase(k) for k in ph['int']), '; '.join(ccase(k) for k in ph['top']),
               ';\n         '.join(cexit(x) for x in ph['exits'])))


def render(c):
    pins = '[' + '; '.join('(%s, %s)' % (ST[q], SYM[s]) for q, s in c['pins']) + ']'
    phases = '[' + ';\n       '.join(render_phase(ph) for ph in c['phases']) + ']'
    fires = '[' + ';\n       '.join('(mkHCF %d %d %d %d %d %s)' % (i, k, x, a, bb, H.cchain(ch))
                                    for i, k, x, a, bb, ch in c['fires']) + ']'
    t0, v, i0, n0 = c['boot']
    low, tv = ctr_of(v, c['b'], c['H'])
    words = lambda ws: '[' + '; '.join(H.clist(x) for x in ws) + ']'  # noqa: E731
    cert = ('(mkHCC %s %d 0 %d\n      %s\n      %s\n      %s\n      %s\n      %d [%s] %d %d %d)'
            % (pins, c['b'], c['H'], words(c['D']), words(c['T']), phases, fires, t0,
               '; '.join(str(x) for x in low), tv, i0, n0))
    lemma = 'hc_sound_nqh_mirror' if c['mir'] else 'hc_sound_nqh'
    return 'apply coversTr_nqh, (%s _\n      %s).\n  vm_cast_no_check (eq_refl true).' % (lemma, cert)


def cmd_find(a):
    specs = [l.split()[0] for l in open(a.rows) if l.strip() and not l.startswith('#')]
    done = set()
    if os.path.exists(a.out):
        done = set(json.loads(l)['spec'] for l in open(a.out))
    todo = [s for s in specs if s not in done]
    stats = collections.Counter()
    with open(a.out, 'a') as f, Pool(a.jobs) as pool:
        for r in pool.imap_unordered(find_row, todo):
            f.write(json.dumps(r) + '\n')
            f.flush()
            stats[r.get('err', 'ok')] += 1
    for k, v in stats.most_common():
        print('%5d  %s' % (v, k))


def cmd_batch(a):
    rem = H.remaining()
    certs, seen = [], set()
    for p in a.found:
        for line in open(p):
            c = json.loads(line)
            s = c['spec']
            if 'err' in c or s not in rem or s in seen or s in a.skip:
                continue
            seen.add(s)
            certs.append(c)
    if a.limit:
        certs = certs[:a.limit]
    nn = next_free(a.tag)
    made = []
    for i in range(0, len(certs), a.chunk):
        chunk = certs[i:i + a.chunk]
        entries = [(c['spec'], render(c)) for c in chunk]
        made.append(write_batch(a.tag, nn, ['From BBB4.Checkers Require Import LapDecider.',
                                            'From BBB4.Counters Require Import HybridCtrTr.'],
                                entries, 'bouncer + counter hybrids with a base-b counter and '
                                         'a top table (HybridCtrTr, hc_check_nqh)'))
        nn += 1
    print('%d rows -> %d batch file(s): %s' % (len(certs), len(made),
          ' '.join(os.path.relpath(p, REPO) for p in made)))


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest='cmd', required=True)
    p = sp.add_parser('find')
    p.add_argument('rows')
    p.add_argument('out')
    p.add_argument('--jobs', type=int, default=4)
    p = sp.add_parser('batch')
    p.add_argument('found', nargs='+')
    p.add_argument('--tag', default='HY2')
    p.add_argument('--chunk', type=int, default=50)
    p.add_argument('--limit', type=int, default=0)
    p.add_argument('--skip', action='append', default=[])
    a = ap.parse_args()
    {'find': cmd_find, 'batch': cmd_batch}[a.cmd](a)


if __name__ == '__main__':
    main()
