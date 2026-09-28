#!/usr/bin/env python3
"""Bouncer + counter hybrids -> closeout batches (UNTRUSTED emitter + batch writer).

    python3 tools/closeouttr/hy_batch.py find ROWS.txt OUT.jsonl [--jobs 4]
    python3 tools/closeouttr/hy_batch.py batch OUT.jsonl [...] --tag HY [--chunk 40]

A hybrid (SCOPING_INSTR.md 7.4.DX/7.4.HY) keeps a binary counter at one
end of the tape and a bouncer block [w^n] beside it.  Each lap increments
the counter once (at its low end, next to the block) and sweeps the block
one or more times, growing it.  Its anchor is two-index,

    hyC p n = (q, (Lpre ++ E p, h, Rpre ++ w^n ++ Rpost))

with E the counter word (E xH = C, E (xO r) = A ++ E r, E (xI r) = B ++ E r),
possibly in L phases that cycle with the lap, and
theories/Counters/HybridGlueTr.v decides a certificate [hycert] for it with
one boolean check, [hy_check_nqh] / [hy_check_qh].  `find`:

  1. runs the machine (and its mirror) for N steps; pins the undefined
     instructions (never-QH rows) or also those silent since the scan's
     quiet point (QH rows, run past it);
  2. collects anchor sequences: the fires of one instruction at one cell
     whose left neighbours change between visits, and the k-th visit of a
     cell after each sweep (sub-sampled every S sweeps, S = 1..4);
  3. reads the counter family (Lpre, A, B, C) off the left sides and the
     block (Rpre, w, Rpost) off the right sides, per phase for L = 1..4;
  4. reads each phase's mid configuration (the counter incremented, the
     head about to step past [Rpre ++ w^m]) off the simulation, and derives
     with tools/counters/lapcert.derive_chain the interior and overflow
     counter chains (block opaque), their concrete short carries, and the
     sweep chain (counter opaque) onto the next phase's anchor;
  5. the earliest boot, and a chain prefix firing each unpinned instruction
     (with the counter-value family that reaches it in its phase).

Everything is re-checked by the kernel; a wrong certificate fails to
compile, it cannot mis-prove.  Only rows still in closeouttr_remaining.txt
are written.  Compile each batch before committing; drop a row Coq rejects
with --skip SPEC.  Then run tools/closeouttr/gen_closeout_tr.py.
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
from cbt import REPO, next_free, write_batch  # noqa: E402
import lapcert as LC                           # noqa: E402

N_STEPS = 400000
BOOT_CAP = 200000        # never-QH boots: the first anchors come early
QH_CAP = 2 ** 24         # HybridGlueTr.hy_check_qh: Nat.log2 t0 < 24
MAX_WORD = 160           # counter words longer than this are not counters
TIME_BUDGET = 240        # seconds a row
ST = ['StA', 'StB', 'StC', 'StD']
SYM = ['S0', 'S1']


def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab


def mirror(tab):
    return {k: (None if v is None else (v[0], -v[1], v[2])) for k, v in tab.items()}


def rstrip0(t):
    i = len(t)
    while i and t[i - 1] == 0:
        i -= 1
    return tuple(t[:i])


def lpad_eq(a, b):
    return rstrip0(a) == rstrip0(b)


def sflat(w):
    return (tuple(w), (), 0, 0, ())


# ------------------------------------------------------------- simulation ---

class Run:
    """one concrete run, with the tape kept as a bytearray around an offset"""

    def __init__(self, tab, n):
        self.tab = tab
        size = 2 * n + 16 if n < 50000 else 4 * int(n ** 0.5) * 8 + 200000
        self.size = size
        self.off = size // 2
        self.n = n

    def trace(self, keep=None, tmin=0):
        """-> fires {(q,h): [t]}, and for the keys in [keep] ((q, h, x)
        absolute), the snapshots (t, L, R), nearest first, blanks stripped"""
        tab, tape, pos, q = self.tab, bytearray(self.size), self.off, 0
        lo = hi = pos
        fires = collections.defaultdict(list)
        cnt = {}
        snaps = collections.defaultdict(list)
        half = self.n // 2
        for t in range(self.n):
            h = tape[pos]
            fires[(q, h)].append(t)
            if t >= half and keep is None:
                k = (q, h, pos - self.off)
                fp = bytes(tape[pos - 6:pos])
                e = cnt.get(k)
                if e is None:
                    cnt[k] = [1, 0, fp]
                else:
                    e[0] += 1
                    if e[2] != fp:
                        e[1] += 1
                        e[2] = fp
            if keep is not None and t >= tmin and (q, h, pos - self.off) in keep:
                L = rstrip0(tape[lo:pos][::-1])
                R = rstrip0(tape[pos + 1:hi + 1])
                snaps[(q, h, pos - self.off)].append((t, L, R))
            tr = tab[(q, h)]
            if tr is None:
                return None, None, None
            w, d, nq = tr
            tape[pos] = w
            pos += d
            q = nq
            if pos < lo:
                lo = pos
            elif pos > hi:
                hi = pos
            if pos <= 0 or pos >= self.size - 1:
                return None, None, None
        self.final = (tape, pos, q, lo, hi)
        return fires, cnt, snaps

    def visits(self, xs, far=16, tmin=0, kmax=3):
        """for each absolute position x in [xs]: the k-th visit of x (k <=
        kmax) after each excursion of the head to x + far or beyond, as
        {(x, k): [(t, q, h, L, R)]}, sides nearest first, blanks stripped.
        The head moves one cell a step, so an excursion past x + far since
        the last visit of x is a visit of x + far after it."""
        tab, tape, pos, q = self.tab, bytearray(self.size), self.off, 0
        lo = hi = pos
        xs = set(x + self.off for x in xs)
        last = [-1] * self.size         # the last visit of each cell
        prev = {x: -1 for x in xs}      # the previous visit of x
        cnt = {x: 0 for x in xs}        # visits since the last excursion
        out = collections.defaultdict(list)
        for t in range(self.n):
            h = tape[pos]
            if pos in cnt:
                if last[pos + far] > prev[pos]:
                    cnt[pos] = 0
                prev[pos] = t
                cnt[pos] += 1
                if cnt[pos] <= kmax and t >= tmin:
                    L = rstrip0(tape[lo:pos][::-1])
                    R = rstrip0(tape[pos + 1:hi + 1])
                    out[(pos - self.off, cnt[pos])].append((t, q, h, L, R))
            last[pos] = t
            tr = tab[(q, h)]
            if tr is None:
                return None
            w, d, nq = tr
            tape[pos] = w
            pos += d
            q = nq
            if pos < lo:
                lo = pos
            elif pos > hi:
                hi = pos
            if pos <= far or pos >= self.size - 1 - far:
                return None
        return out


def concrete(tab, cfg, n):
    """step a (q, L, h, R) configuration n times (unbounded tape)"""
    q, L, h, R = cfg
    L, R = list(L), list(R)
    for _ in range(n):
        tr = tab[(q, h)]
        if tr is None:
            return None
        w, d, nq = tr
        if d > 0:
            L.insert(0, w)
            h = R.pop(0) if R else 0
        else:
            R.insert(0, w)
            h = L.pop(0) if L else 0
        q = nq
    return q, tuple(L), h, tuple(R)


# ----------------------------------------------------------- the families ---

def E(p, A, B, C):
    out = []
    while p > 1:
        out += A if p % 2 == 0 else B
        p //= 2
    return tuple(out + list(C))


def decode(word, A, B, C):
    """word = E p (up to trailing blanks) -> p, else None"""
    d = len(A)
    word = rstrip0(word)
    if len(word) > MAX_WORD:
        return None             # a counter word is short (log growth)
    Cs = rstrip0(C)
    n, k = len(word), len(Cs)
    v, bit, i = 0, 1, 0
    while True:
        if n - i == k and word[i:] == Cs:
            return v + bit
        if i + d > n and n - i < k:
            return None
        ch = word[i:i + d]
        if len(ch) < d:
            ch = ch + (0,) * (d - len(ch))
        if ch == A:
            pass
        elif ch == B:
            v += bit
        else:
            return None
        bit *= 2
        i += d
        if i > n:
            return None


def counter_family(Ls, step=1):
    """Ls: left sides at consecutive anchors.  -> (Lpre, A, B, C, p0) with
    Ls[k] = Lpre ++ E (p0 + k) (up to trailing blanks), or None"""
    first = min(len(x) for x in Ls)
    if min(len(rstrip0(x)) for x in Ls[-3:]) > MAX_WORD + 8:
        return None
    for lp in range(0, 5):
        if lp > first:
            break
        pre = Ls[0][:lp]
        if any(x[:lp] != pre for x in Ls):
            break
        W = [x[lp:] for x in Ls]
        Ws = [rstrip0(w) for w in W]
        for d in (1, 2, 3, 4):
            # the low digit flips at every increment
            lows = [w[:d] + (0,) * (d - len(w[:d])) for w in W[-4:]]
            if any(a == b for a, b in zip(lows, lows[1:])) or len(set(lows)) != 2:
                continue
            for A, B in ((lows[-1], lows[-2]), (lows[-2], lows[-1])):
                for cl in range(1, 7):
                    w0 = Ws[-1]
                    if cl > len(w0):
                        break
                    C = w0[len(w0) - cl:]
                    if any(w[len(w) - cl:] != C for w in Ws[-3:-1]):
                        continue
                    # cheap test on the last three words first
                    tail = [decode(w, A, B, C) for w in W[-3:]]
                    if None in tail or tail[1] != tail[0] + step or tail[2] != tail[1] + step:
                        continue
                    vals = [decode(w, A, B, C) for w in W]
                    if None in vals:
                        continue
                    if all(b == a + step for a, b in zip(vals, vals[1:])):
                        if all(lpad_eq(E(v, A, B, C), w) for v, w in zip(vals, W)):
                            return tuple(pre), A, B, C, vals[0]
    return None


def split_block(R, lp, u):
    if len(R) < lp:
        return None
    i, x = 0, lp
    while R[x:x + len(u)] == u:
        i += 1
        x += len(u)
    return R[:lp], i, rstrip0(R[x:])


def block_family(Rs):
    """Rs: right sides at consecutive anchors -> [(Rpre, w, Rpost, ns)]"""
    out = []
    Rm = Rs[-1]
    for lp in range(0, 4):
        for a in (1, 2, 3, 4, 5, 6, 7, 8):
            u = Rm[lp:lp + a]
            if len(u) < a or not any(u):
                continue
            sp = [split_block(R, lp, u) for R in Rs]
            if any(s is None for s in sp):
                continue
            if len(set((s[0], s[2]) for s in sp)) != 1:
                continue
            ns = [s[1] for s in sp]
            if ns[-1] <= ns[0]:
                continue
            out.append((sp[0][0], u, sp[0][2], ns))
    return out


# --------------------------------------------------------------- the laps ---

def end_counter_ok(c1, q2, h2, Mpre, A, nlap, post, el):
    """HybridGlueTr.hy_cend_ok: the left side denotes Mpre ++ rep A (j + c) ++ post"""
    cq, cl, ch, cr = c1
    if not (cq == q2 and ch == h2 and cr[0] == () and cr[1] == () and cr[4] == ()
            and cl[1] == A and cl[2] == 1 and cl[3] <= nlap):
        return False
    for x in range(nlap - cl[3] + 1):
        rest = A * (nlap - cl[3] - x) + post
        if cl[0] == Mpre + A * x and (lpad_eq(cl[4], rest) if el else cl[4] == rest):
            return True
    return False


def end_cbase_ok(c1, q2, h2, want, el):
    cq, cl, ch, cr = c1
    return (cq == q2 and ch == h2 and cr[0] == () and cr[1] == () and cr[4] == ()
            and cl[1] == () and cl[4] == ()
            and (lpad_eq(cl[0], want) if el else cl[0] == tuple(want)))


def end_sweep_ok(c1, q, h, Lpre, Rpre, w, Rpost, c):
    """SweepGlueTr's [sside_end_is] on the right, flat [Lpre] on the left"""
    cq, cl, ch, cr = c1
    if not (cq == q and ch == h and cl == (tuple(Lpre), (), cl[2], cl[3], ())
            and cr[1] == w and cr[2] == 1 and cr[3] <= c):
        return False
    return any(cr[0] == Rpre + w * x and lpad_eq(cr[4], w * (c - cr[3] - x) + Rpost)
               for x in range(c - cr[3] + 1))


def derive(tabw, el, er, c0, targets, check):
    for tg in targets:
        try:
            ch = LC.derive_chain(tabw, el, er, c0, tg, lift=el or er)
        except LC.Halt:
            ch = None
        if ch is None:
            continue
        r = LC.srun(tabw, el, er, ch, c0)
        if r is not None and check(r):
            return ch
    return None


def cview(p):
    """MonoCounter.cview: (trailing ones, Some high part) or (ones, None)"""
    j = 0
    while p % 2 == 1 and p > 1:
        j += 1
        p //= 2
    if p == 1:
        return j + 1, None
    return j, p // 2


def mid_of(tab, anc, x_r):
    """run the lap from the anchor configuration until the head is about to
    step right past relative cell x_r; -> the configuration then"""
    q, L, h, R = anc
    L, R = list(L), list(R)
    pos = 0
    for _ in range(20000):
        if pos == x_r:
            tr = tab[(q, h)]
            if tr is not None and tr[1] > 0:
                return q, tuple(L), h, tuple(R)
        tr = tab[(q, h)]
        if tr is None:
            return None
        w, d, nq = tr
        if d > 0:
            L.insert(0, w)
            h = R.pop(0) if R else 0
        else:
            R.insert(0, w)
            h = L.pop(0) if L else 0
        pos += d
        q = nq
        if pos > x_r:
            return None
    return None


NANB = ((0, 0), (1, 0), (0, 1), (1, 1), (2, 0), (0, 2), (2, 1), (1, 2), (2, 2))


def phase_mid(tab, cls, Lpre, A, B, C, pc0, L, i, blk, m):
    """the mid of phase [i] at block offset [m], read off every snapshot of
    the phase: (q2, h2, Mpre), or None"""
    Rpre, w, Rpost, ns = blk
    x_r = len(Rpre) + m * len(w)
    Mlen = x_r + len(Lpre)
    got = None
    for k, (t, q, h, Ls, Rs) in enumerate(cls):
        p = pc0 + i + L * k
        n = ns[k]
        if n < m + 1:
            return None
        mc = mid_of(tab, (q, Ls, h, Rs), x_r)
        if mc is None:
            return None
        mq, mL, mh, mR = mc
        if got is None:
            got = (mq, mh, mL[:Mlen])
        if (mq, mh, mL[:Mlen]) != got or not lpad_eq(mL[Mlen:], E(p + 1, A, B, C)) \
                or not lpad_eq(mR, w * (n - m) + Rpost):
            return None
    return got


def phase_counter(tabw, q, h, Lpre, A, B, C, Rpre, w, m, q2, h2, Mpre):
    """the counter half of one phase: interior and overflow chains with
    their concrete short carries"""
    Rw = Rpre + w * m
    out = {}
    for nu in (0, 1, 2):
        A0 = (q, (Lpre + B * nu, B, 1, 0, A), h, sflat(Rw))
        tg = [(q2, (Mpre + A * x, A, 1, nu - x, B), h2, sflat(())) for x in range(nu + 1)]
        chi = derive(tabw, False, False, A0, tg,
                     lambda r: end_counter_ok(r[0], q2, h2, Mpre, A, nu, B, False))
        if chi is None:
            continue
        ibase = []
        for j in range(nu):
            S0 = (q, sflat(Lpre + B * j + A), h, sflat(Rw))
            want = Mpre + A * j + B
            ch = derive(tabw, False, False, S0, [(q2, sflat(want), h2, sflat(()))],
                        lambda r: end_cbase_ok(r[0], q2, h2, want, False))
            if ch is None:
                break
            ibase.append(ch)
        else:
            out.update(nu=nu, chi=chi, ibase=ibase, A0=A0)
            break
    if 'chi' not in out:
        return 'no interior chain'
    for no in (0, 1, 2):
        B0 = (q, (Lpre + B * no, B, 1, 0, C), h, sflat(Rw))
        tg = [(q2, (Mpre + A * x, A, 1, no + 1 - x, C), h2, sflat(())) for x in range(no + 2)]
        cho = derive(tabw, True, False, B0, tg,
                     lambda r: end_counter_ok(r[0], q2, h2, Mpre, A, no + 1, C, True))
        if cho is None:
            continue
        obase = []
        for j in range(no):
            S0 = (q, sflat(Lpre + B * j + C), h, sflat(Rw))
            want = Mpre + A * (j + 1) + C
            ch = derive(tabw, True, False, S0, [(q2, sflat(want), h2, sflat(()))],
                        lambda r: end_cbase_ok(r[0], q2, h2, want, True))
            if ch is None:
                break
            obase.append(ch)
        else:
            out.update(no=no, cho=cho, obase=obase, B0=B0)
            break
    if 'cho' not in out:
        return 'no overflow chain'
    return out


def phase_sweep(tabw, q2, h2, Mpre, w, Rpost, m, d, nxt):
    """the sweep of one phase, onto the next phase's anchor [nxt]:
    [n - nmin] units -> [n + d] of the next phase's units"""
    nq, nLpre, nh, nRpre, nw, nRpost = nxt
    for na, nb in NANB:
        c = na + nb + m + d
        if c < 0:
            continue
        S0 = (q2, sflat(Mpre), h2, (w * na, w, 1, 0, w * nb + Rpost))
        tg = [(nq, sflat(nLpre), nh, (nRpre + nw * x, nw, 1, c - x, nRpost))
              for x in range(c + 1)]
        chs = derive(tabw, False, True, S0, tg,
                     lambda r: r[2] > 0 and end_sweep_ok(r[0], nq, nh, nLpre, nRpre, nw,
                                                        nRpost, c))
        if chs is not None:
            return dict(na=na, nb=nb, chs=chs, c=c, S0=S0)
    return 'no sweep chain'


def int_family(p0, i0, L, i, nu):
    """(j, r0): ones_on j (xO (r0 + L s)) lies in phase i for every s"""
    for j in range(nu, nu + 2 * L + 3):
        for r0 in range(max(1, p0), max(1, p0) + 2 * L + 2):
            x = 2 ** (j + 1) * r0 + 2 ** j - 1
            if x >= p0 and (i0 + x - p0) % L == i:
                return j, r0
    return None


def ovf_family(p0, i0, L, i, no):
    """(k0, T): ones_on (k0 + T s) xH lies in phase i for every s"""
    for k0 in range(max(no, p0.bit_length()), max(no, p0.bit_length()) + 4 * L + 4):
        a = 2 ** (k0 + 1)
        if a - 1 < p0 or (i0 + a - 1 - p0) % L != i:
            continue
        for T in range(1, 4 * L + 1):
            if (2 ** (k0 + 1 + T)) % L == a % L:
                return k0, T
    return None


def try_phases(tab, tabw, pins, x, snaps, fam, L):
    """a certificate with L phases from consecutive-lap snapshots"""
    Lpre, A, B, C, pc0 = fam
    # one prefix for every phase, or (per-phase families) one per phase
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
        # n at lap k (phase k mod L, index k // L in its class)
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
        phases = []
        for i in range(L):
            q, h = qh_[i]
            Rpre, w, Rpost, ns = combo[i]
            ph = None
            for m in (0, 1, 2):
                mid = phase_mid(tab, cls[i], Lpres[i], A, B, C, pc0, L, i, combo[i], m)
                if mid is None:
                    why = 'no mid'
                    continue
                q2, h2, Mpre = mid
                ctr = phase_counter(tabw, q, h, Lpres[i], A, B, C, Rpre, w, m, q2, h2, Mpre)
                if isinstance(ctr, str):
                    why = ctr
                    continue
                j = (i + 1) % L
                nxt = (qh_[j][0], Lpres[j], qh_[j][1], combo[j][0], combo[j][1], combo[j][2])
                sw = phase_sweep(tabw, q2, h2, Mpre, w, Rpost, m, ds[i], nxt)
                if isinstance(sw, str):
                    why = sw
                    continue
                ph = dict(q=q, h=h, Lpre=Lpres[i], Rpre=Rpre, w=w, Rpost=Rpost, m=m,
                          q2=q2, h2=h2, Mpre=Mpre, **ctr, **sw)
                break
            if ph is None:
                break
            phases.append(ph)
        else:
            if all(phases[i]['c'] >= phases[(i + 1) % L]['m'] + phases[(i + 1) % L]['na']
                   + phases[(i + 1) % L]['nb'] for i in range(L)):
                return dict(A=A, B=B, C=C, L=L, pc0=pc0, x=x, phases=phases), None
            why = 'block below a phase minimum'
    return None, why


def phase_fires(tab, tabw, pins, c):
    """a chain prefix firing each unpinned instruction, in some phase, with
    the counter family that reaches it"""
    L, p0, i0 = c['L'], c['boot'][1], c['boot'][2]
    fires = []
    for ins in sorted(tab):
        if ins in pins:
            continue
        wit = None
        for i, ph in enumerate(c['phases']):
            for kind, c0, ch, el, er in ((2, ph['S0'], ph['chs'], False, True),
                                         (0, ph['A0'], ph['chi'], False, False),
                                         (1, ph['B0'], ph['cho'], True, False)):
                f = LC.reach_instr(tabw, el, er, c0, ch, ins)
                if f is None:
                    continue
                rr = LC.srun(tabw, el, er, f, c0)
                if not rr or (rr[0][0], rr[0][2]) != ins:
                    continue
                if kind == 2:
                    wit = (i, 2, 0, 0, f)
                elif kind == 0:
                    fam = int_family(p0, i0, L, i, ph['nu'])
                    if fam:
                        wit = (i, 0, fam[0], fam[1], f)
                else:
                    fam = ovf_family(p0, i0, L, i, ph['no'])
                    if fam:
                        wit = (i, 1, fam[0], fam[1], f)
                if wit:
                    break
            if wit:
                break
        if wit is None:
            return 'no fire witness for %s%d' % ('ABCD'[ins[0]], ins[1])
        fires.append(wit)
    return fires


def source_snaps(tab, src, tmin, n):
    """the anchor sequence [src] over steps [tmin, n): (t, q, h, L, R)"""
    kind, key = src
    run = Run(tab, n)
    if kind == 'key':
        _, _, sn = run.trace(keep={key}, tmin=tmin)
        if sn is None:
            return []
        return [(t, key[0], key[1], L, R) for t, L, R in sn[key]]
    vis = run.visits([key[0]], tmin=tmin)
    return [] if vis is None else vis.get(key, [])


def phase_boot(tab, c, lastq, cap):
    """the first anchor visit (after the last quiet fire) that is an anchor
    of its phase: (t, p, i, n)"""
    L, pc0 = c['L'], c['pc0']
    A, B, C = c['A'], c['B'], c['C']
    for t, q, h, Ls, Rs in source_snaps(tab, c['src'], lastq + 1, cap + 1):
        for i, ph in enumerate(c['phases']):
            Lpre = ph['Lpre']
            if (q, h) != (ph['q'], ph['h']) or tuple(Ls[:len(Lpre)]) != tuple(Lpre):
                continue
            v = decode(tuple(Ls[len(Lpre):]), A, B, C)
            if v is None or (v - pc0) % L != i or not lpad_eq(Ls, tuple(Lpre) + E(v, A, B, C)):
                continue
            sp = split_block(Rs, len(ph['Rpre']), tuple(ph['w']))
            if sp is None or sp[0] != tuple(ph['Rpre']) or sp[2] != rstrip0(ph['Rpost']):
                continue
            if sp[1] >= ph['m'] + ph['na'] + ph['nb']:
                return (t, v, i, sp[1])
    return None


def find_dir(tab, qh, N=N_STEPS, qcut=None):
    run = Run(tab, N)
    fires, cnt, _ = run.trace()
    if fires is None:
        return None, 'halts'
    # never-QH rows pin only the undefined instructions (a rare carry
    # instruction may well be silent over the whole run); QH rows also pin
    # the instructions silent over the last two thirds
    pins = sorted(k for k in tab if tab[k] is None or (qh and (
        not fires.get(k) or fires[k][-1] < (qcut or N // 3))))
    quiet = [k for k in pins if tab[k] is not None and fires.get(k)]
    if qh and not quiet:
        return None, 'no quiet instruction'
    lastq = max((fires[k][-1] for k in quiet), default=-1)
    tabw = {k: (None if k in pins else v) for k, v in tab.items()}
    # candidate positions: an instruction fires there about once per lap
    # and the six cells to the left change between visits (the counter's
    # low end)
    xs = sorted(set(k[2] for k, v in cnt.items() if v[0] >= 12 and v[1] >= 0.8 * v[0]))
    if not xs:
        return None, 'no anchor'
    tmin = max(lastq + 1, N - N_STEPS // 2)
    keys = set(k for k, v in cnt.items() if v[0] >= 12 and v[1] >= 0.8 * v[0])
    seqs = []
    # 1. per instruction and position (the anchor is one (state, symbol))
    run1 = Run(tab, N)
    _, _, ksn = run1.trace(keep=keys, tmin=tmin)
    for key in sorted(keys):
        seqs.append((('key', key), [(t, key[0], key[1], L, R) for t, L, R in ksn[key]], (1,)))
    # 2. per position, the k-th visit after a sweep (the phase may change the
    #    state and symbol there)
    run2 = Run(tab, N)
    vis = run2.visits(xs, tmin=tmin)
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
        if min(diffs) > 6:
            continue
        # the counter may step once every [S] sweeps: sub-sample
        found = None
        for S in (1, 2, 3, 4):
            for o in range(S):
                sub = sn[o::S]
                if len(sub) < 10:
                    continue
                fam = counter_family([s[3] for s in sub])
                if fam is not None:
                    found = (S, o, sub, fam)
                    break
            if found:
                break
        if found is None:
            sub, tries = sn, []
        else:
            S, o, sub, fam = found
            tries = [(L, fam) for L in Ls]
        # the junction cells may rotate with the phase: one prefix per phase
        for L in Ls:
            if L == 1:
                continue
            fams = [counter_family([s[3] for s in sub[i::L]], L) for i in range(L)]
            if None in fams or len(set(f[1:4] for f in fams)) != 1 \
                    or any(f[4] != fams[0][4] + i for i, f in enumerate(fams)) \
                    or len(set(f[0] for f in fams)) == 1:
                continue
            tries.append((L, ([f[0] for f in fams],) + fams[0][1:]))
        if not tries:
            why['no counter family'] += 1
            continue
        for L, fam in tries:
            c, err = try_phases(tab, tabw, pins, src, sub, fam, L)
            if c is None:
                why[err] += 1
                continue
            c['src'] = src
            boot = phase_boot(tab, c, lastq, QH_CAP - 1 if qh else BOOT_CAP)
            if boot is None:
                why['no boot'] += 1
                continue
            c['boot'] = boot
            fw = phase_fires(tab, tabw, pins, c)
            if isinstance(fw, str):
                why[fw] += 1
                continue
            c['fires'] = fw
            c['pins'] = [list(p) for p in pins]
            for ph in c['phases']:
                for key in ('A0', 'B0', 'S0'):
                    ph.pop(key, None)
            return c, None
    return None, (why.most_common(1)[0][0] if why else 'no anchor')


def find(spec, qh=False, lastq=0):
    base = parse(spec)
    errs = []
    for mir in (False, True):
        tab = mirror(base) if mir else base
        try:
            # a QH row's quiet instruction may stop late (the hybrids: near
            # step 8M): run half as long again past it
            if qh and lastq > N_STEPS // 3:
                c, err = find_dir(tab, qh, 3 * lastq // 2 + N_STEPS, lastq + 1)
            else:
                c, err = find_dir(tab, qh)
        except LC.Halt:
            c, err = None, 'halt in chain search'
        if c:
            c.update(spec=spec, mir=mir, qh=qh)
            return c
        errs.append(err)
    return dict(spec=spec, err=' / '.join(errs))


class Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise Timeout


def find_row(line):
    spec, cls = line
    signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(TIME_BUDGET)
    try:
        return find(spec, cls[0] == 'QH', cls[1])
    except Timeout:
        return dict(spec=spec, err='timeout')
    finally:
        signal.alarm(0)


# ------------------------------------------------------------------ render ---

def clist(xs):
    return '[' + ';'.join(SYM[x] for x in xs) + ']'


def cstep(st):
    return '(%s)' % ' '.join([st[0]] + [str(x) for x in st[1:]])


def cchain(ch):
    return '[' + '; '.join(cstep(tuple(s)) for s in ch) + ']'


def cchains(chs):
    return '[' + '; '.join(cchain(ch) for ch in chs) + ']'


def render_phase(ph):
    return ('(mkHP %s %s %s %s %s %s %d\n        %s %s %s %d\n        %d %s %s\n'
            '        %d %s %s\n        %d %d %s)'
            % (ST[ph['q']], SYM[ph['h']], clist(ph['Lpre']), clist(ph['Rpre']), clist(ph['w']),
               clist(ph['Rpost']), ph['m'], ST[ph['q2']], SYM[ph['h2']], clist(ph['Mpre']),
               ph['c'], ph['nu'], cchain(ph['chi']), cchains(ph['ibase']),
               ph['no'], cchain(ph['cho']), cchains(ph['obase']),
               ph['na'], ph['nb'], cchain(ph['chs'])))


def render(c):
    pins = '[' + '; '.join('(%s, %s)' % (ST[q], SYM[s]) for q, s in c['pins']) + ']'
    phases = '[' + ';\n       '.join(render_phase(ph) for ph in c['phases']) + ']'
    fires = '[' + ';\n       '.join('(mkHF %d %d %d %d %s)' % (i, k, a, b, cchain(ch))
                                    for i, k, a, b, ch in c['fires']) + ']'
    t0, p0, i0, n0 = c['boot']
    cert = ('(mkHY %s %s %s %s\n      %s\n      %s\n      %d (%d)%%positive %d %d)'
            % (pins, clist(c['A']), clist(c['B']), clist(c['C']), phases, fires, t0, p0, i0, n0))
    if c['qh']:
        lemma = 'hy_sound_qh_mirror' if c['mir'] else 'hy_sound_qh'
        return 'apply coversTr_qh3, (%s _\n      %s).\n  vm_cast_no_check (eq_refl true).' % (lemma, cert)
    lemma = 'hy_sound_nqh_mirror' if c['mir'] else 'hy_sound_nqh'
    return 'apply coversTr_nqh, (%s _\n      %s).\n  vm_cast_no_check (eq_refl true).' % (lemma, cert)


def remaining():
    return set(l.strip() for l in open(os.path.join(REPO, 'closeouttr_remaining.txt')))


def classes():
    out = {}
    for l in open(os.path.join(REPO, 'closeouttr_classes.tsv')):
        if l.startswith('#'):
            continue
        f = l.rstrip('\n').split('\t')
        out[f[0]] = (f[1], max(0, int(f[2])))
    return out


def cmd_find(a):
    specs = [l.split()[0] for l in open(a.rows) if l.strip() and not l.startswith('#')]
    done = set()
    if os.path.exists(a.out):
        done = set(json.loads(l)['spec'] for l in open(a.out))
    cls = classes()
    todo = [(s, cls.get(s, ('DN', 0))) for s in specs if s not in done]
    stats = collections.Counter()
    with open(a.out, 'a') as f, Pool(a.jobs) as pool:
        for r in pool.imap_unordered(find_row, todo):
            f.write(json.dumps(r) + '\n')
            f.flush()
            stats[r.get('err', 'ok')] += 1
    for k, v in stats.most_common():
        print('%5d  %s' % (v, k))


def cmd_batch(a):
    rem = remaining()
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
                                            'From BBB4.Counters Require Import HybridGlueTr.'],
                                entries, 'bouncer + counter hybrids by the counter-and-block '
                                         'lap glue (HybridGlueTr, hy_check)'))
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
    p.add_argument('--tag', default='HY')
    p.add_argument('--chunk', type=int, default=40)
    p.add_argument('--limit', type=int, default=0)
    p.add_argument('--skip', action='append', default=[])
    a = ap.parse_args()
    {'find': cmd_find, 'batch': cmd_batch}[a.cmd](a)


if __name__ == '__main__':
    main()
