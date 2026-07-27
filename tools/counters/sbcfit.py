#!/usr/bin/env python3
"""UNTRUSTED: check mxdys' SBCv1 sync-bouncer-counter certificate on a machine.

`SBCv1.v` (busycoq BB6) is NOT a decider -- it is a hypothesis-style Coq
section in exactly the shape of our own `LapDecider.v`: sixteen `Hypothesis`
rewrite rules over twelve unknown WORDS, and a `Theorem nonhalt` that follows
from them.  Upstream discharges every rule by concrete stepping (`steps` /
`execute`), so a certificate is a purely finite object and can be checked here
before anyone writes Coq.

    Config:  S0 n m = LeftBinaryCounter (xI n) <{{QL}} d' *> w0^(3+m) *> w10 *> 0^inf
    BigStep: S0 n m -->+ S0 (xI n) (2*|n| - m - 3)          for `full n`

`full n` means n = 2^k - 1, so the left binary counter is all-ones at the
overflow and `m` is its complement: this is the wiki's C'(a,b,k) with
a + b + 1 = 2^k, i.e. THE sync bouncer counter, and one overflow costs
Theta(2^k) increments.  That is the coupling `docs/BOUNCER_COUNTER_READING.md`
identified as inexpressible in `sside = pre ++ rep u (a*j+b) ++ post ++ X`:
SBCv1 expresses it by carrying the two counters as SEPARATE indices (`n`
binary on one side, `m` unary on the other) instead of one carry index `j`.

Tape conventions, checked against the source rather than assumed:

  * `Notation "xs *> r" := (Str_app xs r)`   (Helper.v:179)
  * `Notation "l <* xs" := (Str_app xs l)`   (Helper.v:180)   -- SAME operation

    so `l <* X <* Y` is the stream `Y ++ X ++ l` (later blocks nearer the
    head) while `X *> Y *> r` is `X ++ Y ++ r` (earlier blocks nearer).

  * `l <{{q}} r` reads `hd l`   and `l {{q}}> r` reads `hd r`   (TM.v:101-102)

The soundness gate is the one Coq itself imposes: a rule quantified over an
abstract side `l` (or `r`) can only be proven by `step` while the head is over
CONCRETE symbols, so a run that has to read into the abstract tail is a
FAILURE here exactly as it is there.  Tails written `const 0` are readable
(they are concrete zeros), which is why RL2 and L_overflow are allowed to
wander off the written window and the other rules are not.
"""
import argparse
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from emit_interleave import parse                                 # noqa: E402

ABST, ZEROS = 'abstract', 'zeros'


# ------------------------------------------------------------ the counters ---
def lbc(n, d0, d1, d1a):
    """LeftBinaryCounter n, as a nearest-first stream (LOW bit nearest)."""
    out = []
    while n > 1:
        out.extend(d1 if (n & 1) else d0)
        n >>= 1
    out.extend(d1a)
    return out


def runary(w0, w10, n, m):
    """RightUnaryCounter_0 n m = w0^^n *> w10 *> w0^^m *> const 0."""
    return list(w0) * n + list(w10) + list(w0) * m


def is_full(n):
    """`full n`: n is all-ones in binary, i.e. n = 2^k - 1."""
    return n >= 1 and (n & (n + 1)) == 0


# -------------------------------------------------------- abstract configs ---
def _stream(blocks, right):
    out = []
    for b in (blocks if right else reversed(blocks)):
        out.extend(b)
    return out


def cfg(q, kind, lblocks, rblocks, ltail, rtail, anchor):
    """Lay a symbolic config onto absolute cell positions.

    `anchor` names the side whose ABSTRACT boundary is pinned, so that the two
    sides of a rule are placed on the same tape.  Pinning the abstract side is
    what makes the rule's universally quantified tail line up; the `const 0`
    side is free to grow or shrink because zeros are interchangeable.
    """
    L, R = _stream(lblocks, False), _stream(rblocks, True)
    if anchor == 'L':                      # l's first cell sits at -1
        base = len(L)
    else:                                  # r's first cell sits at 0
        base = -len(R)
    tape = {}
    for i, s in enumerate(L):
        tape[base - 1 - i] = s
    for j, s in enumerate(R):
        tape[base + j] = s
    return {'q': q, 'head': base - 1 if kind == 'L' else base, 'tape': tape,
            'lo': base - len(L), 'hi': base + len(R) - 1,
            'ltail': ltail, 'rtail': rtail}


def check_rule(tab, lhs, rhs, plus=False, maxsteps=200000):
    """`lhs -->* rhs` (or `-->+`), provable by concrete stepping alone."""
    q, head = lhs['q'], lhs['head']
    tape = dict(lhs['tape'])
    lo, hi = lhs['lo'], lhs['hi']
    tq, th, ttape = rhs['q'], rhs['head'], rhs['tape']
    span = [min(lo, rhs['lo']), max(hi, rhs['hi'])]

    def matched(k):
        if (q, head) != (tq, th) or (plus and k == 0):
            return False
        return all(tape.get(p, 0) == ttape.get(p, 0)
                   for p in range(span[0], span[1] + 1))

    for k in range(maxsteps):
        if matched(k):
            return True
        if head < lo and lhs['ltail'] != ZEROS:
            return False                   # would read the abstract left tail
        if head > hi and lhs['rtail'] != ZEROS:
            return False                   # ... or the abstract right tail
        tr = tab.get((q, tape.get(head, 0)))
        if tr is None:
            return False                   # halts: no rule to be had
        w, d, nq = tr
        tape[head] = w
        span[0], span[1] = min(span[0], head), max(span[1], head)
        head += d
        q = nq
    return False


# ------------------------------------------------------------ certificates ---
FIELDS = ('QL QR d0 d1 d1p d1a d dp w0 w0p w10 w11 r0 r1 n0 m0').split()


class Cert(dict):
    def __getattr__(self, k):
        return self[k]


def rules(tab, c):
    """The twelve simulation hypotheses of SBCv1, in source order.

    Each entry is (name, lhs, rhs, plus).  `anchor` is 'L' wherever the left
    tail is the quantified `l`, and 'R' for L_overflow, whose left tail is a
    concrete `const 0` and whose right tail is the quantified `r`.
    """
    A, Z = ABST, ZEROS
    d0, d1, d1p, d1a, d, dp = c.d0, c.d1, c.d1p, c.d1a, c.d, c.dp
    w0, w0p, w10, w11 = c.w0, c.w0p, c.w10, c.w11
    r0, r1, QL, QR = c.r0, c.r1, c.QL, c.QR
    L, R = 'L', 'R'
    out = []

    def rule(name, lhs, rhs, plus=False):
        out.append((name, lhs, rhs, plus))

    # l <* d1 <{{QL}} d' *> r  -->*  l <{{QL}} d' *> d1' *> r
    rule('L_carry',
         cfg(QL, L, [d1], [dp], A, A, L),
         cfg(QL, L, [], [dp, d1p], A, A, L))
    # l <* d0 <{{QL}} d' *> r  -->+  l <* d1 <* d {{QR}}> r
    rule('LR',
         cfg(QL, L, [d0], [dp], A, A, L),
         cfg(QR, R, [d1, d], [], A, A, L), plus=True)
    # l <* d {{QR}}> d1' *> r  -->*  l <* d0 <* d {{QR}}> r
    rule('L_return',
         cfg(QR, R, [d], [d1p], A, A, L),
         cfg(QR, R, [d0, d], [], A, A, L))
    # l <* d {{QR}}> w0 *> r  -->*  l <* w0' <* d {{QR}}> r
    rule('R_carry',
         cfg(QR, R, [d], [w0], A, A, L),
         cfg(QR, R, [w0p, d], [], A, A, L))
    # l <* d {{QR}}> w10 *> w0 *> r  -->*  l <{{QL}} d' *> w11 *> w0 *> r
    rule('RL0',
         cfg(QR, R, [d], [w10, w0], A, A, L),
         cfg(QL, L, [], [dp, w11, w0], A, A, L))
    # l <* d {{QR}}> w11 *> w0 *> r  -->*  l <{{QL}} d' *> w0 *> w10 *> r
    rule('RL1',
         cfg(QR, R, [d], [w11, w0], A, A, L),
         cfg(QL, L, [], [dp, w0, w10], A, A, L))
    # l <* d {{QR}}> w10 *> 0^inf  -->*  l <{{QL}} d' *> w0 *> w10 *> 0^inf
    rule('RL2',
         cfg(QR, R, [d], [w10], A, Z, L),
         cfg(QL, L, [], [dp, w0, w10], A, Z, L))
    # l <* w0' <{{QL}} d' *> r  -->*  l <{{QL}} d' *> w0 *> r
    rule('R_return',
         cfg(QL, L, [w0p], [dp], A, A, L),
         cfg(QL, L, [], [dp, w0], A, A, L))
    # 0^inf <* d1a <{{QL}} d' *> r0 *> r  -->*  0^inf <* d1a <* d0 <* d {{QR}}> r
    rule('L_overflow',
         cfg(QL, L, [d1a], [dp, r0], Z, A, R),
         cfg(QR, R, [d1a, d0, d], [], Z, A, R))
    # l <* d {{QR}}> r1 *> w0 *> w0 *> r  -->*
    #     l <{{QL}} d' *> d1' *> w0 *> w10 *> r
    rule('R_reset',
         cfg(QR, R, [d], [r1, w0, w0], A, A, L),
         cfg(QL, L, [], [dp, d1p, w0, w10], A, A, L))
    return out


def check_cert(spec, c, initT=1000000):
    """Return (ok, list of failed hypothesis names)."""
    tab = parse(spec)
    bad = []

    # the three algebraic side conditions
    if list(c.d1p) != list(c.r0) + list(c.r1):
        bad.append('L_rotate')
    if list(c.d1p) != list(c.r1) + list(c.r0):
        bad.append("L_rotate'")
    if any(s != 0 for s in c.w10):
        bad.append('R_w10_all0')
    if not is_full(c.n0):
        bad.append('full n0')
    if c.m0 + 2 > c.n0:
        bad.append('m0+2<=n0')

    for name, lhs, rhs, plus in rules(tab, c):
        if not check_rule(tab, lhs, rhs, plus):
            bad.append(name)

    if not reach_S0(tab, c, initT):
        bad.append("init'")
    return (not bad), bad


# ------------------------------------------------------------------- init' ---
def s0_pattern(c, n, m):
    """S0 n m as (left stream nearest-first, right stream nearest-first)."""
    left = lbc(2 * n + 1, c.d0, c.d1, c.d1a)          # LeftBinaryCounter (xI n)
    right = list(c.dp) + runary(c.w0, c.w10, 3 + m, 0)
    return left, right


def reach_S0(tab, c, T):
    """c0 -->* S0 n0 m0, searched over the actual run from the blank tape."""
    left, right = s0_pattern(c, c.n0, c.m0)
    while left and left[-1] == 0:
        left.pop()
    while right and right[-1] == 0:
        right.pop()
    q, head, tape = 0, 0, {}
    lo = hi = 0
    for _ in range(T):
        if q == c.QL:
            ok = all(tape.get(head - i, 0) == left[i] for i in range(len(left)))
            if ok:
                ok = all(tape.get(head + 1 + j, 0) == right[j]
                         for j in range(len(right)))
            if ok:
                ok = all(tape.get(p, 0) == 0
                         for p in range(lo, head - len(left) + 1))
            if ok:
                ok = all(tape.get(p, 0) == 0
                         for p in range(head + 1 + len(right), hi + 1))
            if ok:
                return True
        tr = tab.get((q, tape.get(head, 0)))
        if tr is None:
            return False
        w, d, nq = tr
        tape[head] = w
        lo, hi = min(lo, head), max(hi, head)
        head += d
        q = nq
    return False


# ---------------------------------------------------------- upstream certs ---
CERT_RE = re.compile(
    r'Definition tm(\d+)\s*:=.*?TM_from_str\s*"([^"]+)".*?'
    r'solve_SBCv1\s+tm\1\s*\(\s*Build_SBC_cert_v1\s*(.*?)\)\.\s*Qed',
    re.S)
WORD_RE = re.compile(r'\[([^\]]*)\]')


def parse_upstream(path):
    """Yield (spec, Cert) for every `solve_SBCv1` in a *_solved.v file."""
    text = open(path).read()
    for m in CERT_RE.finditer(text):
        spec, body = m.group(2), m.group(3)
        states = re.match(r'\s*([A-Z])\s+([A-Z])', body)
        words = [[int(x) for x in w.group(1).replace(';', ' ').split()]
                 for w in WORD_RE.finditer(body)]
        nums = [int(x) for x in re.findall(r'(?<![\d;])(\d+)\s*\)?\s*$',
                                           body.strip())] or []
        tail = body[body.rindex(']') + 1:].split()
        if states is None or len(words) != 12 or len(tail) != 2:
            continue
        c = Cert(zip(FIELDS,
                     [ord(states.group(1)) - 65, ord(states.group(2)) - 65]
                     + words + [int(tail[0]), int(tail[1])]))
        yield spec, c


# ---------------------------------------------------------------- the search --
# Nothing below is trusted: it PROPOSES certificates, and `check_cert` above --
# validated 416/416 against mxdys' own proofs -- is what accepts them.
def mirror(spec):
    return spec.translate(str.maketrans('RL', 'LR'))


def sample_run(tab, T, want):
    """Snapshots (q, head, tape) spread over the run, for reading words off."""
    q, head, tape = 0, 0, {}
    out, every = [], max(1, T // want)
    for t in range(T):
        if t and t % every == 0:
            out.append((q, head, dict(tape)))
        tr = tab.get((q, tape.get(head, 0)))
        if tr is None:
            break
        w, d, nq = tr
        tape[head] = w
        head += d
        q = nq
    return out


def _walk(tab, tape, q, head, lo, hi, tq, th, maxsteps=2000):
    """Step inside [lo,hi] until (tq,th); reading outside is a failure.

    The window is finite and the machine deterministic, so a repeated config
    can never reach the target: bail on the spot.  Without this the search
    spends its whole budget watching junk candidates bounce.
    """
    seen = set()
    for _ in range(maxsteps):
        if q == tq and head == th:
            return tape
        if head < lo or head > hi:
            return None
        key = (q, head, tuple(tape.get(p, 0) for p in range(lo, hi + 1)))
        if key in seen:
            return None
        seen.add(key)
        tr = tab.get((q, tape.get(head, 0)))
        if tr is None:
            return None
        w, d, nq = tr
        tape[head] = w
        head += d
        q = nq
    return None


def derive_shift(tab, QR, d, blk):
    """`l <* d {{QR}}> blk *> r -->* l <* blk' <* d {{QR}}> r`; return blk'.

    Serves BOTH R_carry (blk = w0, blk' = w0') and L_return (blk = d1',
    blk' = d0) -- upstream writes them as separate hypotheses but they are the
    same rightward shift with a different block.
    """
    nd, nb = len(d), len(blk)
    tape = {nd - 1 - i: s for i, s in enumerate(d)}
    tape.update({nd + j: s for j, s in enumerate(blk)})
    tape = _walk(tab, tape, QR, nd, 0, nd + nb - 1, QR, nd + nb)
    if tape is None:
        return None
    if any(tape.get(nd + nb - 1 - i, 0) != d[i] for i in range(nd)):
        return None                        # the rule demands d comes along
    return tuple(tape.get(nb - 1 - j, 0) for j in range(nb))


def derive_lshift(tab, QL, d1, dp):
    """`l <* d1 <{{QL}} d' *> r -->* l <{{QL}} d' *> d1' *> r`; return d1'."""
    nb, nd = len(d1), len(dp)
    tape = {nb - 1 - i: s for i, s in enumerate(d1)}
    tape.update({nb + j: s for j, s in enumerate(dp)})
    tape = _walk(tab, tape, QL, nb - 1, 0, nb + nd - 1, QL, -1)
    if tape is None:
        return None
    if any(tape.get(j, 0) != dp[j] for j in range(nd)):
        return None
    return tuple(tape.get(nd + k, 0) for k in range(nb))


def derive_rl0(tab, QR, QL, d, dp, w10, w0):
    """`l <* d {{QR}}> w10 *> w0 *> r -->* l <{{QL}} d' *> w11 *> w0 *> r`."""
    nd, nw = len(d), len(w0)
    n11 = len(w10) + nd - len(dp)
    if n11 < 0:
        return None
    seq = list(w10) + list(w0)
    tape = {nd - 1 - i: s for i, s in enumerate(d)}
    tape.update({nd + j: s for j, s in enumerate(seq)})
    tape = _walk(tab, tape, QR, nd, 0, nd + len(seq) - 1, QL, -1)
    if tape is None:
        return None
    if any(tape.get(j, 0) != dp[j] for j in range(len(dp))):
        return None
    if [tape.get(len(dp) + n11 + j, 0) for j in range(nw)] != list(w0):
        return None
    return tuple(tape.get(len(dp) + j, 0) for j in range(n11))


def rotations(d1p):
    """Splits d1' = r0 ++ r1 with r0 ++ r1 = r1 ++ r0 (both L_rotate rules)."""
    L, w = len(d1p), list(d1p)
    return [(tuple(w[:k]), tuple(w[k:]))
            for k in range(L + 1) if w[k:] + w[:k] == w]


def scan_S0(tab, T, cands, kmax=12):
    """ONE pass over the run, resolving every candidate's S0 at once.

    `cands` is a list of (QL, d1, d', w0, w10); the result maps a candidate's
    index to its (n0, m0, d1a).  Doing this per candidate -- a fresh T-step
    run each time -- is what made the first cut of this search unusably slow.

    LeftBinaryCounter (xI n) for a `full n` = 2^k-1 is d1 repeated k times and
    then d1a, so the number of leading d1 copies IS k: the certificate's n0
    and its bottom-of-counter word both fall out of one match.  The prefilter
    (head symbol is d1[0], and d' sits immediately right) is the cheap
    necessary part of that same match.
    """
    by_q = {}
    for i, c in enumerate(cands):
        by_q.setdefault(c[0], []).append((i,) + c[1:])
    out = {}
    q, head, tape = 0, 0, {}
    lo = hi = 0
    for _ in range(T):
        grp = by_q.get(q)
        if grp:
            cur = tape.get(head, 0)
            for i, d1, dp, w0, w10 in grp:
                if i in out or cur != d1[0]:
                    continue
                if any(tape.get(head + 1 + j, 0) != s for j, s in
                       enumerate(dp)):
                    continue
                got = _match_S0(tape, head, lo, hi, d1, dp, w0, w10,
                                len(d1), len(dp), len(w0), kmax)
                if got is not None:
                    out[i] = got
            if len(out) == len(cands):
                break
        tr = tab.get((q, tape.get(head, 0)))
        if tr is None:
            break
        w, d, nq = tr
        tape[head] = w
        lo, hi = min(lo, head), max(hi, head)
        head += d
        q = nq
    return out


def _match_S0(tape, head, lo, hi, d1, dp, w0, w10, nb, nd, nw, kmax):
    R = [tape.get(head + 1 + j, 0) for j in range(hi - head)]
    while R and R[-1] == 0:
        R.pop()
    if R[:nd] != list(dp):
        return None
    body = R[nd:]
    if len(body) % nw and list(w0) * (len(body) // nw + 1) != \
            body + [0] * (nw - len(body) % nw):
        return None
    p = -(-len(body) // nw) if nw else 0
    if list(w0) * p != body + [0] * (p * nw - len(body)):
        return None
    m0 = p - 3
    if m0 < 0:
        return None
    L = [tape.get(head - i, 0) for i in range(head - lo + 1)]
    k = 0
    while k < kmax and L[k * nb:(k + 1) * nb] == list(d1):
        k += 1
    if k < 1:
        return None
    n0 = (1 << k) - 1
    if m0 + 2 > n0:
        return None
    d1a = L[k * nb:]
    while d1a and d1a[-1] == 0:
        d1a.pop()
    return n0, m0, tuple(d1a) + (0,) * (3 * nb)


def search(spec, T=400000, samples=200, maxdl=2, maxwl=8, maxbl=8, cap=400000,
           dbg=None):
    """Propose SBCv1 certificates for `spec`; return the first that verifies."""
    tab = parse(spec)
    snaps = sample_run(tab, T, samples)
    if not snaps:
        return None

    rc, lc = set(), set()
    for q, h, tape in snaps:
        for dl in range(maxdl + 1):
            d = tuple(tape.get(h - 1 - i, 0) for i in range(dl))
            for wl in range(1, maxwl + 1):
                w0 = tuple(tape.get(h + j, 0) for j in range(wl))
                w0p = derive_shift(tab, q, d, w0)
                if w0p is not None and w0p != w0:
                    rc.add((q, d, w0, w0p))
            dp = tuple(tape.get(h + 1 + i, 0) for i in range(dl))
            for bl in range(1, maxbl + 1):
                d1 = tuple(tape.get(h - i, 0) for i in range(bl))
                d1p = derive_lshift(tab, q, d1, dp)
                if d1p is not None:
                    lc.add((q, d1, dp, d1p))

    # Build every partial certificate the two shift rules admit, THEN resolve
    # all their S0 configs in a single pass.
    part, keys = [], []
    for QR, d, w0, w0p in sorted(rc):
        for QL, d1, dp, d1p in sorted(lc):
            if len(d) != len(dp) or len(d1) != len(d1p):
                continue
            d0 = derive_shift(tab, QR, d, d1p)     # L_return gives d0
            if d0 is None or d0 == d1:
                continue
            for w10l in range(1, len(w0) + 1):
                w10 = (0,) * w10l
                w11 = derive_rl0(tab, QR, QL, d, dp, w10, w0)
                if w11 is None:
                    continue
                part.append((QL, QR, d0, d1, d1p, d, dp, w0, w0p, w10, w11))
                keys.append((QL, d1, dp, w0, w10))
                if len(part) >= cap:
                    break
    found = scan_S0(tab, T, keys) if keys else {}
    if dbg is not None:
        dbg.update(rc=len(rc), lc=len(lc), part=len(part), s0=len(found))

    for i, (QL, QR, d0, d1, d1p, d, dp, w0, w0p, w10, w11) in enumerate(part):
        if i not in found:
            continue
        n0, m0, d1a = found[i]
        for r0, r1 in rotations(d1p):
            c = Cert(zip(FIELDS, [QL, QR, d0, d1, d1p, d1a, d, dp,
                                  w0, w0p, w10, w11, r0, r1, n0, m0]))
            ok, _ = check_cert(spec, c, initT=T)
            if ok:
                return c
    return None


def fmt(c):
    def w(x):
        return '[' + ';'.join(str(s) for s in x) + ']'
    return ' '.join(['ABCDEF'[c.QL], 'ABCDEF'[c.QR]]
                    + [w(c[k]) for k in FIELDS[2:14]]
                    + [str(c.n0), str(c.m0)])


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--upstream', help='a busycoq *_solved.v to re-check')
    ap.add_argument('--list', help='file of machine specs to search')
    ap.add_argument('--spec', help='a single machine spec to search')
    ap.add_argument('-T', type=int, default=400000)
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--debug', action='store_true',
                    help='report how far each search got before giving up')
    a = ap.parse_args()

    if a.list or a.spec:
        specs = ([a.spec] if a.spec else
                 [x.split()[0] for x in open(a.list) if x.strip()])
        if a.limit:
            specs = specs[:a.limit]
        hits = 0
        for spec in specs:
            note = []
            for tag, s in (('fwd', spec), ('mir', mirror(spec))):
                dbg = {} if a.debug else None
                c = search(s, T=a.T, dbg=dbg)
                if c is not None:
                    hits += 1
                    print('%s\tSBCV1\t%s\t%s' % (spec, tag, fmt(c)), flush=True)
                    break
                if a.debug:
                    note.append('%s:%s' % (tag, ','.join(
                        '%s=%d' % kv for kv in sorted(dbg.items()))))
            else:
                print('%s\tFAIL\t%s' % (spec, ' '.join(note)), flush=True)
        print('# %d / %d' % (hits, len(specs)), file=sys.stderr)
        return 0

    if a.upstream:
        n = ok = 0
        fails = {}
        for spec, c in parse_upstream(a.upstream):
            n += 1
            good, bad = check_cert(spec, c)
            ok += good
            if not good:
                fails.setdefault(tuple(bad), []).append(spec)
            if a.limit and n >= a.limit:
                break
        print('checked %d   accepted %d   rejected %d' % (n, ok, n - ok))
        for bad, specs in sorted(fails.items(), key=lambda kv: -len(kv[1])):
            print('  %-40s %4d  e.g. %s' % (','.join(bad), len(specs), specs[0]))
        return 0 if ok == n else 1
    ap.error('nothing to do: pass --upstream')


if __name__ == '__main__':
    sys.exit(main())
