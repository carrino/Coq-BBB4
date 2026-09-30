#!/usr/bin/env python3
"""Block-LIST glue (UNTRUSTED finder + batch writer) for
theories/Counters/ListGlueTr.v, SCOPING_INSTR.md §7.4.BLC.

    python3 tools/closeouttr/lg_batch.py find ROWS.txt OUT.jsonl [--jobs 4] [--timeout 300]
    python3 tools/closeouttr/lg_batch.py batch OUT.jsonl [...] --tag BLC [--chunk 10]

The rows of §7.4.BL piece (a) keep a LIST of blocks whose lengths follow a
neighbour recurrence ([b_(i+1) = a b_i + d_i], the offset [d_i] a finite
digit).  TriGlueTr's families are whole symbolic tapes with a fixed number of
blocks; on these rows the block count grows, and TI stops at "too many
families".  Here a family is a TriGlue family (the WINDOW: literal words and
blocks with affine exponents) plus, on each side, an optional TAIL: a list of
ITEMS [pre u^e] (nearest-first) accepted by an automaton whose transitions
carry the neighbour relation of an item to the one before it:

    up   (a, d):  e      = a * e_prev + d
    down (a, d):  e_prev = a * e      + d      (a = 0: e_prev = d and e = 0)

The first item relates to the family's REF, an affine expression over the
family's variables.  A leaf of a family may UNFOLD tail items into its window
(a dispatch on the tail's first item: which transition it takes), runs ONE
LapDecider chain on the window (the tail is the chain's opaque rest), and
lands on a family whose window may FOLD its outermost items back into the
tail.  Every relation is an identity of affine forms, checked coefficient
by coefficient.  Liveness: TriGlue's (leaf, residue) nodes, with rankings
that add a per-kind affine weight [alpha e + beta] for every tail item.

`find` builds the certificate by symbolic execution from a boot tape (as
ti_batch.py, which it extends), learning the item kinds and the automaton
while it explores; every check of the kernel checker is replayed in Python
before a certificate is written.  The kernel re-checks everything: a wrong
certificate fails to compile, it cannot mis-prove.
"""
import argparse
import collections
import json
import math
import os
import signal
import sys
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ti_batch as T                            # noqa: E402
import ti_coq as C                              # noqa: E402

LC = C.LC
Fail, Req = T.Fail, T.Req

MAXFAM = 200
MAXLEAF = 3000
MAXSTEPS = 60000
CUTSTEPS = 400
MAXNA = 8
MAXNFA = 400
MAXROUNDS = 20000
MAXUNF = 3
VERBOSE = bool(os.environ.get('LG_VERBOSE'))
T0S = (20000, 100000)
PLIST = (1, 2)
KEEP = 1            # blocks kept in the window on a tail side
MAXD = 16           # largest offset of a relation guessed from two constants
MAXSHIFT = 4        # largest offset of a shifted automaton state
BOOT_AMAX = 4
# fold only canonical items (§7.4.BLC2): a tail's ref is always the exponent
# of the outermost window block of its side, so tail items never carry an
# offset and the automaton is {unit} x {digit}.  LG_CANON=0 restores BLC's
# shifted states.
CANON = os.environ.get('LG_CANON', '1') != '0'


class NonCanon(Exception):
    """a leaf's end leaves the tail of side [sd] shifted against the window
    (the block its ref names was modified, or is gone): unfold that side's
    next item at the leaf's start"""

    def __init__(self, sd):
        super().__init__('noncanonical tail ' + sd)
        self.sd = sd

# ------------------------------------------------------------- aexps ----


def aeq(e1, e2):
    return C.ale(e1, e2) and C.ale(e2, e1)


def acoefs(e):
    return [(k, a) for k, a in e[1] if a]


def aadd_int(e, d):
    """e + d for an integer d; None if the constant would go negative"""
    c = e[0] + d
    if c < 0:
        return None
    return (c, e[1])


def rel_ok(rel, p, e):
    """the relation as an identity of aexps p (pred) and e (item)"""
    up, a, d = rel
    if up:
        # e = a p + d
        lhs = C.ascale(a, p)
        return aeq(C.aaddc(lhs, max(d, 0)), C.aaddc(e, max(-d, 0)))
    if a == 0:
        return (not acoefs(p)) and p[0] == d and (not acoefs(e)) and e[0] == 0
    rhs = C.ascale(a, e)
    return aeq(C.aaddc(p, max(-d, 0)), C.aaddc(rhs, max(d, 0)))


def rel_num(rel, p, e):
    up, a, d = rel
    if up:
        return e == a * p + d
    if a == 0:
        return p == d and e == 0
    return p == a * e + d


def rel_bound(rel, md):
    """the least pred of an item that satisfies rel with an exponent >= md"""
    up, a, d = rel
    INF = float('inf')
    if md == INF:
        return INF
    if up:
        if a == 0:
            return 0 if d >= md else INF
        need = md - d
        return max(0, -(-need // a))
    if a == 0:
        return d if md == 0 else INF
    return max(0, a * md + d)


def rel_apply(rel, p):
    """the item exponent from the pred aexp p: an aexp, 'void' (no item can
    satisfy it), or ('mod', k, a) / ('ge', k, n) (the region must be refined)"""
    up, a, d = rel
    cs = acoefs(p)
    if up:
        e = (a * p[0] + d, tuple((k, a * m) for k, m in cs) if a else ())
        if e[0] < 0:
            if not e[1]:
                return 'void'
            k, m = e[1][0]
            return ('ge', k, -(e[0]) // m + (1 if (-(e[0])) % m else 0))
        return e
    if a == 0:
        if not cs:
            return (0, ()) if p[0] == d else 'void'
        k, m = cs[0]
        if d < p[0]:
            return 'void'
        if len(cs) > 1:
            return ('ge', k, (d - p[0]) // m + 1)
        if (d - p[0]) % m:
            return 'void'
        return ('ge', k, (d - p[0]) // m + 1)
    for k, m in cs:
        if m % a:
            return ('mod', k, a)
    c = p[0] - d
    if c % a:
        return 'void'
    if c < 0:
        if not cs:
            return 'void'
        k, m = cs[0]
        need = -c
        return ('ge', k, need // m + (1 if need % m else 0))
    return (c // a, tuple((k, m // a) for k, m in cs))


RATIO = [2]


def infer_rel(p, e):
    """a relation making (p, e) an identity, or None"""
    cp, ce = acoefs(p), acoefs(e)
    if not cp and not ce:
        # both constant: the list ratio (so the relation generalises)
        a = RATIO[0]
        if p[0] >= e[0]:
            return (False, a, p[0] - a * e[0])
        return (True, a, e[0] - a * p[0])
    if not ce:
        return (True, 0, e[0])
    if not cp:
        return None
    dp, de = dict(cp), dict(ce)
    if set(dp) != set(de):
        return None
    ks = sorted(dp)
    k0 = ks[0]
    if de[k0] % dp[k0] == 0:
        a = de[k0] // dp[k0]
        if all(de[k] == a * dp[k] for k in ks):
            return (True, a, e[0] - a * p[0])
    if dp[k0] % de[k0] == 0:
        a = dp[k0] // de[k0]
        if all(dp[k] == a * de[k] for k in ks):
            return (False, a, p[0] - a * e[0])
    return None


# --------------------------------------------------------- automaton ----

def shift_rel(rel, dl):
    """the relation to pred p of an item whose true pred is p + dl"""
    up, a, d = rel
    if up:
        return (True, a, d + a * dl) if a else rel
    return (False, a, d - dl)


class NFA:
    """item kinds and transitions, learned during the exploration.  A state is
    ('S', unit of the item read last, offset): the tail after it is valid
    from ('S', unit, 0) with the pred shifted by the offset (the explicit
    shifted copies of the transitions are generated here)"""

    def __init__(self):
        self.kinds = []         # (side, pre, u)
        self.kidx = {}
        self.trans = []         # (side, src, kind, dst, rel)
        self.tidx = {}
        self.acc = set()        # (side, state)
        self.version = 0
        self.touched = set()    # (side, state) whose out-set changed
        self.shifts = collections.defaultdict(set)   # (side, unit) -> offsets

    def kind(self, side, pre, u):
        key = (side, tuple(pre), tuple(u))
        if key not in self.kidx:
            self.kidx[key] = len(self.kinds)
            self.kinds.append(key)
        return self.kidx[key]

    def _add(self, key):
        if key not in self.tidx:
            if len(self.trans) >= MAXNFA:
                raise Fail('automaton too large')
            self.tidx[key] = len(self.trans)
            self.trans.append(key)
            self.version += 1
            self.touched.add((key[0], key[1]))
        return self.tidx[key]

    def learn(self, side, src, k, rel, dst=None):
        if dst is None:
            dst = ('S', self.kinds[k][2], 0)
        ti = self._add((side, src, k, dst, rel))
        if src[2] == 0:
            for dl in list(self.shifts[(side, src[1])]):
                self._add((side, ('S', src[1], dl), k, dst, shift_rel(rel, dl)))
        return ti

    def ensure_shift(self, side, u, dl):
        st = ('S', tuple(u), dl)
        if dl == 0 or dl in self.shifts[(side, tuple(u))]:
            return st
        self.shifts[(side, tuple(u))].add(dl)
        base = ('S', tuple(u), 0)
        for t in list(self.trans):
            if t[0] == side and t[1] == base:
                self._add((side, st, t[2], t[3], shift_rel(t[4], dl)))
        if (side, base) in self.acc:
            self.accept(side, st)
        return st

    def accept(self, side, s):
        for s2 in [s] + ([('S', s[1], dl) for dl in self.shifts[(side, s[1])]] if s[2] == 0 else []):
            if (side, s2) not in self.acc:
                self.acc.add((side, s2))
                self.version += 1
                self.touched.add((side, s2))

    def mins(self):
        """per (side, state): the least ref a valid tail allows (a fixpoint;
        the checker verifies it as a lower bound)"""
        INF = float('inf')
        states = set(self.acc) | set((t[0], t[1]) for t in self.trans) | \
            set((t[0], t[3]) for t in self.trans)
        m = {st: (0 if st in self.acc else INF) for st in states}
        for _ in range(len(states) * 64 + 64):
            ch = False
            for (sd, src, k, dst, rel) in self.trans:
                b = rel_bound(rel, m[(sd, dst)])
                if b < m[(sd, src)]:
                    m[(sd, src)] = b
                    ch = True
            if not ch:
                break
        return m

    def out(self, side, s):
        return [i for i, t in enumerate(self.trans) if t[0] == side and t[1] == s]


def state_of_unit(u):
    return ('S', tuple(u), 0)


# ---------------------------------------------------- learned tail DFA ----
#
# BLC's automaton has one state per unit, so it accepts ANY sequence of the
# learned digits.  The lists are counters, and their digit strings are not
# free: on 0RB1RB_1LC1RA_1RA0LD_1LC1LD the (centred) digits of the halving
# list are {-1, 0, 1} whose nonzero ones ALTERNATE in sign, read from the
# head.  An automaton that forgets that lets the exploration apply a carry to
# a list the machine never builds, and the digits drift without bound.  So
# the tail language is learned as a DFA from the data pass's concrete tails:
# a tail is read from its FAR end, a fold prepends one item (the next state
# is delta(state, item), deterministic), and an unfold enumerates the
# predecessors.  States: the prefixes of the sample, merged by their futures
# up to depth K (k-tails), then refined until the quotient is deterministic.

DFA_K = ('bps',)
DFA_MAXST = 60
DFA_ALPHA = (0.05, 0.3, 0.01)


BPS_MINFREQ = 0.03      # a digit rarer than this (of its type) is transient
BPS_MAXRANGE = 6
BPS_ABS = os.environ.get('LG_BPS_ABS', '0') == '1'
BPS_TRANSFER = os.environ.get('LG_BPS_TRANSFER', '1') == '1'


def _bps_isdig(x):
    return x[1][1] >= 1


def _bps_strs(samples, freq):
    """the strings as (non-digit prefix, digit part cut at the first
    transient symbol) with their counts"""
    out = []
    for w, c in samples.items():
        pre, rest = [], list(w)
        while rest and not _bps_isdig(rest[0]):
            pre.append(rest.pop(0))
        cut = []
        for x in rest:
            if not _bps_isdig(x) or (freq is not None and x not in freq):
                break
            cut.append(x)
        out.append((tuple(pre), cut, c))
    return out


def fit_bps(samples):
    """the BOUNDED-PARTIAL-SUM model of a side's tails, or None.  The digit
    symbols (a relation with a >= 1) fall into m = 1 or 2 classes that
    alternate along the list (the 2-colouring of the digits met adjacently
    with the least weight of same-class neighbours); each class has a
    centre c, and the partial sum of d - c, read from the far end, stays in
    the range the sample shows"""
    tot = collections.Counter()
    for w, c in samples.items():
        for x in w:
            if _bps_isdig(x):
                tot[x] += c
    if not tot:
        return None
    bytype = collections.defaultdict(int)
    for x, c in tot.items():
        bytype[(x[0], x[1][0], x[1][1])] += c
    freq = set(x for x, c in tot.items() if c >= BPS_MINFREQ * bytype[(x[0], x[1][0], x[1][1])])
    strs = _bps_strs(samples, freq)
    adj = collections.Counter()
    for pre, cut, c in strs:
        for a, b in zip(cut, cut[1:]):
            adj[(a, b)] += c
    fl = sorted(freq)
    col, bip = {}, False
    if len(fl) <= 14:
        wall = sum(adj.values())
        bestc = None
        for bits in range(1 << (len(fl) - 1)):
            cc = {x: (bits >> i) & 1 for i, x in enumerate(fl[1:])}
            cc[fl[0]] = 0
            bad = sum(c for (a, b), c in adj.items() if cc[a] == cc[b])
            if bestc is None or bad < bestc[0]:
                bestc = (bad, cc)
        if bestc and bestc[0] <= BPS_MINFREQ * wall:
            col, bip = bestc[1], True
    best = None
    for m in ((2, 1) if bip else (1,)):
        cls = {x: (col[x] if m == 2 else 0) for x in freq}
        ds = [sorted(set(x[1][2] for x in freq if cls[x] == k)) for k in range(m)]
        if any(not d for d in ds):
            continue
        for cs in itertools.product(*[range(d[0], d[-1] + 1) for d in ds]):
            # the spread (max - min) of each string's partial sums
            wd = collections.Counter()
            ab = collections.Counter()
            for _, cut, c in strs:
                S = lo = hi = 0
                for j, x in enumerate(cut):
                    if j and m == 2 and cls[x] == cls[cut[j - 1]]:
                        break
                    S += x[1][2] - cs[cls[x]]
                    lo, hi = min(lo, S), max(hi, S)
                    ab[S] += c
                wd[hi - lo] += c
            # the absolute range: the sums held by all but a few percent
            n2 = sum(ab.values())
            keep = [v for v in ab if ab[v] >= BPS_MINFREQ * n2] or [0]
            alo, ahi = min(min(keep), 0), max(max(keep), 0)
            n, acc, W = sum(wd.values()), 0, 0
            for w in sorted(wd):
                acc += wd[w]
                W = w
                if acc >= (1 - BPS_MINFREQ) * n:
                    break
            if W <= BPS_MAXRANGE and (best is None or (W, ahi - alo) < best[0]):
                best = ((W, ahi - alo), m, cls, cs, alo, ahi)
    if best is None:
        return None
    (W, _), m, cls, cs, alo, ahi = best
    if VERBOSE:
        print('  bps: m=%d centres %s spread %d range [%d,%d] weight %d classes %s' % (
            m, cs, W, alo, ahi, sum(tot.values()), sorted((x[1][2], k) for x, k in cls.items())),
            file=sys.stderr)
    return dict(m=m, cls=cls, cs=cs, W=W, lo=alo, hi=ahi, weight=sum(tot[x] for x in freq))


def transfer_bps(fit, kinds, kidx, sd):
    """the model of the OTHER side's tails from this one: the same list read
    the other way (item and pred swap, so up and down swap); a partial sum
    from the other end is the total minus one from this end"""
    cls = {}
    for (k, (up, a, d)), c in fit['cls'].items():
        _, pre, u = kinds[k]
        k2 = kidx.get((sd, pre, u))
        if k2 is not None:
            cls[(k2, (not up, a, d))] = c
    if not cls:
        return None
    return dict(m=fit['m'], cls=cls, cs=fit['cs'], W=fit['W'], lo=-fit['W'], hi=fit['W'],
                weight=0)


def build_bps(fit, samples):
    """(delta, q0): state 0 the far end, one state per non-digit prefix the
    sample starts with, then (class expected, sum - min, max - min) of the
    partial sums so far, the spread at most W"""
    m, cls, cs, W = fit['m'], fit['cls'], fit['cs'], fit['W']
    sid = {('start',): 0}

    def st(key):
        return sid.setdefault(key, len(sid))

    def step(k, a, b, x):
        """the state after digit x from (class k, sum - min a, spread b);
        with BPS_ABS the state is (class k, the sum a) in [lo, hi]"""
        if k >= 0 and cls[x] != k:
            return None
        v = x[1][2] - cs[cls[x]]
        S = a + v
        if BPS_ABS:
            if not fit['lo'] <= S <= fit['hi']:
                return None
            return ('sum', (cls[x] + 1) % m, S, 0)
        lo, hi = min(0, S), max(b, S)
        if hi - lo > W:
            return None
        return ('sum', (cls[x] + 1) % m, S - lo, hi - lo)
    delta = {}
    heads = {0}
    for pre, _, _ in _bps_strs(samples, None):
        q = 0
        for i, x in enumerate(pre):
            q2 = st(('pre',) + pre[:i + 1])
            delta[(q, x)] = q2
            q = q2
        heads.add(q)
    digs = sorted(cls)
    for q in sorted(heads):
        for x in digs:
            key = step(-1, 0, 0, x)
            if key is not None:
                delta[(q, x)] = st(key)
    done = set()
    while True:
        new = [key for key in sid if key[0] == 'sum' and key not in done]
        if not new:
            break
        for key in new:
            done.add(key)
            _, k, a, b = key
            for x in digs:
                k2 = step(k, a, b, x)
                if k2 is not None:
                    delta[(sid[key], x)] = st(k2)
        if len(sid) > DFA_MAXST:
            return None
    return delta, 0


def learn_bps(samples):
    fit = fit_bps(samples)
    return None if fit is None else build_bps(fit, samples)


def alergia(samples, alpha):
    """(delta, q0) by ALERGIA (Carrasco-Oncina): the prefix tree of the
    sample with its counts, red/blue state merging, two states compatible
    when every frequency (ending, and each symbol, recursively) agrees
    within the Hoeffding bound at [alpha].  None past DFA_MAXST states"""
    child, cnt, fin = [{}], [0], [0]
    for w, c in samples.items():
        nd = 0
        cnt[0] += c
        for x in w:
            nxt = child[nd].get(x)
            if nxt is None:
                nxt = len(child)
                child.append({})
                cnt.append(0)
                fin.append(0)
                child[nd][x] = nxt
            nd = nxt
            cnt[nd] += c
        fin[nd] += c
    lg = math.sqrt(0.5 * math.log(2 / alpha))

    def differ(f1, n1, f2, n2):
        if n1 == 0 or n2 == 0:
            return False
        return abs(f1 / n1 - f2 / n2) > lg * (1 / math.sqrt(n1) + 1 / math.sqrt(n2))

    def compat(a, b, depth=0):
        if depth > 64:
            return True
        if differ(fin[a], cnt[a], fin[b], cnt[b]):
            return False
        for x in set(child[a]) | set(child[b]):
            ca, cb = child[a].get(x), child[b].get(x)
            fa = cnt[ca] if ca is not None else 0
            fb = cnt[cb] if cb is not None else 0
            if differ(fa, cnt[a], fb, cnt[b]):
                return False
            if ca is not None and cb is not None and not compat(ca, cb, depth + 1):
                return False
        return True

    def fold(a, b):
        """merge the subtree at b into a's"""
        cnt[a] += cnt[b]
        fin[a] += fin[b]
        for x, cb in list(child[b].items()):
            ca = child[a].get(x)
            if ca is None:
                child[a][x] = cb
            else:
                fold(ca, cb)

    red = [0]
    reds = {0}
    while True:
        # the blue fringe: children of red states that are not red; the
        # oldest (smallest prefix-tree id, so shortest prefix) first
        blue = [(c, r, x) for r in red for x, c in child[r].items() if c not in reds]
        if not blue:
            break
        b, p, sym = min(blue)
        for r in red:
            if compat(r, b):
                child[p][sym] = r
                fold(r, b)
                break
        else:
            red.append(b)
            reds.add(b)
            if len(red) > DFA_MAXST:
                return None
    rid = {r: i for i, r in enumerate(red)}
    delta = {}
    for r in red:
        for x, c in child[r].items():
            if c not in rid:
                return None
            delta[(rid[r], x)] = rid[c]
    return delta, 0


def learn_dfa(strings, k):
    """(delta, q0) of a DFA over symbols accepting every string of the
    (prefix-closed) sample, or None when it has more than DFA_MAXST states"""
    children = [{}]
    for w in strings:
        nd = 0
        for x in w:
            nxt = children[nd].get(x)
            if nxt is None:
                nxt = len(children)
                children.append({})
                children[nd][x] = nxt
            nd = nxt
    n = len(children)
    # futures up to depth k, bottom-up by depth
    order, depth = [0], [0] * n
    for nd in order:
        for x, c in children[nd].items():
            depth[c] = depth[nd] + 1
            order.append(c)
    fut = [None] * n
    for nd in reversed(order):
        acc = {()}
        for x, c in children[nd].items():
            for p in fut[c]:
                if len(p) < k:
                    acc.add((x,) + p)
        fut[nd] = frozenset(acc)
    ids = {}
    cls = [ids.setdefault(fut[nd], len(ids)) for nd in range(n)]
    # refine until every class maps each symbol into one class
    while True:
        # split a class into groups whose children agree where both exist
        byc = collections.defaultdict(list)
        for nd in range(n):
            byc[cls[nd]].append(nd)
        final = [None] * n
        nid = 0
        for c, mem in byc.items():
            groups = []             # (symbol -> class) maps
            for nd in mem:
                m = {x: cls[ch] for x, ch in children[nd].items()}
                for g in groups:
                    if all(g[0].get(x, y) == y for x, y in m.items()):
                        g[0].update(m)
                        g[1].append(nd)
                        break
                else:
                    groups.append((dict(m), [nd]))
            for g in groups:
                for nd in g[1]:
                    final[nd] = nid
                nid += 1
        if nid == len(set(cls)):
            break
        cls = final
    delta = {}
    for nd in range(n):
        for x, c in children[nd].items():
            key = (cls[nd], x)
            if delta.get(key, cls[c]) != cls[c]:
                return None
            delta[key] = cls[c]
    if len(set(cls)) > DFA_MAXST:
        return None
    return delta, cls[0]


def item_segs(nfa, k, e):
    side, pre, u = nfa.kinds[k]
    return [('L', tuple(pre)), ('B', tuple(u), e)]


# ---------------------------------------------------------------- leaf ----

def leaf_run(tabw, q, h, Lz, Rz, endL, endR, na, p):
    """ti_batch.leaf_run on explicit (substituted) window sides; reaching the
    end of a side whose tail is not known empty asks for an unfold"""
    tr = tabw.get((q, h))
    if tr is None:
        raise Fail('pinned at a family start')
    D = 'R' if tr[1] > 0 else 'L'
    Dz, Oz = (Rz, Lz) if D == 'R' else (Lz, Rz)
    dpre, i = T.cprefix(Dz, 0)
    idx = None
    if not dpre and i < len(Dz) and Dz[i][0] == 'B':
        u, e = tuple(Dz[i][1]), Dz[i][2]
        if len(e[1]) != 1:
            raise Fail('multi-variable block')
        (k, a), c = e[1][0], e[0]
        if c < na:
            raise Req('ge', k, na - c)
        if p > 1 and a % p:
            raise Req('mod', k, p)
        b, r = divmod(c - na, p)
        post, i2 = T.cprefix(Dz, i + 1)
        dss = (C.rep(u, na), C.rep(u, p), a // p, b, C.rep(u, r) + post)
        nD = i2
        idx = (k, D, u)
    else:
        dss = (dpre, (), 0, 0, ())
        nD = i
    opre, nO = T.cprefix(Oz, 0)
    oss = (opre, (), 0, 0, ())
    if D == 'R':
        c0 = (q, oss, h, dss)
        nL, nR = nO, nD
    else:
        c0 = (q, dss, h, oss)
        nL, nR = nD, nO
    el, er = nL >= len(Lz) and endL, nR >= len(Rz) and endR
    j = idx[0] if idx else 0
    chain = []
    c = c0
    crossed = False
    nsteps = 0

    def emit(st):
        nonlocal c
        try:
            r = LC.sstep(tabw, el, er, st, c)
        except LC.Halt:
            r = None
        if r is None:
            raise Fail('sstep refused %r' % (st,))
        chain.append(st)
        c = r[0]

    lastd = None
    while True:
        if nsteps > MAXSTEPS:
            raise Fail('leaf too long')
        q1, L1, h1, R1 = c
        tr = tabw.get((q1, h1))
        if tr is None:
            raise Fail('pinned inside a leaf')
        if nsteps >= CUTSTEPS and lastd is not None and tr[1] != lastd and (crossed or idx is None):
            break                       # a long walk in literal cells: cut at a turn
        lastd = tr[1]
        if idx is not None and not crossed:
            bs = R1 if idx[1] == 'R' else L1
            if not bs[0] and bs[1]:
                if idx[1] == 'R':
                    n = T.cyc_R(tabw, q1, h1, bs[1])
                    if n is not None:
                        emit(('SCycR', n))
                        crossed = True
                        nsteps += 1
                        continue
                else:
                    r = T.cyc_L(tabw, q1, h1, bs[1], R1[0])
                    if r is not None:
                        emit(('SCycL', r[0], r[1]))
                        crossed = True
                        nsteps += 1
                        continue
        d = tr[1]
        side = R1 if d > 0 else L1
        if side[0]:
            emit(('SWin', 1))
            nsteps += 1
            continue
        if side[1]:
            if idx is not None and not crossed and ((d > 0) == (idx[1] == 'R')):
                u = idx[2]
                if p == 1:
                    for p2 in (2, 3, 4):
                        U2 = u * p2
                        ok = (T.cyc_R(tabw, q1, h1, U2) is not None) if d > 0 \
                            else T.cyc_L(tabw, q1, h1, U2, R1[0]) is not None
                        if ok:
                            raise Req('pow', idx[0], p2)
                if nsteps > 0:
                    break
                if na >= MAXNA:
                    raise Fail('no cycle through the start block')
                raise Req('na', idx[0], na + 1)
            break
        X = (Rz[nR:] if d > 0 else Lz[nL:])
        if X:
            break
        if not (endR if d > 0 else endL):
            if nsteps > 0:
                break
            raise Req('unf', 'R' if d > 0 else 'L', 0)
        emit(('SWinR', 1) if d > 0 else ('SWinL', 1))
        nsteps += 1
    if nsteps == 0:
        raise Fail('empty leaf')
    chain = T.merge_chain(chain)
    r = LC.srun(tabw, el, er, chain, c0)
    if r is None:
        raise Fail('chain does not replay')
    c1, ca, cb = r
    if cb == 0:
        if idx is None:
            raise Fail('zero-step leaf')
        raise Req('ge', idx[0], 1 + (0 if dss[3] or dss[0] else 0))
    endLs = C.ss_segs(c1[1], j) + Lz[nL:]
    endRs = C.ss_segs(c1[3], j) + Rz[nR:]
    return dict(c0=c0, el=el, er=er, chain=chain, j=j, nL=nL, nR=nR, c1=c1,
                q1=c1[0], h1=c1[2], endL=endLs, endR=endRs)


# ------------------------------------------------------------ families ----

SMALL = 7           # a boot block this short is read as literal
MINCOPY = 3         # ... and a block of a longer unit needs this many copies
LUMIN = 3           # copies that make a run of a side's list unit an item
GENZ = 3            # a run of zeros this long is a block (away from the tape end)


def gen_lit(w, strip_end, small=SMALL, units=()):
    """a literal word (nearest-first) as segments: runs of >= 2 copies of a
    unit of 1..4 cells (zeros: >= GENZ, not at the end of the word when
    [strip_end]) longer than [small] cells become constant blocks"""
    w = tuple(w)
    if strip_end:
        while w and w[-1] == 0:
            w = w[:-1]
    out, lit, i = [], [], 0
    while i < len(w):
        best = None
        for u in T.GEN_UNITS + [(0,)]:
            k = len(u)
            n = 0
            while w[i + k * n:i + k * (n + 1)] == u:
                n += 1
            lu = u in units
            if (lu and n >= LUMIN) or (n >= max(2, MINCOPY if k > 1 else 2) and k * n > small):
                if best is not None and k * n <= len(best[0]) * best[1]:
                    continue
                if u == (0,) and ((n < GENZ and not lu) or (strip_end and i + n >= len(w))):
                    continue
                best = (u, n, lu)
        if best:
            if lit:
                out.append(('L', tuple(lit)))
                lit = []
            # a short run of the side's list unit is an item of a known
            # length (constant), a long run is a block born from a literal
            out.append(('B', best[0], (best[1], ()), not (best[2] and best[1] * len(best[0]) <= small)))
            i += len(best[0]) * best[1]
        else:
            lit.append(w[i])
            i += 1
    if lit:
        out.append(('L', tuple(lit)))
    return out


def fpush(acc, x):
    """ti_coq.push, except that a constant block longer than SMALL cells
    stays a block (a length a relation fixed is not a growing literal)"""
    if x[0] == 'L':
        return C.push_lit(acc, tuple(x[1]))
    v, p = C.primroot(x[1])
    e2 = C.ascale(p, x[2])
    if not v:
        return acc
    if not e2[1] and e2[0] == 0:
        return acc
    return C.push_blk(acc, v, e2)


def fnorm(l):
    acc = []
    for x in l:
        acc = fpush(acc, x)
    return list(reversed(acc))


def gen_side(syms, small=SMALL):
    return gen_lit(syms, True, small)


def gen_segs(side, ended, units=()):
    """the literal segments of a normalized side, generalized (a trailing
    zero run of an ended side is blank)"""
    out = []
    for i, x in enumerate(side):
        if x[0] != 'L':
            out.append(x)
            continue
        out.extend(gen_lit(x[1], ended and i == len(side) - 1, SMALL, units))
    return out


def blocks_of(side):
    return [i for i, s in enumerate(side) if s[0] == 'B']


from fractions import Fraction                      # noqa: E402
import itertools                                    # noqa: E402


class Hull:
    """an affine subspace of Q^n: the affine hull of every value vector
    joined into it (Karr's affine-equality domain), and per coordinate the
    least value of a joined base point"""

    def __init__(self, n):
        self.n = n
        self.base = None
        self.rows = []            # echelon basis: (pivot, vector of Fractions)
        self.mins = [None] * n

    def _add_dir(self, v):
        v = [Fraction(x) for x in v]
        for piv, r in self.rows:
            if v[piv]:
                f = v[piv] / r[piv]
                v = [a - f * b for a, b in zip(v, r)]
        for i, x in enumerate(v):
            if x:
                self.rows.append((i, v))
                return True
        return False

    def add(self, e0, ks):
        ch = False
        for i, x in enumerate(e0):
            if self.mins[i] is None or x < self.mins[i]:
                self.mins[i] = x
                ch = True
        if self.base is None:
            self.base = list(e0)
            ch = True
        elif self._add_dir([a - b for a, b in zip(e0, self.base)]):
            ch = True
        for k in ks:
            if self._add_dir(k):
                ch = True
        return ch

    def dim(self):
        return len(self.rows)

    def param(self, isref=()):
        """(B, lam, cst, lb): coordinates B cover the hull (every other
        coordinate j is cst_j + sum lam[j][i] (lb_i + x_i) on it, lam
        nonnegative integers, cst_j >= 0), lb_i the least joined value of B_i"""
        d = self.dim()
        D = [r for _, r in self.rows]
        n = self.n
        vary = [j for j in range(n) if any(r[j] for r in D)]
        for size in range(d, len(vary) + 1):
            for B in itertools.combinations(vary, size):
                lb = [int(self.mins[i]) for i in B]
                lam, cst = {}, {}
                ok = True
                for j in range(n):
                    if j in B:
                        continue
                    got = None
                    for l in _solve(D, list(B), j, size == d, j in isref):
                        c = self.base[j] - sum(a * self.base[i] for a, i in zip(l, B)) \
                            + sum(a * m for a, m in zip(l, lb))
                        if c >= 0 and Fraction(c).denominator == 1:
                            got = (l, int(c))
                            break
                    if got is None:
                        ok = False
                        break
                    lam[j], cst[j] = got
                if ok:
                    return list(B), lam, cst, lb
        return None


LAMMAX = 4


def _solve(D, B, j, exact, pref):
    """lam >= 0 integers with D[k][j] = sum_i lam_i D[k][B_i] for every row k"""
    """(candidates, in order of preference)"""
    d = len(D)
    if exact and len(B) == d:
        M = [[D[k][i] for i in B] for k in range(d)]
        inv = _inv(M)
        if inv is None:
            return []
        col = [D[k][j] for k in range(d)]
        l = [sum(col[k] * inv[i][k] for k in range(d)) for i in range(len(B))]
        if any(x < 0 or x.denominator != 1 for x in l):
            return []
        return [[int(x) for x in l]]
    out = []
    for l in itertools.product(range(LAMMAX + 1), repeat=len(B)):
        if all(D[k][j] == sum(a * D[k][i] for a, i in zip(l, B)) for k in range(d)):
            key = (0 if (pref and any(l)) or (not pref and not any(l)) else 1, sum(l), l)
            out.append((key, list(l)))
    out.sort()
    return [l for _, l in out]


def _inv(M):
    d = len(M)
    A = [list(r) + [Fraction(int(i == j)) for j in range(d)] for i, r in enumerate(M)]
    for c in range(d):
        p = next((r for r in range(c, d) if A[r][c]), None)
        if p is None:
            return None
        A[c], A[p] = A[p], A[c]
        f = A[c][c]
        A[c] = [x / f for x in A[c]]
        for r in range(d):
            if r != c and A[r][c]:
                g = A[r][c]
                A[r] = [x - g * y for x, y in zip(A[r], A[c])]
    return [r[d:] for r in A]


class Fam:
    """one family per SHAPE (state, head, window shapes, tail states): the
    coordinates are the window blocks' exponents (left then right) and the
    refs (left, right: the sides with a tail); their values range over an
    affine hull, parametrized by a basis of coordinates"""

    def __init__(self, key):
        self.key = key
        self.q, self.h, self.sL, self.sR, self.tL, self.tR, self.wrel = key
        self.nb = sum(1 for x in self.sL + self.sR if x[0] == 'B')
        self.nc = self.nb + (self.tL is not None) + (self.tR is not None)
        self.hull = Hull(self.nc)
        self.version = 0
        self.fix()

    def fix(self):
        """the parametrization of the current hull"""
        H = self.hull
        if H.base is None:
            self.B, self.lam, self.cst, self.lb = [], {}, {}, []
            self.ex = ()
            self.n = 0
            return
        pr = H.param(isref=tuple(range(self.nb, self.nc)))
        if pr is None:
            raise Fail('no nonnegative parametrization')
        self._set(*pr)

    def _set(self, B, lam, cst, lb):
        self.B, self.lam, self.cst, self.lb = B, lam, cst, lb
        ex = []
        for j in range(self.nc):
            if j in B:
                k = B.index(j)
                ex.append((lb[k], ((k, 1),)))
            else:
                ex.append((cst[j], tuple((k, a) for k, a in enumerate(lam[j]) if a)))
        self.ex = tuple(ex)
        self.n = len(B)

    def match(self, exps):
        """tgt (aexps in z) with pattern(tgt) = exps, or None"""
        if self.hull.base is None:
            return None
        tgt = []
        for k, i in enumerate(self.B):
            e = exps[i]
            if e[0] < self.lb[k]:
                return None
            tgt.append((e[0] - self.lb[k], e[1]))
        for j in range(self.nc):
            if j in self.B:
                continue
            want = C.asubst(tgt, self.ex[j])
            if not aeq(want, exps[j]):
                return None
        return tgt

    def join(self, exps):
        """widen the hull by the affine set of exps; True if it changed"""
        e0 = [e[0] for e in exps]
        ks = sorted(set(k for e in exps for k, _ in e[1]))
        dirs = [[dict(e[1]).get(k, 0) for e in exps] for k in ks]
        if self.hull.add(e0, dirs):
            old = self.ex
            self.fix()
            if self.ex != old or True:
                self.version += 1
                return True
        return False

    def tstate(self, sd):
        return self.tL if sd == 'L' else self.tR

    def pattern(self):
        k = 0
        out = []
        for sh in (self.sL, self.sR):
            side = []
            for x in sh:
                if x[0] == 'L':
                    side.append(x)
                else:
                    side.append(('B', x[1], self.ex[k]))
                    k += 1
            out.append(side)
        return out

    def ref(self, sd):
        if self.tstate(sd) is None:
            return None
        i = self.nb
        if sd == 'R' and self.tL is not None:
            i += 1
        return self.ex[i]


class Explorer:
    def __init__(self, tab, pins):
        self.tab = tab
        self.tabw = {k: (None if k in pins else v) for k, v in tab.items()}
        self.nfa = NFA()
        self.fams = []
        self.fidx = {}
        self.trees = {}
        self.utrees = {}
        self.fleaves = {}
        self.failed = {}
        self.uses = collections.defaultdict(set)
        self.booting = False
        self.dfa = None
        self.dfa_in = {}
        self.samples = {'L': collections.Counter(), 'R': collections.Counter()}

    # -- folding --------------------------------------------------------
    def fold_dfa(self, sd, W, tail):
        """fold with the learned DFA: an item folds only when the DFA has a
        transition for it from the tail's state (and canonically: the tail's
        ref is the item's exponent); nothing is learned"""
        nfa = self.nfa
        delta, q0 = self.dfa[sd]
        W = list(W)
        folds = []
        cur = tail
        while len(blocks_of(W)) > KEEP:
            last = W[-1]
            if last[0] == 'L':
                if cur is not None:
                    break
                pred = W[blocks_of(W)[-1]]
                k = nfa.kidx.get((sd, tuple(last[1]), ()))
                f, nrm, q = (0, ()), 1, q0
            else:
                u, f = tuple(last[1]), last[2]
                if len(W) >= 2 and W[-2][0] == 'L':
                    pre, nrm = tuple(W[-2][1]), 2
                else:
                    pre, nrm = (), 1
                if len(W) - nrm - 1 < 0 or W[len(W) - nrm - 1][0] != 'B':
                    break
                pred = W[len(W) - nrm - 1]
                k = nfa.kidx.get((sd, pre, u))
                if cur is None:
                    q = q0
                else:
                    s_old, r_old = cur
                    if not aeq(f, r_old):
                        break
                    q = s_old[3]
            if k is None:
                break
            ti = None
            for t in self.dfa_in.get((sd, q), ()):
                tr = nfa.trans[t]
                if tr[2] == k and rel_ok(tr[4], pred[2], f):
                    ti = t
                    break
            if ti is None:
                break
            folds.insert(0, (ti, f))
            cur = (nfa.trans[ti][1], pred[2])
            W = W[:len(W) - nrm]
        return W, cur, folds

    def use_dfa(self, dfas):
        """replace the automaton by the learned DFAs (side -> (delta, q0))"""
        old = self.nfa
        n = NFA()
        n.kinds, n.kidx = old.kinds, old.kidx
        self.dfa_in = collections.defaultdict(list)
        for sd, (delta, q0) in sorted(dfas.items()):
            # a pinned end (a = 0 down) before a free one: the more precise
            for (q, sym), q2 in sorted(delta.items(), key=lambda kv: (kv[0][0], kv[0][1][0],
                                                                   kv[0][1][1][0], kv[0][1][1])):
                k, rel = sym
                key = (sd, ('D', None, 0, q2), k, ('D', None, 0, q), rel)
                n.tidx[key] = len(n.trans)
                self.dfa_in[(sd, q)].append(len(n.trans))
                n.trans.append(key)
            n.acc.add((sd, ('D', None, 0, q0)))
        self.nfa = n
        self.dfa = dfas
        self.fams, self.fidx = [], {}
        self.trees, self.utrees, self.fleaves = {}, {}, {}
        self.failed = {}
        self.uses = collections.defaultdict(set)

    def fold(self, sd, W, tail):
        """fold the outermost window items into the tail; learns the
        automaton.  Returns (window, tail spec (state, ref aexp) or None, folds)
        where folds are the (transition, exponent) pairs, nearest-first"""
        if self.dfa is not None:
            return self.fold_dfa(sd, W, tail)
        nfa = self.nfa
        W = list(W)
        folds = []
        cur = tail
        if cur is not None and (sd, cur[0]) in nfa.acc and not nfa.out(sd, cur[0]):
            cur = None              # an accepting state with no way on: the tail is empty
        while len(blocks_of(W)) > KEEP:
            last = W[-1]
            if last[0] == 'L':
                if cur is not None:
                    break
                bi = blocks_of(W)[-1]
                pred = W[bi]
                k = nfa.kind(sd, last[1], ())
                src = state_of_unit(pred[1])
                free = (sd, src, k, state_of_unit(()), (True, 0, 0)) in nfa.tidx
                pinned = [t for t in nfa.trans if t[0] == sd and t[1] == src and t[2] == k
                          and t[4][:2] == (False, 0)]
                if acoefs(pred[2]) or free:
                    rel = (True, 0, 0)
                else:
                    rel = (False, 0, pred[2][0])
                    if (sd, src, k, state_of_unit(()), rel) not in nfa.tidx:
                        if not self.booting:
                            break
                        if pinned:
                            # a second pinned length: the list may end anywhere
                            rel = (True, 0, 0)
                ti = nfa.learn(sd, src, k, rel)
                nfa.accept(sd, state_of_unit(()))
                folds.insert(0, (ti, (0, ())))
                cur = (src, pred[2])
                W = W[:-1]
                continue
            u, f = tuple(last[1]), last[2]
            if len(W) >= 2 and W[-2][0] == 'L':
                pre, nrm = tuple(W[-2][1]), 2
            else:
                pre, nrm = (), 1
            if len(W) - nrm - 1 < 0 or W[len(W) - nrm - 1][0] != 'B':
                break
            pred = W[len(W) - nrm - 1]
            k = nfa.kind(sd, pre, u)
            dst = None
            if cur is not None:
                s_old, r_old = cur
                if CANON:
                    # fold only a CANONICAL item: the tail after it is valid
                    # from its own exponent (the leaf left it unchanged); a
                    # modified one stays in the window, and the leaf unfolds
                    # its neighbour instead (NonCanon)
                    if s_old[2] != 0 or not aeq(f, r_old):
                        break
                else:
                    if dict(acoefs(f)) != dict(acoefs(r_old)):
                        break
                    dl = s_old[2] + r_old[0] - f[0]
                    if abs(dl) > MAXSHIFT:
                        break
                    dst = nfa.ensure_shift(sd, s_old[1], dl)
            src = state_of_unit(pred[1])
            rel = None
            for t in nfa.trans:
                if t[0] == sd and t[1] == src and t[2] == k and rel_ok(t[4], pred[2], f):
                    rel = t[4]
                    break
            if rel is None:
                rel = infer_rel(pred[2], f)
                if rel is None or not rel_ok(rel, pred[2], f):
                    break
                if not acoefs(pred[2]) and not acoefs(f) and (abs(rel[2]) > MAXD
                                                               or not self.booting):
                    break
            ti = nfa.learn(sd, src, k, rel, dst)
            if cur is None:
                nfa.accept(sd, state_of_unit(u))
            folds.insert(0, (ti, f))
            cur = (src, pred[2])
            W = W[:len(W) - nrm]
        return W, cur, folds

    def fam_of(self, q, h, L, R, tails, boot=False):
        """(fid, exps, changed?, folds) for a normalized end configuration;
        the family's hull is widened by exps.  tails: side -> None |
        (state, ref aexp)"""
        W, specs, folds = {}, {}, {}
        for sd, side in (('L', L), ('R', R)):
            units = set(k[2] for k in self.nfa.kinds if k[0] == sd and k[2])
            if not boot:
                # constant blocks back to literal (re-blocked by the side's
                # list units below): a separator stays a separator
                side = C.norm([x if x[0] == 'L' or acoefs(x[2]) else
                               ('L', C.rep(x[1], x[2][0])) for x in side])
            side = gen_segs(side, tails[sd] is None, units)
            W[sd], specs[sd], folds[sd] = self.fold(sd, side, tails[sd])
        if CANON and not boot:
            for sd, od in (('L', 'R'), ('R', 'L')):
                if specs[sd] is None:
                    continue
                # the pred of the tail's first item, in tape order: the
                # side's outermost window block, else the other side's
                # nearest one
                s_, r_ = specs[sd]
                bs, bo = blocks_of(W[sd]), blocks_of(W[od])
                pb = W[sd][bs[-1]] if bs else (W[od][bo[0]] if bo else None)
                if pb is None or s_[2] != 0 or (s_[0] == 'S' and tuple(pb[1]) != tuple(s_[1])) \
                        or not aeq(pb[2], r_):
                    raise NonCanon(sd)
        exps = T.exps(W['L']) + T.exps(W['R'])
        for sd in ('L', 'R'):
            if specs[sd] is not None:
                exps.append(specs[sd][1])
        # the relation between adjacent window blocks of a side's list unit
        # (a digit) is part of the family: joining two digits would lose it
        # (in tape order, across the head)
        wrel = []
        units = set(k[2] for k in self.nfa.kinds if k[2])
        bl = [x for x in reversed(W['L']) if x[0] == 'B'] + [x for x in W['R'] if x[0] == 'B']
        for x, y in zip(bl, bl[1:]):
            if tuple(x[1]) in units and tuple(y[1]) in units:
                wrel.append(infer_rel(x[2], y[2]))
            else:
                wrel.append(None)
        key = (q, h, T.shape(W['L']), T.shape(W['R']),
               None if specs['L'] is None else specs['L'][0],
               None if specs['R'] is None else specs['R'][0], tuple(wrel))
        if key not in self.fidx:
            if len(self.fams) >= MAXFAM:
                raise Fail('too many families')
            self.fidx[key] = len(self.fams)
            self.fams.append(Fam(key))
        fid = self.fidx[key]
        F = self.fams[fid]
        ch = False
        if F.match(exps) is None:
            ch = F.join(exps)
            if F.match(exps) is None:
                raise Fail('join does not cover its target')
        return fid, exps, ch, folds

    # -- exploration ------------------------------------------------------
    def data_pass(self, boot, nleaves):
        """follow the REAL run leaf by leaf from the boot (the same cuts, folds
        and unfolds as the exploration, the tails concrete), joining every
        value vector into its family's hull"""
        q, L, h, R, tails, conc = boot
        self.booting = True
        f0, ex0, _, folds0 = self.fam_of(q, h, L, R, tails, boot=True)
        self.booting = False
        nfa = self.nfa
        fid, vals = f0, [e[0] for e in ex0]
        # the boot's family may fold more than the boot did (a DFA fold)
        ctail = {sd: [(ti, e[0]) for ti, e in folds0[sd]] + list(conc[sd]) for sd in ('L', 'R')}
        for sd in ('L', 'R'):
            self.samples[sd][tuple((nfa.trans[ti][2], nfa.trans[ti][4])
                                   for ti, _ in reversed(ctail[sd]))] += 1
        self.booting = True
        try:
            for _ in range(nleaves):
                F = self.fams[fid]
                # the window, concrete
                k = 0
                ext = {}
                for sd, sh in (('L', F.sL), ('R', F.sR)):
                    segs = []
                    for x in sh:
                        if x[0] == 'L':
                            segs.append(x)
                        else:
                            segs.append(('B', x[1], (vals[k], ())))
                            k += 1
                    ext[sd] = segs
                st, end, ref = {}, {}, {}
                ri = F.nb
                for sd in ('L', 'R'):
                    s_ = F.tstate(sd)
                    if s_ is None:
                        st[sd], end[sd] = None, True
                    else:
                        st[sd], end[sd], ref[sd] = s_, False, vals[ri]
                        ri += 1
                while True:
                    try:
                        lf = leaf_run(self.tabw, F.q, F.h, ext['L'], ext['R'], end['L'],
                                      end['R'], 0, 1)
                        break
                    except Req as rq:
                        if rq.kind != 'unf':
                            raise Fail('data pass: %s' % rq.kind)
                        sd = rq.k
                    if not ctail[sd]:
                        end[sd] = True
                        continue
                    ti, e = ctail[sd].pop(0)
                    ext[sd] = ext[sd] + item_segs(nfa, nfa.trans[ti][2], (e, ()))
                    st[sd], ref[sd] = nfa.trans[ti][3], e
                Ln = fnorm(lf['endL'])
                Rn = fnorm(lf['endR'])
                if end['L']:
                    Ln = C.nstrip(Ln)
                if end['R']:
                    Rn = C.nstrip(Rn)
                if CANON:
                    # the concrete leaves walk constant blocks cell by cell,
                    # so they are not the exploration's leaves: re-segment
                    # the whole concrete tape (window and the rest of the
                    # tail) as the boot does, which folds canonically
                    full = {}
                    for sd, sn in (('L', Ln), ('R', Rn)):
                        segs = list(sn)
                        for ti, e in ctail[sd]:
                            segs += item_segs(nfa, nfa.trans[ti][2], (e, ()))
                        full[sd] = C.nstrip(fnorm(segs))
                    fid, exps, _, folds = self.fam_of(lf['q1'], lf['h1'], full['L'], full['R'],
                                                      {'L': None, 'R': None})
                    vals = [e[0] for e in exps]
                    for sd in ('L', 'R'):
                        ctail[sd] = [(ti, e[0]) for ti, e in folds[sd]]
                        # the tail as a string read from its far end
                        self.samples[sd][tuple((nfa.trans[ti][2], nfa.trans[ti][4])
                                               for ti, _ in reversed(folds[sd]))] += 1
                    continue
                tails = {sd: (None if end[sd] else (st[sd], (ref[sd], ()))) for sd in ('L', 'R')}
                if any(end[sd] and ctail[sd] for sd in ('L', 'R')):
                    raise Fail('data pass: ended with a tail')
                fid, exps, _, folds = self.fam_of(lf['q1'], lf['h1'], Ln, Rn, tails)
                vals = [e[0] for e in exps]
                for sd in ('L', 'R'):
                    ctail[sd] = [(ti, e[0]) for ti, e in folds[sd]] + ctail[sd]
        finally:
            self.booting = False
        self.nfa.touched.clear()

    def explore(self, boot):
        q, L, h, R, tails, conc = boot
        f0, ex0, _, folds0 = self.fam_of(q, h, L, R, tails, boot=True)
        self.boot = (f0, ex0, folds0, conc)
        todo = [f0]
        rounds = 0
        while todo:
            rounds += 1
            if rounds > MAXROUNDS:
                raise Fail('exploration does not settle')
            fid = todo.pop(0)
            if fid in todo:
                continue
            if VERBOSE and rounds % 50 == 0:
                print('  round %d: %d families, %d todo, %d transitions, %d failed' % (
                    rounds, len(self.fams), len(todo), len(self.nfa.trans), len(self.failed)),
                      file=sys.stderr, flush=True)
            F = self.fams[fid]
            v0 = F.version
            try:
                self.explore_fam(fid, todo)
                self.failed.pop(fid, None)
            except Fail as e:
                self.failed[fid] = str(e)
                self.trees.pop(fid, None)
                self.fleaves.pop(fid, None)
            if F.version != v0 and fid not in todo:
                todo.append(fid)
            if self.nfa.touched:
                for st in list(self.nfa.touched):
                    for f2 in self.uses.get(st, ()):
                        self.trees.pop(f2, None)
                        self.fleaves.pop(f2, None)
                        if f2 not in todo:
                            todo.append(f2)
                self.nfa.touched.clear()
        # the families the boot reaches
        reach, stack = set(), [f0]
        while stack:
            f = stack.pop()
            if f in reach:
                continue
            reach.add(f)
            if f in self.failed:
                raise Fail('%s (family %d)' % (self.failed[f], f))
            if f not in self.fleaves:
                raise Fail('unexplored family %d' % f)
            for lf in self.fleaves[f]:
                stack.append(lf['g'])
        self.reach = reach

    def explore_fam(self, fid, todo):
        self.mins = self.nfa.mins()
        F = self.fams[fid]
        nfa = self.nfa
        nodes, unodes, leaves = [], [], []
        pat = F.pattern()
        used = set()

        class Up(Exception):
            def __init__(self, rq):
                self.rq = rq

        def run_unf(R, paths, na, p):
            """a leaf, or an unfold node, below region R.  paths: side ->
            list of (transition, exponent) or 'end' entries"""
            if len(leaves) > MAXLEAF:
                raise Fail('too many leaves')
            sub = C.rsub(R)
            ext, end, st = {}, {}, {}
            for sd, pt in (('L', pat[0]), ('R', pat[1])):
                segs = [C.seg_subst(sub, x) for x in pt]
                r = F.ref(sd)
                if r is None:
                    end[sd] = True
                    st[sd] = None
                else:
                    r = C.asubst(sub, r)
                    s = F.tstate(sd)
                    end[sd] = False
                    for ent in paths[sd]:
                        if ent == 'end':
                            end[sd] = True
                            break
                        ti, u = ent
                        segs = segs + item_segs(nfa, nfa.trans[ti][2], u)
                        s, r = nfa.trans[ti][3], u
                    st[sd] = (s, r)
                ext[sd] = segs
            mins = self.mins
            for sd in ('L', 'R'):
                if st[sd] is None or end[sd]:
                    continue
                s_, r_ = st[sd]
                used.add((sd, s_))
                mm = mins.get((sd, s_), 0)
                if mm == float('inf'):
                    raise Fail('state with no valid tail')
                if r_[0] < mm:
                    cs = acoefs(r_)
                    if not cs:
                        me = len(unodes)
                        unodes.append(('void', sd))
                        return me
                    if len(cs) == 1:
                        k, m_ = cs[0]
                        raise Up(Req('uge', k, -(-(mm - r_[0]) // m_)))
            def unfold(sd):
                if len(paths[sd]) >= MAXUNF:
                    raise Fail('unfold depth')
                s, r = st[sd]
                used.add((sd, s))
                me = len(unodes)
                unodes.append(None)
                kids = []
                endk = None
                if (sd, s) in nfa.acc:
                    p2 = dict(paths)
                    p2[sd] = paths[sd] + ['end']
                    endk = run_unf(R, p2, na, p)
                for ti in nfa.out(sd, s):
                    u = rel_apply(nfa.trans[ti][4], r)
                    if u != 'void' and not (isinstance(u[0], str)) and not acoefs(u) \
                            and u[0] < self.mins.get((sd, nfa.trans[ti][3]), 0):
                        # the item is below its state's least ref: a void node
                        vi = len(unodes)
                        unodes.append(('void', sd))
                        kids.append((ti, u, vi))
                        continue
                    if u == 'void':
                        kids.append((ti, None, None))
                        continue
                    if isinstance(u, tuple) and u and isinstance(u[0], str):
                        raise Up(Req('u' + u[0], u[1], u[2]))
                    p2 = dict(paths)
                    p2[sd] = paths[sd] + [(ti, u)]
                    kids.append((ti, u, run_unf(R, p2, na, p)))
                unodes[me] = ('unf', sd, endk, kids)
                return me

            while True:
                try:
                    lf = leaf_run(self.tabw, F.q, F.h, ext['L'], ext['R'], end['L'], end['R'],
                                  na, p)
                    break
                except Req as rq:
                    if rq.kind == 'na':
                        na = rq.n
                        continue
                    if rq.kind == 'unf':
                        return unfold(rq.k)
                    raise Up(rq)
            Ln = fnorm(lf['endL'])
            Rn = fnorm(lf['endR'])
            if end['L']:
                Ln = C.nstrip(Ln)
            if end['R']:
                Rn = C.nstrip(Rn)
            tails = {sd: (None if end[sd] else st[sd]) for sd in ('L', 'R')}
            try:
                g, ex, low, folds = self.fam_of(lf['q1'], lf['h1'], Ln, Rn, tails)
            except NonCanon as nc:
                return unfold(nc.sd)
            lf.update(reg=list(R), g=g, ex=ex, unf=paths, folds=folds, end=dict(end))
            me = len(unodes)
            unodes.append(('uleaf', len(leaves)))
            leaves.append(lf)
            if low or g not in self.fleaves:
                if g not in todo:
                    todo.append(g)
            return me

        def build(R, na, p):
            while True:
                try:
                    u0, l0 = len(unodes), len(leaves)
                    ui = run_unf(R, {'L': [], 'R': []}, na, p)
                    me = len(nodes)
                    nodes.append(('leaf', ui))
                    return me
                except Up as up:
                    rq = up.rq
                    # discard what the failed attempt built
                    del unodes[u0:]
                    del leaves[l0:]
                    k = rq.k
                    M, c = R[k]
                    me = len(nodes)
                    nodes.append(None)
                    if rq.kind in ('ge', 'uge'):
                        n = rq.n
                        kids = []
                        for v in range(n):
                            R2 = list(R)
                            R2[k] = (0, c + M * v)
                            kids.append(build(R2, 0, 1))
                        R2 = list(R)
                        R2[k] = (M, c + M * n)
                        kids.append(build(R2, na, p))
                        nodes[me] = ('split', k, n, 1, kids)
                    elif rq.kind in ('mod', 'pow', 'umod'):
                        pp = rq.n
                        kids = []
                        for s in range(pp):
                            R2 = list(R)
                            R2[k] = (M * pp, c + M * s)
                            kids.append(build(R2, na, p if rq.kind == 'umod' else pp))
                        nodes[me] = ('split', k, 0, pp, kids)
                    else:
                        raise Fail('request %s' % rq.kind)
                    return me

        nlv0 = len(leaves)
        build([(1, 0)] * F.n, 0, 1)
        for st in used:
            self.uses[st].add(fid)
        self.trees[fid] = nodes
        self.utrees[fid] = unodes
        self.fleaves[fid] = leaves


# ------------------------------------------------------------ assembly ----

def dsplit(d):
    return (d, 0) if d >= 0 else (0, -d)


def assemble(X, boot_t0, pins):
    """the certificate (liveness still missing): lcert fields, the families
    the boot reaches only, renumbered"""
    nfa = X.nfa
    reach = sorted(X.reach)
    fmap = {f: i for i, f in enumerate(reach)}
    # states
    sid = {}

    def st_id(sd, st):
        key = (sd, st)
        if key not in sid:
            sid[key] = len(sid)
        return sid[key]
    kinds = [(pre, u) for (_, pre, u) in nfa.kinds]
    trans = []
    for (sd, src, k, dst, rel) in nfa.trans:
        up, a, d = rel
        dp, dn = dsplit(d)
        trans.append(dict(left=(sd == 'L'), src=st_id(sd, src), kind=k, dst=st_id(sd, dst),
                          up=up, a=a, dp=dp, dn=dn))
    acc = sorted(set((sd == 'L', st_id(sd, st)) for (sd, st) in nfa.acc))
    m = nfa.mins()
    mins = {}
    for (sd, st), v in m.items():
        if v != float('inf') and v > 0:
            mins[(sd == 'L', st_id(sd, st))] = int(v)
    # lower until the Coq check holds (unlisted states count as 0)
    for _ in range(10000):
        ch = False
        for tr in trans:
            b = c_rbound(tr, mins.get((tr['left'], tr['dst']), 0))
            k = (tr['left'], tr['src'])
            if b is not None and mins.get(k, 0) > b:
                mins[k] = b
                ch = True
        if not ch:
            break
    for (l_, st), v in list(mins.items()):
        if (l_, st) in acc:
            mins[(l_, st)] = 0
    mins = sorted((k[0], k[1], v) for k, v in mins.items() if v > 0)
    # families, leaves
    fams, leaves = [], []
    for f in reach:
        F = X.fams[f]
        base = len(leaves)
        lmap = {}
        for li, lf in enumerate(X.fleaves[f]):
            G = X.fams[lf['g']]
            tgt = G.match(lf['ex'])
            if tgt is None:
                raise Fail('assemble: a target is not an instance')
            lmap[li] = len(leaves)
            paths = lf['unf']
            leaves.append(dict(f=fmap[f], reg=[tuple(x) for x in lf['reg']], g=fmap[lf['g']],
                               tgt=tgt, c0=lf['c0'], j=lf['j'], el=lf['el'], er=lf['er'],
                               nL=lf['nL'], nR=lf['nR'], chain=lf['chain'],
                               fL=list(lf['folds']['L']), fR=list(lf['folds']['R']),
                               uL=[x for x in paths['L'] if x != 'end'],
                               uR=[x for x in paths['R'] if x != 'end']))
        un = []
        for nd in X.utrees[f]:
            if nd[0] == 'uleaf':
                un.append(('uleaf', lmap[nd[1]]))
            elif nd[0] == 'void':
                un.append(nd)
            else:
                _, sd, endk, kids = nd
                un.append(('unf', sd, endk, kids))
        pat = F.pattern()
        tl = None if F.tL is None else (st_id('L', F.tL), F.ref('L'))
        tr = None if F.tR is None else (st_id('R', F.tR), F.ref('R'))
        fams.append(dict(q=F.q, h=F.h, L=pat[0], R=pat[1], n=F.n, tree=X.trees[f], utree=un,
                         tL=tl, tR=tr))
    f0, ex0, folds0, conc = X.boot
    F0 = X.fams[f0]
    v0 = F0.match(ex0)
    if v0 is None or any(e[1] for e in v0):
        raise Fail('assemble: boot not an instance')
    v0 = [e[0] for e in v0]
    # the anchor's tails: what the boot's family folded, then the boot's own
    ct = {sd: [(ti, e[0]) for ti, e in folds0[sd]] + list(conc[sd]) for sd in ('L', 'R')}
    a0 = dict(f=fmap[f0], v=v0, L=[tuple(x) for x in ct['L']], R=[tuple(x) for x in ct['R']])
    return dict(pins=sorted(pins), kinds=kinds, trans=trans, acc=acc, mins=mins, fams=fams,
                leaves=leaves, t0=boot_t0, a0=a0)


def c_rbound(tr, md):
    """ListGlueTr.rbound (nat subtraction truncates)"""
    a, dp, dn = tr['a'], tr['dp'], tr['dn']
    if tr['up']:
        if a == 0:
            return 0 if md + dn <= dp else None
        return max(0, md + dn - dp + a - 1) // a
    if a == 0:
        return max(0, dp - dn) if md == 0 else None
    return max(0, a * md + dp - dn)


# -------------------------------------------------------- replica ----

def c_relchk(tr, p, e):
    a, dp, dn = tr['a'], tr['dp'], tr['dn']
    if tr['up']:
        return aeq(C.aaddc(e, dn), C.aaddc(C.ascale(a, p), dp))
    if a == 0:
        return aeq(C.aaddc(p, dn), (dp, ())) and aeq(e, (0, ()))
    return aeq(C.aaddc(p, dn), C.aaddc(C.ascale(a, e), dp))


def c_relsem(tr, p, e):
    a, dp, dn = tr['a'], tr['dp'], tr['dn']
    if tr['up']:
        return e + dn == a * p + dp
    if a == 0:
        return p + dn == dp and e == 0
    return p + dn == a * e + dp


def anocoef(e):
    return all(a == 0 for _, a in e[1])


def c_tvoid(tr, r):
    a, dp, dn = tr['a'], tr['dp'], tr['dn']
    c = r[0]
    if tr['up']:
        return anocoef(r) and a * c + dp < dn
    if a == 0:
        return anocoef(r) and c + dn != dp
    return (C.pdiv(a, r) and (c + dn) % a != dp % a) or (anocoef(r) and c + dn < dp)


def c_accb(cert, left, s):
    return (left, s) in set(tuple(x) for x in cert['acc'])


def c_mget(cert, left, s):
    for l_, st, v in cert['mins']:
        if l_ == left and st == s:
            return v
    return 0


def c_mins_ok(cert):
    for tr in cert['trans']:
        b = c_rbound(tr, c_mget(cert, tr['left'], tr['dst']))
        if b is not None and c_mget(cert, tr['left'], tr['src']) > b:
            return False
    for l_, st, v in cert['mins']:
        if c_accb(cert, l_, st) and v != 0:
            return False
    return True


def c_item_segs(cert, k, e):
    if k >= len(cert['kinds']):
        return []
    pre, u = cert['kinds'][k]
    return [('L', tuple(pre)), ('B', tuple(u), e)]


def c_isegs(cert, I):
    out = []
    for t, e in I:
        k = cert['trans'][t]['kind'] if t < len(cert['trans']) else 0
        out += c_item_segs(cert, k, e)
    return out


def c_cover(cert, left, s, kids):
    ts = set(t for t, _, _ in kids)
    for i, tr in enumerate(cert['trans']):
        if tr['left'] == left and tr['src'] == s and i not in ts:
            return False
    return True


def c_uleaves(cert, ut, fuel, u, pL, pR, iL, iR):
    if fuel == 0 or u is None or u >= len(ut):
        return None
    nd = ut[u]
    if nd[0] == 'uleaf':
        return [(nd[1], pL, pR, iL, iR)]
    if nd[0] == 'void':
        left = nd[1] == 'L'
        p = pL if left else pR
        if p is None:
            return None
        s, r = p
        return [] if anocoef(r) and r[0] < c_mget(cert, left, s) else None
    _, sd, endk, kids = nd
    left = sd == 'L'
    p = pL if left else pR
    if p is None:
        return None
    s, r = p
    if not c_cover(cert, left, s, kids):
        return None
    out = []
    if c_accb(cert, left, s):
        if endk is None:
            return None
        sub = c_uleaves(cert, ut, fuel - 1, endk, None if left else pL, pR if left else None, iL, iR)
        if sub is None:
            return None
        out += sub
    for t, e, u2 in kids:
        if t >= len(cert['trans']):
            return None
        tr = cert['trans'][t]
        if tr['left'] != left or tr['src'] != s:
            return None
        if e is None:
            if not c_tvoid(tr, r):
                return None
            continue
        if not c_relchk(tr, r, e):
            return None
        if left:
            sub = c_uleaves(cert, ut, fuel - 1, u2, (tr['dst'], e), pR, iL + [(t, e)], iR)
        else:
            sub = c_uleaves(cert, ut, fuel - 1, u2, pL, (tr['dst'], e), iL, iR + [(t, e)])
        if sub is None:
            return None
        out += sub
    return out


def c_fchain(cert, left, s, r, F):
    for t, e in F:
        if t >= len(cert['trans']):
            return None
        tr = cert['trans'][t]
        if not (tr['left'] == left and tr['src'] == s and c_relchk(tr, r, e)):
            return None
        s, r = tr['dst'], e
    return s, r


def c_tail_end_ok(cert, left, sg, F, p):
    if sg is None:
        return not F and p is None
    s0, r0 = sg
    fc = c_fchain(cert, left, s0, r0, F)
    if fc is None:
        return False
    s1, r1 = fc
    if p is None:
        return c_accb(cert, left, s1)
    return s1 == p[0] and aeq(r1, p[1])


def sp_subst(tgt, sp):
    return None if sp is None else (sp[0], C.asubst(tgt, sp[1]))


def c_leaf_ok(cert, tabw, F, lf, pL, pR, iL, iR):
    fams = cert['fams']
    if lf['g'] >= len(fams):
        return 'g'
    G = fams[lf['g']]
    sub = C.rsub(lf['reg'])
    Lz = [C.seg_subst(sub, x) for x in F['L']] + c_isegs(cert, iL)
    Rz = [C.seg_subst(sub, x) for x in F['R']] + c_isegs(cert, iR)
    c0 = lf['c0']
    try:
        r = LC.srun(tabw, lf['el'], lf['er'], lf['chain'], c0)
    except LC.Halt:
        r = None
    if r is None:
        return 'srun'
    c1, ca, cb = r
    j = lf['j']
    tgt = lf['tgt']
    if not (c0[0] == F['q'] and c0[2] == F['h']):
        return 'start state'
    if not C.same_segs(C.ss_segs(c0[1], j) + Lz[lf['nL']:], Lz):
        return 'start L'
    if not C.same_segs(C.ss_segs(c0[3], j) + Rz[lf['nR']:], Rz):
        return 'start R'
    if lf['el'] and not (len(Lz) <= lf['nL'] and pL is None):
        return 'el'
    if lf['er'] and not (len(Rz) <= lf['nR'] and pR is None):
        return 'er'
    if not (c1[0] == G['q'] and c1[2] == G['h']):
        return 'end state'
    for side, p, cs, nS, Sz, gS, fS in (('L', pL, c1[1], lf['nL'], Lz, G['L'], lf['fL']),
                                        ('R', pR, c1[3], lf['nR'], Rz, G['R'], lf['fR'])):
        post = C.ss_segs(cs, j) + Sz[nS:]
        rhs = [C.seg_subst(tgt, x) for x in gS] + c_isegs(cert, fS)
        ok = C.lsame_segs(post, rhs) if p is None else C.same_segs(post, rhs)
        if not ok:
            return 'end ' + side
    if not c_tail_end_ok(cert, True, sp_subst(tgt, G['tL']), lf['fL'], pL):
        return 'tail L'
    if not c_tail_end_ok(cert, False, sp_subst(tgt, G['tR']), lf['fR'], pR):
        return 'tail R'
    if not (cb > 0 and len(tgt) == G['n'] and len(lf['reg']) == F['n']):
        return 'sizes'
    return None


def c_fams_ok(cert, tabw):
    for fi, F in enumerate(cert['fams']):
        L = C.tleaves(F['tree'], len(F['tree']), 0, [(1, 0)] * F['n'])
        if L is None:
            return 'bad tree %d' % fi
        for u, R in L:
            sp = lambda x: None if x is None else (x[0], C.asubst(C.rsub(R), x[1]))
            Ls = c_uleaves(cert, F['utree'], len(F['utree']), u, sp(F['tL']), sp(F['tR']), [], [])
            if Ls is None:
                return 'uleaves fam %d node %d' % (fi, u)
            for l, pL, pR, iL, iR in Ls:
                if l >= len(cert['leaves']):
                    return 'leaf index'
                lf = cert['leaves'][l]
                if lf['f'] != fi or [tuple(x) for x in lf['reg']] != [tuple(x) for x in R]:
                    return 'leaf %d misfiled' % l
                if [tuple(x) for x in lf['uL']] != [tuple(x) for x in iL] or \
                        [tuple(x) for x in lf['uR']] != [tuple(x) for x in iR]:
                    return 'leaf %d path' % l
                err = c_leaf_ok(cert, tabw, F, lf, pL, pR, iL, iR)
                if err:
                    return 'leaf %d: %s' % (l, err)
    return None


def c_trend(cert, T):
    out = ()
    for t, e in T:
        k = cert['trans'][t]['kind']
        pre, u = cert['kinds'][k]
        out += tuple(pre) + C.rep(u, e)
    return out


def c_tvalidb(cert, left, s, r, T):
    for t, e in T:
        if t >= len(cert['trans']):
            return False
        tr = cert['trans'][t]
        if not (tr['left'] == left and tr['src'] == s and c_relsem(tr, r, e)):
            return False
        s, r = tr['dst'], e
    return c_accb(cert, left, s)


def c_tanc(cert, a):
    F = cert['fams'][a['f']]
    return (F['q'], C.sided(a['v'], F['L']) + c_trend(cert, a['L']), F['h'],
            C.sided(a['v'], F['R']) + c_trend(cert, a['R']))


def c_uwalk(ut, fuel, u, TL, TR):
    for _ in range(fuel):
        if u is None or u >= len(ut):
            return None
        nd = ut[u]
        if nd[0] == 'uleaf':
            return nd[1], TL, TR
        if nd[0] == 'void':
            return None
        _, sd, endk, kids = nd
        T = TL if sd == 'L' else TR
        if not T:
            u = endk
            continue
        t = T[0][0]
        k = next((x for x in kids if x[0] == t), None)
        if k is None or k[1] is None:
            return None
        u = k[2]
        if sd == 'L':
            TL = TL[1:]
        else:
            TR = TR[1:]
    return None


def c_lwalk(cert, a):
    F = cert['fams'][a['f']]
    r = C.twalk(F['tree'], len(F['tree']), 0, [(1, 0)] * F['n'], a['v'])
    if r is None:
        return None
    u, R, z = r
    w = c_uwalk(F['utree'], len(F['utree']), u, list(a['L']), list(a['R']))
    if w is None:
        return None
    l, TL, TR = w
    return l, R, z, TL, TR


def c_boot_ok(cert, tab, tabw):
    a0 = cert['a0']
    F = cert['fams'][a0['f']]
    r = T.run_conc(tabw, cert['t0'])
    if r is None:
        return 'boot run'
    q, L, h, R, _ = r
    q2, L2, h2, R2 = c_tanc(cert, a0)
    strip = C.rstrip0
    if not ((q, h) == (q2, h2) and strip(L) == strip(L2) and strip(R) == strip(R2)):
        return 'boot config'
    if len(a0['v']) != F['n']:
        return 'boot n'
    for sd, key in (('L', 'tL'), ('R', 'tR')):
        sp = F[key]
        T_ = a0[sd]
        if sp is None:
            if T_:
                return 'boot tail'
        elif not c_tvalidb(cert, sd == 'L', sp[0], C.aeval(a0['v'], sp[1]), T_):
            return 'boot tail valid'
    return None
# ----------------------------------------------------------- liveness ----

def leaf_fired(tabw, lf):
    return set(C.leaf_fired(tabw, dict(chain=lf['chain'], el=lf['el'], er=lf['er'], c0=lf['c0'])))


def isub(sub, I):
    return [(t, C.asubst(sub, e)) for t, e in I]


def l_edges(cert, P, node):
    """[(src, tgt, uL, uR, fL, fR, rho', [candidate leaves])] of a node, or None"""
    l, rho = node
    lvs = cert['leaves']
    lf = lvs[l]
    out = []
    for s_ in C.sassign(P, lf['reg'], list(rho)):
        sub = C.zsub(P, s_)
        src = [C.asubst(sub, e) for e in C.rsub(lf['reg'])]
        tgt = [C.asubst(sub, e) for e in lf['tgt']]
        if not all(C.pdiv(P, e) for e in tgt):
            return None
        rho2 = tuple(e[0] % P for e in tgt)
        cands = [l2 for l2, lf2 in enumerate(lvs)
                 if lf2['f'] == lf['g'] and C.compat(P, lf2['reg'], tgt)]
        out.append((src, tgt, isub(sub, lf['uL']), isub(sub, lf['uR']),
                    isub(sub, lf['fL']), isub(sub, lf['fR']), rho2, cands))
    return out


def l_boot_node(cert, P):
    w = c_lwalk(cert, cert['a0'])
    if w is None:
        return None
    return (w[0], tuple(v % P for v in cert['a0']['v']))


def l_live_search(cert, tabw, fired, P):
    """closed node set from the boot, then per instruction a ranking: the
    window affine, per node and side one weight per tail item"""
    import numpy as np
    from scipy.optimize import milp, LinearConstraint, Bounds
    b = l_boot_node(cert, P)
    if b is None:
        return 'boot walk'
    S = [b]
    seen = {b}
    E = {}
    k = 0
    while k < len(S):
        nd = S[k]
        k += 1
        es = l_edges(cert, P, nd)
        if es is None:
            return 'pdiv'
        E[nd] = es
        for e in es:
            for l2 in e[7]:
                n2 = (l2, e[6])
                if n2 not in seen:
                    seen.add(n2)
                    S.append(n2)
        if len(S) > 6000:
            return 'too many nodes'
    nv = {nd: cert['fams'][cert['leaves'][nd[0]]['f']]['n'] for nd in S}
    off = {}
    n = 0
    for nd in S:
        off[nd] = n
        n += 3 + nv[nd]      # c, coefs, bL, bR
    ranks = []
    for q in range(4):
        for h in range(2):
            t = (q, h)
            if t in cert['pins']:
                continue
            A, lo = [], []
            for nd in S:
                if t in fired[nd[0]]:
                    continue
                for (src, tgt, uL, uR, fL, fR, rho2, cands) in E[nd]:
                    for l2 in cands:
                        if t in fired[l2]:
                            continue
                        n2 = (l2, rho2)
                        o, o2 = off[nd], off[n2]
                        m1, m2 = nv[nd], nv[n2]
                        params = sorted(set(p for e in src + tgt for p, _ in e[1]))
                        row = np.zeros(n)
                        row[o] += 1
                        row[o2] -= 1
                        for kk, e in enumerate(src[:m1]):
                            row[o + 1 + kk] += e[0]
                        for kk, e in enumerate(tgt[:m2]):
                            row[o2 + 1 + kk] -= e[0]
                        row[o + 1 + m1] += len(uL)
                        row[o + 2 + m1] += len(uR)
                        row[o2 + 1 + m2] -= len(fL)
                        row[o2 + 2 + m2] -= len(fR)
                        A.append(row)
                        lo.append(1)
                        for p_ in params:
                            row = np.zeros(n)
                            for kk, e in enumerate(src[:m1]):
                                row[o + 1 + kk] += C.tcoef(p_, e[1])
                            for kk, e in enumerate(tgt[:m2]):
                                row[o2 + 1 + kk] -= C.tcoef(p_, e[1])
                            A.append(row)
                            lo.append(0)
                        for dd in (1, 2):
                            row = np.zeros(n)
                            row[o + dd + m1] += 1
                            row[o2 + dd + m2] -= 1
                            A.append(row)
                            lo.append(0)
            if not A:
                continue
            A = np.array(A)
            res = milp(c=np.ones(n), constraints=LinearConstraint(A, np.array(lo), np.inf),
                       integrality=np.ones(n), bounds=Bounds(0, 10 ** 6))
            if not res.success:
                return ('norank', t)
            x = np.round(res.x).astype(int)
            if (A @ x < np.array(lo)).any():
                return ('norank', t)
            V = [dict(V=(int(x[off[nd]]), [int(y) for y in x[off[nd] + 1:off[nd] + 1 + nv[nd]]]),
                      bL=int(x[off[nd] + 1 + nv[nd]]), bR=int(x[off[nd] + 2 + nv[nd]]))
                 for nd in S]
            ranks.append((t, V))
    return dict(P=P, S=[(l, list(rho)) for l, rho in S], ranks=ranks)


def c_twa(b, I):
    """twa with an empty weight list: every item (0, b)"""
    acc = (0, ())
    for _ in I:
        acc = C.aadd(acc, (b, ()))
    return acc


def c_live_ok(cert, tabw, fired):
    """ListGlueTr.llive_ok (the weight lists are empty: every item weighs (0, b))"""
    P = cert['P']
    if P <= 0:
        return 'P'
    S = [(l, tuple(r)) for l, r in cert['S']]
    rk = dict((tuple(t), V) for t, V in cert['ranks'])
    for i, nd in enumerate(S):
        if nd[0] >= len(cert['leaves']):
            return 'node leaf'
        es = l_edges(cert, P, nd)
        if es is None:
            return 'pdiv'
        for (src, tgt, uL, uR, fL, fR, rho2, cands) in es:
            for l2 in cands:
                try:
                    i2 = S.index((l2, rho2))
                except ValueError:
                    return 'not closed'
                for q in range(4):
                    for h in range(2):
                        t = (q, h)
                        if t in cert['pins'] or t in fired[nd[0]] or t in fired[l2]:
                            continue
                        Vs = rk.get(t, [])
                        z = dict(V=(0, []), bL=0, bR=0)
                        r = Vs[i] if i < len(Vs) else z
                        r2 = Vs[i2] if i2 < len(Vs) else z
                        lhs = C.aaddc(C.aadd(C.veval(r2['V'], tgt),
                                             C.aadd(c_twa(r2['bL'], fL), c_twa(r2['bR'], fR))), 1)
                        rhs = C.aadd(C.veval(r['V'], src),
                                     C.aadd(c_twa(r['bL'], uL), c_twa(r['bR'], uR)))
                        if not C.ale(lhs, rhs) or r2['bL'] > r['bL'] or r2['bR'] > r['bR']:
                            return 'rank %s at node %d' % (t, i)
    return None


def c_check(cert, tab):
    """every part of lg_check, replayed"""
    tabw = {k: (None if k in cert['pins'] else v) for k, v in tab.items()}
    if not c_mins_ok(cert):
        return 'mins'
    err = c_fams_ok(cert, tabw)
    if err:
        return 'fams: ' + err
    fired = [leaf_fired(tabw, lf) for lf in cert['leaves']]
    err = c_live_ok(cert, tabw, fired)
    if err:
        return 'live: ' + err
    err = c_boot_ok(cert, tab, tabw)
    if err:
        return err
    b = l_boot_node(cert, cert['P'])
    if b is None or (b[0], list(b[1])) not in [(l, list(r)) for l, r in cert['S']]:
        return 'boot node'
    return None


# -------------------------------------------------------------- render ----

ST = ['StA', 'StB', 'StC', 'StD']
SYM = ['S0', 'S1']


def r_list(xs):
    return '[' + ';'.join(SYM[x] for x in xs) + ']'


def r_aexp(e):
    return '(mkA %d [%s])' % (e[0], ';'.join('(%d,%d)' % (k, a) for k, a in e[1] if a))


def r_seg(x):
    return '(SL %s)' % r_list(x[1]) if x[0] == 'L' else '(SB %s %s)' % (r_list(x[1]), r_aexp(x[2]))


def r_segs(l):
    return '[' + ';'.join(r_seg(x) for x in l) + ']'


def r_bool(b):
    return 'true' if b else 'false'


def r_opt(x, f):
    return 'None' if x is None else '(Some %s)' % f(x)


def r_items(I):
    return '[' + ';'.join('(%d,%s)' % (t, r_aexp(e)) for t, e in I) + ']'


def r_cert(c):
    pins = '[' + ';'.join('(%s,%s)' % (ST[q], SYM[h]) for q, h in c['pins']) + ']'
    kinds = '[' + ';'.join('(%s,%s)' % (r_list(pre), r_list(u)) for pre, u in c['kinds']) + ']'
    trans = '[' + ';'.join('(mkLT %s %d %d %d %s %d %d %d)' % (
        r_bool(t['left']), t['src'], t['kind'], t['dst'], r_bool(t['up']), t['a'], t['dp'], t['dn'])
        for t in c['trans']) + ']'
    acc = '[' + ';'.join('(%s,%d)' % (r_bool(l), s) for l, s in c['acc']) + ']'
    mins = '[' + ';'.join('(%s,%d,%d)' % (r_bool(l), s, v) for l, s, v in c['mins']) + ']'

    def r_unode(nd):
        if nd[0] == 'uleaf':
            return '(ULeaf %d)' % nd[1]
        if nd[0] == 'void':
            return '(UVoid %s)' % r_bool(nd[1] == 'L')
        _, sd, endk, kids = nd
        ks = ';'.join('(%d,%s)' % (t, 'None' if e is None else '(Some (%s,%d))' % (r_aexp(e), u))
                      for t, e, u in kids)
        return '(UUnf %s %s [%s])' % (r_bool(sd == 'L'), r_opt(endk, str), ks)

    fams = '[' + ';\n      '.join('(mkLF %s %s %s %s %d [%s] [%s] %s %s)' % (
        ST[F['q']], SYM[F['h']], r_segs(F['L']), r_segs(F['R']), F['n'],
        ';'.join(T.cnode(nd) for nd in F['tree']), ';'.join(r_unode(nd) for nd in F['utree']),
        r_opt(F['tL'], lambda x: '(%d,%s)' % (x[0], r_aexp(x[1]))),
        r_opt(F['tR'], lambda x: '(%d,%s)' % (x[0], r_aexp(x[1]))))
        for F in c['fams']) + ']'
    leaves = '[' + ';\n      '.join('(mkLL %d [%s] %d [%s] (mkC %s %s %s %s) %d %s %s %d %d %s %s %s %s %s)' % (
        lf['f'], ';'.join('(%d,%d)' % tuple(x) for x in lf['reg']), lf['g'],
        ';'.join(r_aexp(e) for e in lf['tgt']),
        ST[lf['c0'][0]], T.cside(lf['c0'][1]), SYM[lf['c0'][2]], T.cside(lf['c0'][3]),
        lf['j'], r_bool(lf['el']), r_bool(lf['er']), lf['nL'], lf['nR'], T.cchain(lf['chain']),
        r_items(lf['fL']), r_items(lf['fR']), r_items(lf['uL']), r_items(lf['uR']))
        for lf in c['leaves']) + ']'
    S = '[' + ';'.join('(%d,[%s])' % (l, ';'.join(str(x) for x in r)) for l, r in c['S']) + ']'
    ranks = '[' + ';\n      '.join('((%s,%s), [%s])' % (
        ST[t[0]], SYM[t[1]], ';'.join('(mkRk (%d,[%s]) [] %d [] %d)' % (
            v['V'][0], ';'.join(str(x) for x in v['V'][1]), v['bL'], v['bR']) for v in V))
        for t, V in c['ranks']) + ']'
    a0 = c['a0']
    a0s = '(mkAn %d [%s] [%s] [%s])' % (a0['f'], ';'.join(str(x) for x in a0['v']),
                                        ';'.join('(%d,%d)' % tuple(x) for x in a0['L']),
                                        ';'.join('(%d,%d)' % tuple(x) for x in a0['R']))
    return '(mkLC %s\n      %s\n      %s\n      %s\n      %s\n      %s\n      %s\n      %d %s\n      %s\n      %d %s)' % (
        pins, kinds, trans, acc, mins, fams, leaves, c['P'], S, ranks, c['t0'], a0s)


def render(c):
    lemma = 'lg_sound_mirror' if c.get('mir') else 'lg_sound'
    return 'apply coversTr_nqh, (%s _\n      %s).\n  vm_cast_no_check (eq_refl true).' % (
        lemma, r_cert(c))
# ---------------------------------------------------------------- boot ----

def run_rec(tab, n):
    """the configuration at the last record step (the head on a new cell)
    at or before step n: (q, L, h, R, t)"""
    tape, pos, q, lo, hi = {}, 0, 0, 0, 0
    last = None
    for t in range(n):
        h = tape.get(pos, 0)
        tr = tab[(q, h)]
        if tr is None:
            return None
        w, d, nq = tr
        tape[pos] = w
        pos += d
        q = nq
        if pos < lo or pos > hi:
            lo, hi = min(lo, pos), max(hi, pos)
            last = (t + 1, q, pos, lo, hi)
    t, q, pos, lo, hi = last
    return T.run_conc(tab, t)[:4] + (t,)


def boot_of(X, tab, t0):
    """the concrete tape after t0 steps as (q, L, h, R, tails, concrete tails):
    the window keeps KEEP blocks a side, the rest are tail items whose
    relations are read off the concrete lengths (the list ratio)"""
    r = run_rec(X.tabw, t0)
    if r is None:
        raise Fail('halts')
    q, L, h, R, t0 = r
    X.t0 = t0
    nfa = X.nfa
    X.booting = True
    out, tails, conc = {}, {}, {}
    rs = []
    for side in (L, R):
        es = [x[2][0] for x in gen_side(side) if x[0] == 'B']
        for a, b in zip(es, es[1:]):
            lo, hi = min(a, b), max(a, b)
            if lo >= 8:
                rs.append(round(hi / lo))
    RATIO[0] = max(1, min(BOOT_AMAX, collections.Counter(rs).most_common(1)[0][0])) if rs else 2
    for sd, side in (('L', L), ('R', R)):
        segs = gen_side(side)
        W, cur, folds = X.fold(sd, segs, None)
        out[sd] = W
        tails[sd] = cur
        conc[sd] = [(ti, e[0]) for ti, e in folds]
    X.booting = False
    return q, out['L'], h, out['R'], tails, conc


NDATA = 3000


def explore_row(spec, t0, mir=False, dfa_k=None):
    tab = T.parse(spec)
    if mir:
        tab = T.mirror(tab)
    r2 = T.run_conc(tab, 60000)
    if r2 is None:
        raise Fail('halts')
    pins = set(k for k in tab if k not in r2[4])
    X = Explorer(tab, pins)
    global _lastX
    _lastX = X
    boot = boot_of(X, tab, t0)
    X.data_pass(boot, NDATA)
    if dfa_k is not None:
        # the tail language, learned from the pass's tails; then a second
        # pass (under the DFA) seeds the hulls of the families it keys
        dfas = {}
        fits = {}
        if dfa_k == 'bps':
            fits = {sd: fit_bps(X.samples[sd]) for sd in ('L', 'R')}
            # both tails are one list: the side with more digits fits both
            ws = {sd: (f['weight'] if f else 0) for sd, f in fits.items()}
            src = max(ws, key=lambda sd: ws[sd])
            oth = 'L' if src == 'R' else 'R'
            if fits[src] is not None:
                tr = transfer_bps(fits[src], X.nfa.kinds, X.nfa.kidx, oth)
                if tr is not None and ws[oth] < 4 * ws[src] and BPS_TRANSFER:
                    fits[oth] = tr
        for sd in ('L', 'R'):
            if dfa_k == 'bps':
                d = None if fits[sd] is None else build_bps(fits[sd], X.samples[sd])
            else:
                d = learn_dfa(list(X.samples[sd]), dfa_k)
            if d is None:
                if not X.samples[sd]:
                    d = ({}, 0)
                else:
                    raise Fail('dfa %s: no automaton for side %s' % (dfa_k, sd))
            dfas[sd] = d
        X.use_dfa(dfas)
        boot = boot_of(X, tab, t0)
        X.data_pass(boot, NDATA)
    X.explore(boot)
    return X, pins, boot


# --------------------------------------------------------------- driver ----

def find_dir(spec, mir, t0, dfa_k=None):
    X, pins, boot = explore_row(spec, t0, mir, dfa_k)
    tab = T.parse(spec)
    if mir:
        tab = T.mirror(tab)
    cert = assemble(X, X.t0, pins)
    cert['mir'] = mir
    tabw = X.tabw
    err = c_fams_ok(cert, tabw)
    if err:
        return dict(err='fams: ' + err, nfam=len(cert['fams']))
    err = c_boot_ok(cert, tab, tabw)
    if err:
        return dict(err=err)
    fired = [leaf_fired(tabw, lf) for lf in cert['leaves']]
    last = None
    for P in PLIST:
        lv = l_live_search(cert, tabw, fired, P)
        if isinstance(lv, dict):
            cert.update(lv)
            err = c_check(cert, tab)
            if err:
                return dict(err='check: ' + err)
            return cert
        last = lv
    return dict(err='norank %s' % (last,), nfam=len(cert['fams']))


class Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise Timeout()


def find(spec, timeout=0, t0s=T0S):
    if timeout:
        signal.signal(signal.SIGALRM, _alarm)
        signal.alarm(timeout)
    errs = []
    try:
        for mir in (False, True):
            for t0, k in [(t0, k) for t0 in t0s for k in ((None,) + DFA_K if CANON else (None,))]:
                try:
                    r = find_dir(spec, mir, t0, k)
                except Fail as e:
                    r = dict(err=str(e))
                except RecursionError:
                    r = dict(err='recursion')
                if 'err' not in r:
                    r['spec'] = spec
                    return r
                errs.append('%s t%d%s %s' % ('m' if mir else 'd', t0,
                                              '' if k is None else ' %s' % (k,), r['err']))
    except Timeout:
        errs.append('timeout')
    finally:
        if timeout:
            signal.alarm(0)
    return dict(spec=spec, err=' / '.join(errs))


def jsonable(c):
    def conv(x):
        if isinstance(x, (list, tuple)):
            return [conv(y) for y in x]
        if isinstance(x, dict):
            return {str(k): conv(v) for k, v in x.items()}
        if isinstance(x, set):
            return sorted(conv(y) for y in x)
        return x
    return conv(c)


def detuple(c):
    def TT(x):
        return tuple(TT(y) for y in x) if isinstance(x, list) else x
    c['pins'] = [tuple(p) for p in c['pins']]
    c['kinds'] = [(tuple(a), tuple(b)) for a, b in c['kinds']]
    c['acc'] = [tuple(x) for x in c['acc']]
    c['mins'] = [tuple(x) for x in c['mins']]

    def seg(x):
        return ('L', tuple(x[1])) if x[0] == 'L' else ('B', tuple(x[1]), TT(x[2]))
    for F in c['fams']:
        F['L'] = [seg(x) for x in F['L']]
        F['R'] = [seg(x) for x in F['R']]
        F['tree'] = [tuple(TT(x) if i < 4 else list(x) for i, x in enumerate(nd))
                     if nd[0] == 'split' else tuple(nd) for nd in F['tree']]
        ut = []
        for nd in F['utree']:
            if nd[0] == 'unf':
                ut.append(('unf', nd[1], nd[2], [(k[0], None if k[1] is None else TT(k[1]), k[2])
                                                 for k in nd[3]]))
            else:
                ut.append(tuple(nd))
        F['utree'] = ut
        F['tL'] = None if F['tL'] is None else (F['tL'][0], TT(F['tL'][1]))
        F['tR'] = None if F['tR'] is None else (F['tR'][0], TT(F['tR'][1]))
    for lf in c['leaves']:
        lf['c0'] = TT(lf['c0'])
        lf['tgt'] = [TT(e) for e in lf['tgt']]
        lf['chain'] = [tuple(x) for x in lf['chain']]
        lf['reg'] = [tuple(x) for x in lf['reg']]
        for k in ('fL', 'fR', 'uL', 'uR'):
            lf[k] = [(t, TT(e)) for t, e in lf[k]]
    c['ranks'] = [(tuple(t), V) for t, V in c['ranks']]
    return c


def _find1(args):
    return find(*args)


def cmd_find(a):
    specs = [l.split()[0] for l in open(a.rows) if l.strip() and not l.startswith('#')]
    done = set()
    if os.path.exists(a.out):
        done = set(json.loads(l)['spec'] for l in open(a.out))
    todo = [(s, a.timeout) for s in specs if s not in done]
    stats = collections.Counter()
    with open(a.out, 'a') as f, Pool(a.jobs) as pool:
        for r in pool.imap_unordered(_find1, todo):
            f.write(json.dumps(jsonable(r)) + '\n')
            f.flush()
            stats['ok' if 'err' not in r else 'fail'] += 1
            print(r['spec'], r.get('err', 'OK')[:200], flush=True)
    print(dict(stats))


def cmd_batch(a):
    from cbt import next_free, write_batch
    rem = T.remaining()
    certs, seen = [], set()
    for p in a.found:
        for line in open(p):
            c = json.loads(line)
            s = c['spec']
            if 'err' in c or s not in rem or s in seen or s in a.skip:
                continue
            seen.add(s)
            certs.append(detuple(c))
    nn = next_free(a.tag)
    made = []
    for i in range(0, len(certs), a.chunk):
        chunk = certs[i:i + a.chunk]
        entries = [(c['spec'], render(c)) for c in chunk]
        made.append(write_batch(a.tag, nn, ['From BBB4.Checkers Require Import LapDecider.',
                                            'From BBB4.Counters Require Import TriGlueTr ListGlueTr.'],
                                entries, 'block-list rows by the list glue (ListGlueTr, lg_check)'))
        nn += 1
    print('%d rows -> %d batch file(s): %s' % (len(certs), len(made),
          ' '.join(os.path.relpath(p, T.REPO) for p in made)))


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest='cmd', required=True)
    p = sp.add_parser('find')
    p.add_argument('rows')
    p.add_argument('out')
    p.add_argument('--jobs', type=int, default=4)
    p.add_argument('--timeout', type=int, default=300)
    p = sp.add_parser('batch')
    p.add_argument('found', nargs='+')
    p.add_argument('--tag', default='BLC')
    p.add_argument('--chunk', type=int, default=10)
    p.add_argument('--skip', action='append', default=[])
    a = ap.parse_args()
    {'find': cmd_find, 'batch': cmd_batch}[a.cmd](a)


if __name__ == '__main__':
    main()
