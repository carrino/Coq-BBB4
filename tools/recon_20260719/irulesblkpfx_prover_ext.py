#!/usr/bin/env python3
"""Python model of the BLOCK-RUN + (phase 2) rule-prefix irules checker.

Forked from tools/irulesk_prover.py (the multi-decrement K checker model).
This is the executable design spec for the Coq checker
theories/Checkers/IRules/EngineK.v + RulesBlk.v + MetaBlk.v: a faithful
port of the v3 block machinery of ../BBB/src/verify.c and
../BBB/docs/irules2.md ("Block-level chain hops", "Canonical
re-blocking", "Cell-stream end equality").

THE CRUX (denotation).  Once a run's symbol can be a block id, a run
(B, e) denotes e copies of B's cell sequence, NOT e copies of one
symbol.  We carry the certificate's FULL (untrusted) block table `tbl`
and denote a side by

    bdside tbl nu rs = concat( cells(tbl,s) * cnt(nu,e)  for (s,e) in rs )

with cells(tbl,s) = [s] for a raw symbol s < NK (degenerate block), so a
raw-only side reduces to RLE.dside.  Soundness holds for ANY table.

Mechanisms (mirror of verify.c), each toggleable so the minimal set that
boards the 6 v3-blk holdouts can be measured:
  * block denotation (always on -- the template/rules reference blocks);
  * block-hop      iv_hop_sim  + iv_step block-hop branch (needs HOPS);
  * block-peel     iv_step block-peel branch (always on when a block run
                   is met and the hop is off or fails);
  * canonical re-blocking  iv_reblock_side  (needs HOPS);
  * cell-stream end equality  iv_streams_eq  (v3 meta end-match fallback).

Phase 2 (rulepfx) additions are gated by the cert `rulepfx` lines and the
sentinel engine hard-fail; see check_cert.

Usage:
  irulesblk_prover.py CERT ...            check each, print PASS/FAIL
  irulesblk_prover.py --dir DIR           check every *.cert in DIR
  irulesblk_prover.py --no-anchor ...     skip anchor+coverage (rule+meta only)
  irulesblk_prover.py --mech M ...        M in off,hop,peel,reblock,streams,all
"""
import sys, os, glob

FUEL = 300000
NK = 2  # 2-symbol machines

# ---------------------------------------------------------------------------
# Affine expressions:  Expr = (c0, cf).  eval nu e = c0 + sum cf_i*nu_i.
# ---------------------------------------------------------------------------

def econst(v):            return (v, ())
def evar(i):              return (0, tuple(1 if j == i else 0 for j in range(i + 1)))

def eaddc(e, v):          return (e[0] + v, e[1])

def _cf_addmul(a, d, b):
    n = max(len(a), len(b))
    return tuple((a[i] if i < len(a) else 0) + d * (b[i] if i < len(b) else 0)
                 for i in range(n))

def eaddmul(a, d, b):     return (a[0] + d * b[0], _cf_addmul(a[1], d, b[1]))
def eadd(a, b):           return eaddmul(a, 1, b)

def _cf_strip(cf):
    cf = list(cf)
    while cf and cf[-1] == 0:
        cf.pop()
    return tuple(cf)

def eeqb(a, b):
    return a[0] == b[0] and _cf_strip(a[1]) == _cf_strip(b[1])

def cf_nonneg(cf):        return all(c >= 0 for c in cf)

def _eval(e, nu):
    return e[0] + sum(c * nu(i) for i, c in enumerate(e[1]))

def _lo_nu(lo):
    return lambda i: (lo[i] if i < len(lo) else 0)

def elo(lo, e):           return _eval(e, _lo_nu(lo))

def expr_ge(lo, e, need):
    return cf_nonneg(e[1]) and need <= elo(lo, e)

def eisconst(e):
    return (None if _cf_strip(e[1]) else e[0])

def emin(lo, e):
    # min over nu >= lo, valid only when cf_nonneg
    return elo(lo, e)

def cnt(nu, e):           return max(0, _eval(e, nu))

def ediv(e, d):
    return (e[0] // d, tuple(c // d for c in e[1]))

def ebad(e):
    # placeholder: our Python affine exprs never overflow; C guards int64.
    return False

# ---------------------------------------------------------------------------
# TMs.  St A..D ; Sym 0/1 ; Dir 'L'/'R'.  tm[(q,s)] = (write,dir,next)|None.
# ---------------------------------------------------------------------------

ST = {"A": 0, "B": 1, "C": 2, "D": 3}
ALL_ST = [0, 1, 2, 3]

def parse_tm(machine):
    tm = {}
    for qi, g in enumerate(machine.split("_")):
        for si in range(2):
            t = g[3 * si:3 * si + 3]
            tm[(qi, si)] = None if t == "---" else (int(t[0]), t[1], ST[t[2]])
    return tm

def chainable(tm, q, s, mv):
    tr = tm.get((q, s))
    return tr is not None and tr[2] == q and tr[1] == mv

# ---------------------------------------------------------------------------
# Block table.  tbl: id -> list of raw cells.  Raw symbol s < NK => [s].
# ---------------------------------------------------------------------------

def blk_cells(tbl, s):
    if s < NK:
        return [s]
    return tbl.get(s)          # None if undefined (a miss aborts the op)

def blk_len(tbl, s):
    c = blk_cells(tbl, s)
    return len(c) if c is not None else 0

def blk_find(tbl, w):
    # content lookup: raw if len 1, else a table id with exactly these cells
    w = list(w)
    if len(w) == 1 and w[0] < NK:
        return w[0]
    for i, cells in tbl.items():
        if cells == w:
            return i
    return None

def primitive_root_len(w):
    # smallest p | len with w[i]==w[i%p]; else len
    L = len(w)
    for p in range(1, L):
        if L % p != 0:
            continue
        if all(w[i] == w[i % p] for i in range(p, L)):
            return p
    return L

# ---------------------------------------------------------------------------
# Concrete tape (CTape.v) for anchor sim + block-hop replay.
# ---------------------------------------------------------------------------

def _sim(tm, n, want_states=None):
    q = 0
    L, R, h = [], [], 0
    visited = set()
    for _ in range(n):
        if want_states is not None:
            visited.add(q)
        tr = tm[(q, h)]
        if tr is None:
            return (None, L, h, R, visited)
        w, d, q = tr
        if d == "R":
            L.append(w)
            h = R.pop() if R else 0
        else:
            R.append(w)
            h = L.pop() if L else 0
    return (q, L, h, R, visited)

# ---------------------------------------------------------------------------
# Symbolic runs.  SRun = (sym, Expr).  SCfg = (st, hs, L, R).
# ---------------------------------------------------------------------------

def push(lo, s, e, rs):
    if not expr_ge(lo, e, 0):
        return None
    if not rs:
        return [] if s == 0 else [(s, e)]
    s2, e2 = rs[0]
    if s == s2:
        if expr_ge(lo, e2, 0):
            return [(s2, eadd(e, e2))] + rs[1:]
        return None
    return [(s, e)] + rs

def merge_adj(lo, rs):
    if not rs:
        return []
    s, e = rs[0]
    mt = merge_adj(lo, rs[1:])
    if mt is None:
        return None
    if not mt:
        return [(s, e)]
    s2, e2 = mt[0]
    if s == s2:
        if expr_ge(lo, e, 0) and expr_ge(lo, e2, 0):
            return [(s, eadd(e, e2))] + mt[1:]
        return None
    return [(s, e)] + mt

def trim_blanks(rs):
    if not rs:
        return []
    s, e = rs[0]
    tt = trim_blanks(rs[1:])
    if not tt:
        return [] if s == 0 else [(s, e)]
    return [(s, e)] + tt

def sruns_eqb(a, b):
    if len(a) != len(b):
        return False
    return all(sa == sb and eeqb(ea, eb) for (sa, ea), (sb, eb) in zip(a, b))

def scfg_eqb(a, b):
    return (a[0] == b[0] and a[1] == b[1]
            and sruns_eqb(a[2], b[2]) and sruns_eqb(a[3], b[3]))

# ---------------------------------------------------------------------------
# Block-hop: bounded one-copy concrete replay (mirror of iv_hop_sim).
# ---------------------------------------------------------------------------

IVHOPCAP = 1024

def hop_sim(tm, tbl, q, mv, bid):
    cells = list(blk_cells(tbl, bid))
    blen = len(cells)
    fired = set()
    st = q
    idx = 0
    for _ in range(IVHOPCAP):
        s = cells[idx]
        tr = tm.get((st, s))
        if tr is None:
            return None
        fired.add((st, s))
        w, d, nx = tr
        cells[idx] = w
        idx += 1 if d == mv else -1
        st = nx
        if idx < 0:
            return None
        if idx >= blen:
            if st != q:
                return None
            return (cells, fired)
    return None

# ---------------------------------------------------------------------------
# The engine, one op (mirror of iv_step): concrete step + chain hops +
# block hops + block peels.  `hops` gates block-hop and re-blocking.
# `sent` = (sentL, sentR) sentinel flags (phase 2 rulepfx); when a
# sentinel side is exhausted the engine hard-fails (reads opaque rest).
# ---------------------------------------------------------------------------

def eng_step(tm, tbl, lo, hops, sent, c, Facc):
    st, hs, L, R = c
    tr = tm.get((st, hs))
    if tr is None:
        return None
    w, d, q1 = tr
    Facc.append((st, hs))
    if d == "R":
        dep, app = list(L), list(R)
    else:
        dep, app = list(R), list(L)
    dep = push(lo, w, econst(1), dep)
    if dep is None:
        return None
    q = q1
    hsym = None
    guard = 0
    while True:
        guard += 1
        if guard > 100000:
            return None
        if not app:
            si = 1 if d == "R" else 0
            if sent[si]:
                return None          # v5: would read the opaque rest
            if chainable(tm, q, 0, d):
                return None          # spin-out
            hsym = 0
            break
        top_sym, top_e = app[0]
        blen = blk_len(tbl, top_sym)
        if blen == 0:
            return None              # undefined block symbol
        if blen >= 2:
            if hops:
                hr = hop_sim(tm, tbl, q, d, top_sym)
                if hr is not None:
                    hout, hfired = hr
                    w2 = [hout[blen - 1 - j] for j in range(blen)]
                    root = primitive_root_len(w2)
                    nsym = w2[0] if root == 1 else blk_find(tbl, w2[:root])
                    cnt_e = eaddmul(econst(0), blen // root, top_e)
                    if nsym is not None and not ebad(cnt_e):
                        app = app[1:]
                        dep = push(lo, nsym, cnt_e, dep)
                        if dep is None:
                            return None
                        for t in hfired:
                            Facc.append(t)
                        continue
            # peel the nearest copy of the block into cells
            v = eisconst(top_e)
            if v == 1:
                app = app[1:]
            else:
                if not expr_ge(lo, top_e, 2):
                    return None
                app = [(top_sym, eaddc(top_e, -1))] + app[1:]
            cells = blk_cells(tbl, top_sym)
            for j in range(blen - 1, -1, -1):
                app = push(lo, cells[j], econst(1), app)
                if app is None:
                    return None
            continue
        # raw run (blen == 1)
        if chainable(tm, q, top_sym, d):
            if not expr_ge(lo, top_e, 1):
                return None
            w2 = tm[(q, top_sym)][0]
            e = top_e
            app = app[1:]
            dep = push(lo, w2, e, dep)
            if dep is None:
                return None
            Facc.append((q, top_sym))
            continue
        if eeqb(top_e, econst(1)):
            hsym = top_sym
            app = app[1:]
            break
        if not expr_ge(lo, top_e, 2):
            return None
        app = [(top_sym, eaddc(top_e, -1))] + app[1:]
        hsym = top_sym
        break
    if d == "R":
        c2 = (q, hsym, dep, app)
    else:
        c2 = (q, hsym, app, dep)
    return c2

# ---------------------------------------------------------------------------
# Canonical re-blocking (iv_reblock_side) + absorb (iv_absorb_side).
# ---------------------------------------------------------------------------

IV_BLK_LEN = 8
IV_BLK_MINCOV = 16
IV_REBLK_CELLS = 96

def iv_enc_side(buf):
    # canonical block factorization of a concrete cell buffer.
    # returns list of (sym, cnt) or None on a block-table miss / overflow.
    n = len(buf)
    out = []
    i = 0
    while i < n:
        bl = 0
        reps = 0
        for L in range(2, IV_BLK_LEN + 1):
            if i + 2 * L > n:
                continue
            if primitive_root_len(buf[i:i + L]) != L:
                continue
            r = 1
            while i + (r + 1) * L <= n and buf[i:i + L] == buf[i + r * L:i + (r + 1) * L]:
                r += 1
            if r >= 2 and r * L >= IV_BLK_MINCOV:
                bl = L
                reps = r
                break
        if len(out) >= 48:
            return None
        if bl >= 2:
            idv = blk_find(g_tbl, buf[i:i + bl])
            if idv is None or idv < NK:
                return None
            out.append((idv, reps))
            i += reps * bl
        else:
            sy = buf[i]
            r = 0
            while i < n and buf[i] == sy:
                r += 1
                i += 1
            out.append((sy, r))
    return out

def iv_reblock_side(lst):
    # re-encode the concrete single-cell near-prefix (mirror). in-place list.
    i = 0
    cells = 0
    vals = []
    while i < len(lst):
        v = eisconst(lst[i][1])
        if blk_len(g_tbl, lst[i][0]) != 1 or v is None or cells + v > IV_REBLK_CELLS:
            break
        vals.append(v)
        cells += v
        i += 1
    if i < 2 or cells < IV_BLK_MINCOV:
        return lst
    buf = []
    for r in range(i):
        buf += [lst[r][0]] * vals[r]
    enc = iv_enc_side(buf)
    if enc is None:
        return lst
    same = (len(enc) == i) and all(enc[r][0] == lst[r][0] and enc[r][1] == vals[r]
                                   for r in range(len(enc)))
    if same:
        return lst
    new = [(sy, econst(cn)) for (sy, cn) in enc] + lst[i:]
    # merge boundary
    m = len(enc)
    if 0 < m < len(new) and new[m - 1][0] == new[m][0]:
        merged = eadd(new[m - 1][1], new[m][1])
        new = new[:m - 1] + [(new[m - 1][0], merged)] + new[m + 1:]
    return new

def iv_absorb_side(lo, lst):
    # absorb completed block copies into the nearest block run (mirror).
    while True:
        i = -1
        for j in range(len(lst)):
            if blk_len(g_tbl, lst[j][0]) >= 2:
                i = j
                break
        if i <= 0:
            return lst
        bid = lst[i][0]
        L = blk_len(g_tbl, bid)
        cellsb = blk_cells(g_tbl, bid)
        take = []
        need = L - 1
        j = i - 1
        partial = False
        ok = True
        while need >= 0 and ok:
            if j < 0 or blk_len(g_tbl, lst[j][0]) != 1:
                ok = False
                break
            s = lst[j][0]
            t = 0
            while need - t >= 0 and cellsb[need - t] == s:
                t += 1
            if t == 0:
                ok = False
                break
            cv = eisconst(lst[j][1])
            if cv is not None and cv <= t:
                take.append(cv)
                need -= cv
                j -= 1
                continue
            if t >= need + 1 and (cv is not None or emin(lo, lst[j][1]) >= need + 2):
                take.append(need + 1)
                need = -1
                partial = True
            else:
                ok = False
        if not ok or need >= 0:
            return lst
        lst = list(lst)
        lst[i] = (lst[i][0], eadd(lst[i][1], econst(1)))
        nwhole = len(take) - (1 if partial else 0)
        if partial:
            idx = i - 1 - nwhole
            lst[idx] = (lst[idx][0], eaddc(lst[idx][1], -take[-1]))
        if nwhole > 0:
            del lst[i - nwhole:i]
            i -= nwhole
        if i > 0 and lst[i - 1][0] == lst[i][0]:
            lst[i - 1] = (lst[i - 1][0], eadd(lst[i - 1][1], lst[i][1]))
            del lst[i]
        # loop again

def iv_absorb(lo, reblock, c):
    st, hs, L, R = c
    if reblock:
        L = iv_reblock_side(L)
        R = iv_reblock_side(R)
    L = iv_absorb_side(lo, L)
    R = iv_absorb_side(lo, R)
    return (st, hs, L, R)

# ---------------------------------------------------------------------------
# Cell-stream end equality (iv_streams_eq): provable denoted-tape equality.
# ---------------------------------------------------------------------------

def _sumcells(xs):
    s = econst(0)
    for (sy, e) in xs:
        s = eaddmul(s, blk_len(g_tbl, sy), e)
    return s

def iv_streams_eq(lo, xa, xb):
    if not eeqb(_sumcells(xa), _sumcells(xb)):
        return False
    ia = ib = 0
    na, nb = len(xa), len(xb)
    rema = remb = econst(0)
    pha = phb = 0
    la = lb = False
    for _ in range(8192):
        if la and eisconst(rema) == 0:
            la = False; ia += 1
        if lb and eisconst(remb) == 0:
            lb = False; ib += 1
        if not la:
            if ia >= na:
                return ib >= nb and not lb
            rema = eaddmul(econst(0), blk_len(g_tbl, xa[ia][0]), xa[ia][1])
            pha = 0; la = True
            continue
        if not lb:
            if ib >= nb:
                return False
            remb = eaddmul(econst(0), blk_len(g_tbl, xb[ib][0]), xb[ib][1])
            phb = 0; lb = True
            continue
        wa = blk_cells(g_tbl, xa[ia][0]); La = len(wa)
        wb = blk_cells(g_tbl, xb[ib][0]); Lb = len(wb)
        win = La
        while win % Lb != 0:
            win += La
        agree = all(wa[(pha + x) % La] == wb[(phb + x) % Lb] for x in range(win))
        if not agree:
            if wa[pha] != wb[phb]:
                return False
            rema = eaddc(rema, -1); remb = eaddc(remb, -1)
            pha = (pha + 1) % La; phb = (phb + 1) % Lb
            continue
        if eeqb(rema, remb):
            la = lb = False; ia += 1; ib += 1
            continue
        ca = eisconst(rema); cb = eisconst(remb)
        if ca is not None and cb is not None:
            a_smaller = ca < cb
        else:
            diff = eaddmul(remb, -1, rema)
            a_smaller = cf_nonneg(diff[1]) and emin(lo, diff) >= 0
            if not a_smaller:
                diff2 = eaddmul(rema, -1, remb)
                b_smaller = cf_nonneg(diff2[1]) and emin(lo, diff2) >= 0
                if not b_smaller:
                    return False
        if a_smaller:
            if ca is None and La != Lb:
                return False
            res = (ca % Lb) if ca is not None else (La - pha % La) % La
            remb = eaddmul(remb, -1, rema)
            phb = (phb + res) % Lb
            la = False; ia += 1
        else:
            if cb is None and La != Lb:
                return False
            res = (cb % La) if cb is not None else (Lb - phb % Lb) % Lb
            rema = eaddmul(rema, -1, remb)
            pha = (pha + res) % La
            lb = False; ib += 1
    return False

# ---------------------------------------------------------------------------
# Rules (RRun: ('C',v)|('V',delta,lb); phase-1 same as K applier).
# ---------------------------------------------------------------------------

g_latt = True   # v7: honor the residue lattice of refined var runs

def _ref(rc):
    # (mod, res) for a var run: refined -> (mod, res); plain -> (1, 0).
    # g_latt=False collapses refined runs to plain (the "rulepfx alone" probe).
    if len(rc) == 5 and g_latt:
        return rc[3], rc[4]
    return 1, 0

def rc_lo(rc):
    # lo for the fresh variable w: count = mod*w+res >= lb  <=>  w >= (lb-res)/mod
    mod, res = _ref(rc)
    return (rc[2] - res) // mod

def rc_start(rc, vid):
    mod, res = _ref(rc)
    return eaddc(eaddmul(econst(0), mod, evar(vid)), res)      # mod*w + res

def rc_end(rc, vid):
    mod, res = _ref(rc)
    return eaddc(rc_start(rc, vid), rc[1])                      # mod*w + res + del

def rlbs(rr):    return [rc_lo(rc) for (_, rc) in rr if rc[0] == 'V']
def rule_lbs(r): return rlbs(r[2]) + rlbs(r[3])

def rstart(vid, rr):
    out = []
    for (s, rc) in rr:
        if rc[0] == 'C':
            out.append((s, econst(rc[1])))
        else:
            out.append((s, rc_start(rc, vid))); vid += 1
    return out

def rend(vid, rr):
    out = []
    for (s, rc) in rr:
        if rc[0] == 'C':
            out.append((s, econst(rc[1])))
        else:
            out.append((s, rc_end(rc, vid))); vid += 1
    return out

def rule_start_cfg(r):
    st, hs, L, R = r
    return (st, hs, rstart(0, L), rstart(len(rlbs(L)), R))

def rule_end_cfg(r):
    st, hs, L, R = r
    return (st, hs, rend(0, L), rend(len(rlbs(L)), R))

# --- the K applier (block-agnostic at the syntax level) ---

def collect_decs(rr, mr):
    out = []
    for (rsym, rc), (msym, e) in zip(rr, mr):
        if rc[0] == 'V' and rc[1] <= -1:
            out.append((rc[1], rc[2], e))
    return out

def surviveb(lo, Rex, t):
    delta, lb, e = t
    return expr_ge(lo, eaddmul(e, delta, Rex), lb + delta)

def find_binding(lo, decs):
    # Mirror of verify.c iv_rule_apply binding drain (lines ~3299-3348).
    # v6 rmdok (g_rmdok): the drain may leave a constant remainder
    # rmd = (e_j - lb_j) mod d_j; the binding run then ends at
    # lb_j + rmd - d_j (a constant, produced automatically by the uniform
    # appK_side because Rex uses floor division and the run coefficients
    # are all divisible by d_j).  Frozen versions require rmd == 0.
    for (delta, lb, e) in decs:
        dj = -delta
        if not (lb >= dj):
            continue
        r_lb = eaddc(e, -lb)                       # e - lb
        rmd = ((r_lb[0] % dj) + dj) % dj           # constant remainder
        if rmd != 0 and not g_rmdok:
            continue
        # coefficients must be exactly divisible by dj (c0 carries rmd);
        # this is what makes the binding-run end value a constant.
        if any(cc % dj != 0 for cc in r_lb[1]):
            continue
        Rex = eaddc(ediv(r_lb, dj), 1)             # (e-lb)//dj + 1
        # R >= 1  <=>  min(e) >= lb + rmd  (verify.c 3330-3331 guard)
        if not expr_ge(lo, Rex, 1):
            continue
        if all(surviveb(lo, Rex, t) for t in decs):
            return Rex
    return None

def appK_side(lo, Rex, rr, mr, prefix=False):
    # prefix: rr matches only the first len(rr) runs of mr; the rest of
    # mr (mr[len(rr):]) is spliced back untouched after applying.
    rest = []
    if prefix:
        if len(mr) < len(rr):
            return None
        rest = mr[len(rr):]
        mr = mr[:len(rr)]
    elif len(rr) != len(mr):
        return None
    out = []
    for (rsym, rc), (msym, e) in zip(rr, mr):
        if rsym != msym:
            return None
        if rc[0] == 'C':
            if not eeqb(e, econst(rc[1])):
                return None
            out.append((msym, e))
        else:
            delta, lb = rc[1], rc[2]
            mod, res = _ref(rc)
            if mod > 1:
                # v7 residue precondition (verify.c 3245-3254): the config
                # count must lie on the lattice -- residue res mod `mod` and
                # every coefficient divisible by `mod`.
                if ((e[0] % mod) + mod) % mod != res or any(cc % mod != 0 for cc in e[1]):
                    return None
            if not expr_ge(lo, e, lb):
                return None
            if delta >= 0:
                out.append((msym, eaddmul(e, delta, Rex)))
            else:
                ne = eaddmul(e, delta, Rex)
                if not expr_ge(lo, ne, lb + delta):
                    return None
                if eeqb(ne, econst(0)):
                    pass
                else:
                    out.append((msym, ne))
    return out + rest

def ruleK_apply(lo, r, c, pfx=(False, False)):
    st, hs, rL, rR = r
    cst, chs, cL, cR = c
    if st != cst or hs != chs:
        return None
    pL, pR = pfx
    if pL:
        if len(cL) < len(rL):
            return None
    elif len(rL) != len(cL):
        return None
    if pR:
        if len(cR) < len(rR):
            return None
    elif len(rR) != len(cR):
        return None
    # decs come only from the matched prefix portion
    mL = cL[:len(rL)] if pL else cL
    mR = cR[:len(rR)] if pR else cR
    decs = collect_decs(rL, mL) + collect_decs(rR, mR)
    if not decs:
        return None
    Rex = find_binding(lo, decs)
    if Rex is None:
        return None
    if not expr_ge(lo, Rex, 1):
        return None
    outL = appK_side(lo, Rex, rL, cL, prefix=pL)
    outR = appK_side(lo, Rex, rR, cR, prefix=pR)
    if outL is None or outR is None:
        return None
    mmL = merge_adj(lo, outL)
    mmR = merge_adj(lo, outR)
    if mmL is None or mmR is None:
        return None
    return (cst, chs, trim_blanks(mmL), trim_blanks(mmR))

def try_rulesK(lo, rules, c):
    for (r, F, pfx) in rules:
        c2 = ruleK_apply(lo, r, c, pfx)
        if c2 is not None:
            return (c2, F)
    return None

# ---------------------------------------------------------------------------
# Replay driver.
# ---------------------------------------------------------------------------

def replayK(tm, tbl, lo, rules, endt, fuel, stepped, hops, reblock, sent, c):
    F_acc = []
    for _ in range(fuel):
        if stepped and endt(c):
            return (c, F_acc)
        tr = try_rulesK(lo, rules, c)
        if tr is not None:
            c, Fr = tr
            F_acc = F_acc + Fr
            continue
        Facc = []
        c2 = eng_step(tm, tbl, lo, hops, sent, c, Facc)
        if c2 is None:
            return None
        c = iv_absorb(lo, reblock, c2)
        F_acc = F_acc + Facc
        stepped = True
    return None

def rule_check(tm, tbl, fuel, prior, r, pfx, hops, reblock):
    start = rule_start_cfg(r)
    end = rule_end_cfg(r)
    # during a prefix rule's OWN validation, its prefix sides are opaque
    sent = pfx
    res = replayK(tm, tbl, rule_lbs(r), prior,
                  (lambda cc: scfg_eqb(cc, end)), fuel, False, hops, reblock, sent, start)
    return None if res is None else res[1]

def check_rules(tm, tbl, fuel, rules_raw, hops, reblock):
    out = []
    for (r, pfx) in rules_raw:
        F = rule_check(tm, tbl, fuel, out, r, pfx, hops, reblock)
        if F is None:
            return None
        out.append((r, F, pfx))
    return out

# ---------------------------------------------------------------------------
# Template / certificate.
# ---------------------------------------------------------------------------

def tpl_start(rs):
    return [(s, (be, (al,))) for (s, al, be) in rs]

def tpl_want(a, b, rs):
    return [(s, (al * b + be, (al * a,))) for (s, al, be) in rs]

def bdside_const(K, rs):
    out = []
    for (s, e) in rs:
        c = blk_cells(g_tbl, s)
        out += c * cnt((lambda i: K), e)
    return out

def st_in(q, F):
    return any(t[0] == q for t in F)

def parse_cert(path):
    c = {"tplL": {}, "tplR": {}, "rules": {}, "blk": {}, "pfx": {}}
    for ln in open(path):
        p = ln.split()
        if not p:
            continue
        k = p[0]
        if k in ("anchor_step", "k0", "kmin", "meta_a", "meta_b",
                 "tpl_hsym", "nrules"):
            c[k] = int(p[1])
        elif k == "bbbcert":  c["ver"] = p[1]
        elif k == "machine":  c["machine"] = p[1]
        elif k == "type":     c["type"] = p[1]
        elif k == "tpl_state": c["tpl_state"] = ST[p[1]]
        elif k == "blk":
            c["blk"][int(p[1])] = [int(x) for x in p[2]]
        elif k == "tplrun":
            side, idx, sym, al, be = p[1], int(p[2]), int(p[3]), int(p[4]), int(p[5])
            c["tplL" if side == "L" else "tplR"][idx] = (sym, al, be)
        elif k == "rule":
            ridx = int(p[1])
            c["rules"][ridx] = {"st": ST[p[2]], "hs": int(p[3]), "L": {}, "R": {}}
        elif k == "rulepfx":
            # verify.c format: rulepfx RIDX pl pr  (pl,pr in {0,1}; a set
            # flag means that side is a near-head prefix match).
            ridx = int(p[1])
            c["pfx"][ridx] = [p[2] == "1", p[3] == "1"]
        elif k == "rulerun":
            ridx, side, idx, sym = int(p[1]), p[2], int(p[3]), int(p[4])
            r = c["rules"][ridx]
            if p[5] == "C":
                r[side][idx] = (sym, ('C', int(p[6])))
            else:
                r[side][idx] = (sym, ('V', int(p[6]), int(p[7])))
        elif k == "rulerunm":
            # v7: rulerunm IDX side ri sym del lb mod res  -- a var run
            # whose count is confined to the residue lattice mod*w + res.
            ridx, side, idx, sym = int(p[1]), p[2], int(p[3]), int(p[4])
            dl, lb, mo, re = int(p[5]), int(p[6]), int(p[7]), int(p[8])
            c["rules"][ridx][side][idx] = (sym, ('V', dl, lb, mo, re))
    return c

def cert_to_rule(rd):
    L = [rd["L"][i] for i in sorted(rd["L"])]
    R = [rd["R"][i] for i in sorted(rd["R"])]
    return (rd["st"], rd["hs"], L, R)

def truns(d):
    return [d[i] for i in sorted(d)]

g_tbl = {}   # active block table (set per cert)
g_rmdok = False   # v6+: binding drain may leave a constant remainder

def check_cert(path, fuel=FUEL, verbose=False, anchor=True, mech="all"):
    global g_tbl, g_rmdok, NK
    c = parse_cert(path)
    if c.get("type") != "irules":
        return (False, "not an irules cert")
    ver = c.get("ver")
    tm = parse_tm(c["machine"])
    NK = 2
    g_tbl = c["blk"]
    # verify.c: g->rmdok = (c->ver >= 6).  ver is the "bbbcert vN" token.
    try:
        g_rmdok = int(str(ver).lstrip("v")) >= 6
    except ValueError:
        g_rmdok = False
    # mech granularity: which of {block-hop, reblocking, streams-eq} are on
    do_hop = mech in ("hop", "hopstreams", "reblock", "streams", "all")
    do_reblock = mech in ("reblock", "streams", "all")
    do_streams = mech in ("hopstreams", "streams", "all")

    a, b = c["meta_a"], c["meta_b"]
    kmin, k0 = c["kmin"], c["k0"]
    if not (0 <= kmin <= k0 and 0 <= a and kmin <= a * kmin + b):
        return (False, "meta-map preconditions")
    TL, TR = truns(c["tplL"]), truns(c["tplR"])
    rules_raw = []
    for i in sorted(c["rules"]):
        pfx = tuple(c["pfx"].get(i, [False, False]))
        rules_raw.append((cert_to_rule(c["rules"][i]), pfx))

    rules_val = check_rules(tm, g_tbl, fuel, rules_raw, do_hop, do_reblock)
    if rules_val is None:
        return (False, "rule validation failed")

    tpl_cfg = (c["tpl_state"], c["tpl_hsym"], tpl_start(TL), tpl_start(TR))
    want_cfg = (c["tpl_state"], c["tpl_hsym"], tpl_want(a, b, TL), tpl_want(a, b, TR))

    def endt(cc):
        if scfg_eqb(cc, want_cfg):
            return True
        if do_streams and cc[0] == want_cfg[0] and cc[1] == want_cfg[1]:
            return (iv_streams_eq([kmin], cc[2], want_cfg[2]) and
                    iv_streams_eq([kmin], cc[3], want_cfg[3]))
        return False

    rep = replayK(tm, g_tbl, [kmin], rules_val, endt, fuel, False,
                  do_hop, do_reblock, (False, False), tpl_cfg)
    if rep is None:
        return (False, "meta replay did not close the cycle")
    _, F = rep

    if not anchor:
        return (True, "F=%s (anchor+coverage skipped)" % sorted(set(F)))

    q, Ls, h, Rs, visited = _sim(tm, c["anchor_step"], want_states=set())
    if q is None:
        return (False, "anchor sim halted")
    l, r = list(reversed(Ls)), list(reversed(Rs))
    if q != c["tpl_state"] or h != c["tpl_hsym"]:
        return (False, "anchor state/head mismatch")
    if not lpad_eqb(l, bdside_const(k0, tpl_start(TL))):
        return (False, "anchor left tape mismatch")
    if not lpad_eqb(r, bdside_const(k0, tpl_start(TR))):
        return (False, "anchor right tape mismatch")
    for q2 in ALL_ST:
        if q2 in visited and not st_in(q2, F):
            return (False, "state coverage: %d visited but not in F" % q2)
    return (True, "F=%s" % sorted(set(F)))

def lpad_eqb(a, b):
    n = max(len(a), len(b))
    for i in range(n):
        if (a[i] if i < len(a) else 0) != (b[i] if i < len(b) else 0):
            return False
    return True

# ---------------------------------------------------------------------------

def main():
    args = sys.argv[1:]
    anchor = True
    mech = "all"
    while args and args[0].startswith("--"):
        if args[0] == "--no-anchor":
            anchor = False; args = args[1:]
        elif args[0] == "--mech":
            mech = args[1]; args = args[2:]
        elif args[0] == "--dir":
            break
        else:
            break
    if args and args[0] == "--dir":
        paths = sorted(glob.glob(os.path.join(args[1], "*.cert")))
    else:
        paths = args
    npass = 0
    for p in paths:
        try:
            ok, msg = check_cert(p, anchor=anchor, mech=mech)
        except Exception as ex:
            ok, msg = False, "EXC %r" % ex
        name = os.path.basename(p).replace(".cert", "")
        print("%s %s\t%s" % ("PASS" if ok else "FAIL", name, msg if not ok else ""))
        npass += ok
    print("# %d/%d pass  (mech=%s)" % (npass, len(paths), mech), file=sys.stderr)

if __name__ == "__main__":
    main()
