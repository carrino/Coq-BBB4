#!/usr/bin/env python3
"""Python model of the multi-decrement (general step size) irules checker.

This is the executable design spec for the Coq checker
theories/Checkers/IRules/RulesK.v + MetaK.v: a faithful port of the
symbolic engine (Engine.v/RLE.v), the meta-cycle replay (Meta.v) and the
NEW general-delta rule applier (the K applier).  The v1 engine's rule
applier hardcodes a single -1 decrement (Rules.v find_dec: `d =? -1`);
the K applier supports any negative constant delta with the v3
binding-run semantics of ../BBB/docs/irules2.md
"Multi-decrement rules, general step sizes":

  application picks a *binding* run j (step d_j = -delta_j) deterministically
  -- first decrementing run, left side first, ascending index -- such that
  d_j divides e_j - lb_j coefficient-wise (so R = (e_j - lb_j)/d_j + 1 is an
  exact affine expression), lb_j >= d_j (the drained run lands on
  lb_j - d_j >= 0), and every other decrementing run survives R rounds.

Key soundness insight used by the Coq port: the applier need NOT trust the
division.  A candidate Rex is validated by, for every decrementing run i,
  expr_ge lo (e_i + delta_i*Rex) (lb_i + delta_i)
which forces the run to meet its lower bound at every one of the R rounds
(the minimum is the last round).  With that check the R-fold application is
sound for ANY Rex >= 1; the binding selection only has to PRODUCE the Rex
that makes the drained run land exactly (so the output matches the
template).  Output is uniform: every variable run steps to e + delta*Rex and
a decrementing run that reaches the constant 0 is dropped.

Usage:
  irulesk_prover.py CERT ...      check each cert, print PASS/FAIL
  irulesk_prover.py --dir DIR     check every *.cert in DIR
"""
import sys, os, glob

FUEL = 300000

# ---------------------------------------------------------------------------
# Affine expressions:  Expr = (c0, cf) with cf a tuple of coefficients.
# eval nu e = c0 + sum_i cf_i * nu_i.  Trailing zero coefficients are
# irrelevant (mirrors Expr.cf_eqb / cf_zeros).
# ---------------------------------------------------------------------------

def econst(v):            return (v, ())
def evar(i):              return (0, tuple(1 if j == i else 0 for j in range(i + 1)))
def e_c0(e):              return e[0]
def e_cf(e):              return e[1]

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
    # nu: callable index -> Z
    return e[0] + sum(c * nu(i) for i, c in enumerate(e[1]))

def _lo_nu(lo):
    return lambda i: (lo[i] if i < len(lo) else 0)

def elo(lo, e):           return _eval(e, _lo_nu(lo))

def expr_ge(lo, e, need):
    return cf_nonneg(e[1]) and need <= elo(lo, e)

def cnt(nu, e):           return max(0, _eval(e, nu))

def ediv(e, d):
    # untrusted integer division of each coefficient (validated by eeqb)
    return (e[0] // d, tuple(c // d for c in e[1]))

# ---------------------------------------------------------------------------
# TMs, symbols, states, directions.
#   St 0..3 = A..D ; Sym 0/1 ; Dir 'L'/'R'.
#   tm[(q, s)] = (write, dir, next) or None.
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

# ---------------------------------------------------------------------------
# Concrete tape (CTape.v): ctape = (left, head, right), nearest cell first.
# ---------------------------------------------------------------------------

def chd(l):  return l[0] if l else 0
def ctl(l):  return l[1:] if l else []

def ctape_move(d, w, ct):
    l, h, r = ct
    if d == "R":  return ([w] + l, chd(r), ctl(r))
    else:         return (ctl(l), chd(l), [w] + r)

def cstep(tm, c):
    q, ct = c
    _, h, _ = ct
    tr = tm[(q, h)]
    if tr is None:
        return None
    w, d, nx = tr
    return (nx, ctape_move(d, w, ct))

# Efficient concrete simulation for the anchor re-simulation and coverage.
# left/right are stacks whose TOP (last element) is the cell nearest the head,
# so a step is O(1) instead of the O(n) list-copy of cstep above.  The blank
# infinity beyond each end is implicit (pop of an empty stack yields S0).

def _sim(tm, n, want_states=None):
    # run n concrete steps from the blank start; return
    #   (q, left_stack, head, right_stack, visited_set)
    # or (None, ..., visited_set) if it halts.  visited_set collects the
    # states of configs at steps 0..n-1 when want_states is given.
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

def csteps(tm, n, c):
    # only ever called on the blank start c0 = (0, ([], 0, []))
    q, L, h, R, _ = _sim(tm, n)
    if q is None:
        return None
    return (q, (list(reversed(L)), h, list(reversed(R))))

def cvisits(tm, c, length, q):
    _, _, _, _, visited = _sim(tm, length, want_states=set())
    return q in visited

# ---------------------------------------------------------------------------
# Symbolic RLE (RLE.v).  SRun = (sym, Expr).  SCfg = (st, hs, L, R).
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
# The engine (Engine.v): one concrete step + chain hops.
# ---------------------------------------------------------------------------

def chainable(tm, q, s, mv):
    tr = tm[(q, s)]
    return tr is not None and tr[2] == q and tr[1] == mv

def eng_cross(tm, lo, q, mv, app, dep):
    # returns (app', dep', head_sym, F) or None
    if not app:
        if chainable(tm, q, 0, mv):
            return None
        return ([], dep, 0, [])
    s, e = app[0]
    rest = app[1:]
    if chainable(tm, q, s, mv):
        tr = tm[(q, s)]  # defined
        w = tr[0]
        if not expr_ge(lo, e, 1):
            return None
        dep2 = push(lo, w, e, dep)
        if dep2 is None:
            return None
        rec = eng_cross(tm, lo, q, mv, rest, dep2)
        if rec is None:
            return None
        app2, dep3, h, F = rec
        return (app2, dep3, h, [(q, s)] + F)
    if eeqb(e, econst(1)):
        return (rest, dep, s, [])
    if expr_ge(lo, e, 2):
        return ([(s, eaddc(e, -1))] + rest, dep, s, [])
    return None

def eng_step(tm, lo, c):
    st, hs, L, R = c
    tr = tm[(st, hs)]
    if tr is None:
        return None
    w, d, q1 = tr
    if d == "R":
        dep0, app0 = L, R
    else:
        dep0, app0 = R, L
    dep = push(lo, w, econst(1), dep0)
    if dep is None:
        return None
    cross = eng_cross(tm, lo, q1, d, app0, dep)
    if cross is None:
        return None
    app2, dep2, h, F = cross
    if d == "R":
        c2 = (q1, h, dep2, app2)
    else:
        c2 = (q1, h, app2, dep2)
    return (c2, [(st, hs)] + F)

# ---------------------------------------------------------------------------
# Rules.  RCnt = ('C', v) | ('V', delta, lb).  RRun = (sym, RCnt).
# Rule = (st, hs, L, R) with L, R lists of RRun.
# ---------------------------------------------------------------------------

def rlbs(rr):
    return [rc[2] for (_, rc) in rr if rc[0] == 'V']

def rule_lbs(r):
    return rlbs(r[2]) + rlbs(r[3])

def rstart(vid, rr):
    out = []
    for (s, rc) in rr:
        if rc[0] == 'C':
            out.append((s, econst(rc[1])))
        else:
            out.append((s, evar(vid)))
            vid += 1
    return out

def rend(vid, rr):
    out = []
    for (s, rc) in rr:
        if rc[0] == 'C':
            out.append((s, econst(rc[1])))
        else:
            out.append((s, eaddc(evar(vid), rc[1])))
            vid += 1
    return out

def rule_start_cfg(r):
    st, hs, L, R = r
    return (st, hs, rstart(0, L), rstart(len(rlbs(L)), R))

def rule_end_cfg(r):
    st, hs, L, R = r
    return (st, hs, rend(0, L), rend(len(rlbs(L)), R))

# ---------------------------------------------------------------------------
# The K applier (this is the whole point).
# ---------------------------------------------------------------------------

def collect_decs(rr, mr):
    # (delta, lb, e) for each decrementing var run, in scan order
    out = []
    for (rsym, rc), (msym, e) in zip(rr, mr):
        if rc[0] == 'V' and rc[1] <= -1:
            out.append((rc[1], rc[2], e))
    return out

def surviveb(lo, Rex, t):
    delta, lb, e = t
    return expr_ge(lo, eaddmul(e, delta, Rex), lb + delta)

def find_binding(lo, decs):
    # first decrementing run whose Rex divides exactly, is >= 1, and under
    # which every decrementing run survives R rounds.  Untrusted; appK_side
    # re-validates the survival for soundness.
    for (delta, lb, e) in decs:
        dj = -delta
        if not (lb >= dj):
            continue
        Rex = eaddc(ediv(eaddc(e, -lb), dj), 1)       # (e - lb)/dj + 1
        # dj*(Rex - 1) == e - lb   (exact division check)
        if not eeqb(eaddmul(econst(0), dj, eaddc(Rex, -1)), eaddc(e, -lb)):
            continue
        if not expr_ge(lo, Rex, 1):
            continue
        if all(surviveb(lo, Rex, t) for t in decs):
            return Rex
    return None

def appK_side(lo, Rex, rr, mr):
    if len(rr) != len(mr):
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
            if not expr_ge(lo, e, lb):
                return None
            if delta >= 0:
                out.append((msym, eaddmul(e, delta, Rex)))
            else:
                ne = eaddmul(e, delta, Rex)
                if not expr_ge(lo, ne, lb + delta):
                    return None
                if eeqb(ne, econst(0)):
                    pass  # drained run drops
                else:
                    out.append((msym, ne))
    return out

def ruleK_apply(lo, r, c):
    st, hs, rL, rR = r
    cst, chs, cL, cR = c
    if st != cst or hs != chs:
        return None
    if len(rL) != len(cL) or len(rR) != len(cR):
        return None
    decs = collect_decs(rL, cL) + collect_decs(rR, cR)
    if not decs:
        return None
    Rex = find_binding(lo, decs)
    if Rex is None:
        return None
    if not expr_ge(lo, Rex, 1):
        return None
    outL = appK_side(lo, Rex, rL, cL)
    outR = appK_side(lo, Rex, rR, cR)
    if outL is None or outR is None:
        return None
    mL = merge_adj(lo, outL)
    mR = merge_adj(lo, outR)
    if mL is None or mR is None:
        return None
    return (cst, chs, trim_blanks(mL), trim_blanks(mR))

def try_rulesK(lo, rules, c):
    for (r, F) in rules:
        c2 = ruleK_apply(lo, r, c)
        if c2 is not None:
            return (c2, F)
    return None

def replayK(tm, lo, rules, endt, fuel, stepped, c):
    F_acc = []
    for _ in range(fuel):
        if stepped and endt(c):
            return (c, F_acc)
        tr = try_rulesK(lo, rules, c)
        if tr is not None:
            c, Fr = tr
            F_acc = F_acc + Fr
            continue
        st = eng_step(tm, lo, c)
        if st is None:
            return None
        c, Fe = st
        F_acc = F_acc + Fe
        stepped = True
    return None

def rule_check(tm, fuel, r):
    start = rule_start_cfg(r)
    end = rule_end_cfg(r)
    res = replayK(tm, rule_lbs(r), [], (lambda cc: scfg_eqb(cc, end)),
                  fuel, False, start)
    return None if res is None else res[1]

def check_rules(tm, fuel, rules):
    out = []
    for r in rules:
        F = rule_check(tm, fuel, r)
        if F is None:
            return None
        out.append((r, F))
    return out

# ---------------------------------------------------------------------------
# Template / certificate.
# ---------------------------------------------------------------------------

def tpl_start(rs):
    return [(s, (be, (al,))) for (s, al, be) in rs]

def tpl_want(a, b, rs):
    return [(s, (al * b + be, (al * a,))) for (s, al, be) in rs]

def dside_const(K, rs):
    out = []
    for (s, e) in rs:
        out += [s] * cnt((lambda i: K), e)
    return out

def st_in(q, F):
    return any(t[0] == q for t in F)

def parse_cert(path):
    c = {"tplL": {}, "tplR": {}, "rules": {}, "rmeta": {}}
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
        elif k == "tplrun":
            side, idx, sym, al, be = p[1], int(p[2]), int(p[3]), int(p[4]), int(p[5])
            c["tplL" if side == "L" else "tplR"][idx] = (sym, al, be)
        elif k == "rule":
            ridx = int(p[1])
            c["rules"][ridx] = {"st": ST[p[2]], "hs": int(p[3]), "L": {}, "R": {}}
        elif k == "rulerun":
            ridx, side, idx, sym = int(p[1]), p[2], int(p[3]), int(p[4])
            r = c["rules"][ridx]
            if p[5] == "C":
                r[side][idx] = (sym, ('C', int(p[6])))
            else:
                r[side][idx] = (sym, ('V', int(p[6]), int(p[7])))
    return c

def cert_to_rule(rd):
    L = [rd["L"][i] for i in sorted(rd["L"])]
    R = [rd["R"][i] for i in sorted(rd["R"])]
    return (rd["st"], rd["hs"], L, R)

def truns(d):
    return [d[i] for i in sorted(d)]

def check_cert(path, fuel=FUEL, verbose=False, anchor=True):
    c = parse_cert(path)
    if c.get("ver") != "v3" or c.get("type") != "irules":
        return (False, "not a v3 irules cert")
    tm = parse_tm(c["machine"])
    a, b = c["meta_a"], c["meta_b"]
    kmin, k0 = c["kmin"], c["k0"]
    if not (0 <= kmin <= k0 and 0 <= a and kmin <= a * kmin + b):
        return (False, "meta-map preconditions")
    TL, TR = truns(c["tplL"]), truns(c["tplR"])
    rules = [cert_to_rule(c["rules"][i]) for i in sorted(c["rules"])]

    rules_val = check_rules(tm, fuel, rules)
    if rules_val is None:
        return (False, "rule validation failed")

    tpl_cfg = (c["tpl_state"], c["tpl_hsym"], tpl_start(TL), tpl_start(TR))
    want_cfg = (c["tpl_state"], c["tpl_hsym"], tpl_want(a, b, TL), tpl_want(a, b, TR))
    rep = replayK(tm, [kmin], rules_val, (lambda cc: scfg_eqb(cc, want_cfg)),
                  fuel, False, tpl_cfg)
    if rep is None:
        return (False, "meta replay did not close the cycle")
    _, F = rep

    if not anchor:
        return (True, "F=%s (anchor+coverage skipped)" % sorted(set(F)))

    # single concrete pass gives both the anchor config and the visited set
    q, Ls, h, Rs, visited = _sim(tm, c["anchor_step"], want_states=set())
    if q is None:
        return (False, "anchor sim halted")
    l, r = list(reversed(Ls)), list(reversed(Rs))
    if q != c["tpl_state"] or h != c["tpl_hsym"]:
        return (False, "anchor state/head mismatch")
    if not lpad_eqb(l, dside_const(k0, tpl_start(TL))):
        return (False, "anchor left tape mismatch")
    if not lpad_eqb(r, dside_const(k0, tpl_start(TR))):
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
    if args and args[0] == "--no-anchor":
        anchor = False
        args = args[1:]
    if args and args[0] == "--dir":
        paths = sorted(glob.glob(os.path.join(args[1], "*.cert")))
    else:
        paths = args
    npass = 0
    for p in paths:
        ok, msg = check_cert(p, anchor=anchor)
        name = os.path.basename(p).replace(".cert", "")
        print("%s %s\t%s" % ("PASS" if ok else "FAIL", name, msg if not ok else ""))
        npass += ok
    print("# %d/%d pass" % (npass, len(paths)), file=sys.stderr)

if __name__ == "__main__":
    main()
