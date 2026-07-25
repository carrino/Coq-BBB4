#!/usr/bin/env python3
"""UNTRUSTED auto-emitter for LEFT-growth comb-free interleaved-counter boards.

Per machine SPEC (a (4,2) transition string like 0RB---_0LC1RB_1LA1LD_1LC0RB):

  1. read the fingerprint (enc / growth / edge / p0) from fp_counters.jsonl;
  2. DERIVE the anchor  Cc p = (edge, (Jp p ++ [S0], S0, []))  and the six lap
     unit windows -- P1 prologue, RIP leftward carry ripple (cycL over the low
     set-bit pairs), STPI interior stop / STPO overflow stop off the deep-left
     tape edge, RET rightward return (cycR), FIN -- by a chained search over
     the comb-free skeleton anchored by the RAW step count of one lap: a
     candidate decomposition is accepted only if the symbolic chain lands on
     Cc(p+1) in exactly the raw number of steps, on an interior sample AND on
     an overflow sample;
  3. differentially validate the derived symbolic lap against the raw
     simulator for many p across BOTH cview branches, and check the derived
     units against the algebraic shape the Coq template's rewrites need;
  4. probe the bootstrap (least T with csteps tm T c0 = Cc p0) and derive the
     per-state visit witnesses (bounded anchor prefix / deep overflow route);
  5. string-emit theories/Machines/Counters/ILQ_<spec>.v, a clone of the
     hand-authored template Interleave_TGT.v with the per-machine table,
     states, step counts, windows and proof-script variant substituted, every
     global name suffixed by the sanitised spec so files never clash;
  6. run coqc -native-compiler no and Print Assumptions, and report pass/fail.

Everything here is UNTRUSTED: a wrong window or step count cannot mis-prove
anything, it simply fails to typecheck.  The Coq kernel re-checks every board.

Usage
  emit_interleave.py --list FILE            survey (derive+validate only)
  emit_interleave.py --emit SPEC...         emit + coqc + Print Assumptions
"""
import argparse
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

from executor import Exec, Wall  # noqa: E402

LAB = "ABCD"
# The anchor head symbol, set per machine by process() from the anchor
# search.  Wave-8 hard-coded S0 here and so could not derive any counter
# whose frontier cell is S1 (the majority of the quasihalting ones).
HEAD = 0
ST = ["StA", "StB", "StC", "StD"]
SYM = ["S0", "S1"]

SCRATCH = ('/tmp/claude-0/-home-user/722d7ed5-2c00-5fef-984d-cc3db7bde694/'
           'scratchpad')
DEFAULT_FP = os.path.join(SCRATCH, 'fp_counters.jsonl')
OUTDIR = os.path.join(REPO, 'theories', 'Machines', 'Counters')


# --------------------------------------------------------------- encodings ---
def Jp(m):
    """JpCounter.Jp: xH=[1]; xO q = 1::1::Jp q; xI q = 1::0::Jp q."""
    out = []
    while m > 1:
        out += [1, 1 - (m & 1)]
        m >>= 1
    return out + [1]


def Ip(m):
    """ILCounter.Ip: xH=[1]; xO q = 1::0::Ip q; xI q = 1::1::Ip q."""
    out = []
    while m > 1:
        out += [1, m & 1]
        m >>= 1
    return out + [1]


ENC = {'Jp': Jp, 'Ip': Ip}


def carry(m):
    """cview: (#low set bits j, overflow?)."""
    j = 0
    while (m >> j) & 1:
        j += 1
    return j, (m == (1 << j) - 1)


def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab


class DeriveError(Exception):
    pass


# --------------------------------------------------------------- the tail ---
# The anchor family is  Cc p = (edge, (enc p ++ tail, head, []))  with
#   enc  in {Ip, Jp}          -- ILCounter.Ip / JpCounter.Jp
#   head in {S0, S1}          -- the frontier cell under the head
#   tail an arbitrary short suffix READ OFF THE RUN.
# Wave-8's emitter fixed all three (Jp / S0 / "...++[S0]") and so could not see
# the counters whose anchor differs in any of them; the search below derives
# all three from the real run instead.

MAXTAIL = 4
_ETAB = {}


def enc_table(encname, tail, bound=1 << 14):
    """{tuple(enc m ++ tail): m} for one (encoding, tail) pair."""
    key = (encname, tuple(tail))
    d = _ETAB.get(key)
    if d is None:
        f = ENC[encname]
        d = {}
        for m in range(1, bound):
            d[tuple(f(m) + list(tail))] = m
        _ETAB[key] = d
    return d


def anchor_hits(spec, T=200000):
    """One real run; per (edge, head, enc, tail) key collect (step, value).

    A key fires when the FAR side is blank (after stripping trailing S0 --
    blank is not the same as empty) and the near side decodes exactly.
    """
    raw = Raw(spec)
    cfg = (0, [], 0, [])
    keys = [(e, tuple(t)) for e in ENC
            for tl in range(MAXTAIL + 1)
            for t in _tails(tl)]
    hits = {}
    for t in range(T):
        q, l, h, r = cfg
        if not strip0(r):
            near = tuple(strip0(l))
            if near:
                for (encname, tail) in keys:
                    m = enc_table(encname, tail).get(near)
                    if m is not None and m > 1:
                        hits.setdefault((LAB[q], h, encname, tail),
                                        []).append((t, m))
        cfg = raw.step(cfg)
        if cfg is None:
            break
    return hits


def _tails(n):
    for v in range(1 << n):
        yield [(v >> i) & 1 for i in range(n)]


def anchor_candidates(spec, edge_hint, minrun=8):
    """Ranked anchor families (edge, enc, head, tail, p0), best first.

    A family counts only when the machine reaches p+1 AFTER p (the run must
    ASCEND in time).  Without that check the same tape decodes under both Ip
    and Jp -- one ascending, one descending -- and sorting the value set makes
    the descending reading look just as consecutive.
    """
    hits = anchor_hits(spec)
    out = []
    for (edge, head, encname, tail), evs in hits.items():
        first = {}
        for t, m in evs:
            if m not in first:
                first[m] = t
        vs = sorted(first)
        run, bestrun, startv = 1, 0, None
        for i in range(1, len(vs)):
            asc = (vs[i] == vs[i - 1] + 1 and first[vs[i]] > first[vs[i - 1]])
            if asc:
                run += 1
            else:
                if run > bestrun:
                    bestrun, startv = run, vs[i - run]
                run = 1
        if run > bestrun:
            bestrun, startv = run, vs[len(vs) - run]
        if bestrun < minrun:
            continue
        out.append(((bestrun, edge == edge_hint, -len(tail)),
                    (edge, encname, head, list(tail), startv)))
    out.sort(key=lambda kv: kv[0], reverse=True)
    if not out:
        raise DeriveError("no anchor family (enc x head x tail) in the run")
    return [v for _, v in out]


def derive_tail(spec, edge_hint, maxt=MAXTAIL):
    """Back-compat single-best entry point."""
    return anchor_candidates(spec, edge_hint)[0]


# ------------------------------------------------------------ raw stepping ---
class Raw:
    def __init__(self, spec):
        self.tab = parse(spec)

    def step(self, cfg):
        q, l, h, r = cfg
        e = self.tab[(q, h)]
        if e is None:
            return None
        w, d, ns = e
        if d > 0:
            return (ns, [w] + l, r[0] if r else 0, r[1:])
        return (ns, l[1:], l[0] if l else 0, [w] + r)


def strip0(l):
    l = list(l)
    while l and l[-1] == 0:
        l.pop()
    return l


def nrm(cfg):
    q, l, h, r = cfg
    return (q, tuple(strip0(l)), h, tuple(strip0(r)))


def raw_lap(raw, E, encf, m, tail, maxsteps=400000):
    """Steps of one lap Cc(m) -> Cc(m+1) (match up to blank padding)."""
    cfg = (E, encf(m) + tail, HEAD, [])
    tgt = nrm((E, encf(m + 1) + tail, HEAD, []))
    for t in range(1, maxsteps):
        cfg = raw.step(cfg)
        if cfg is None:
            raise DeriveError("halts inside lap m=%d at t=%d" % (m, t))
        if nrm(cfg) == tgt:
            return t, cfg
    raise DeriveError("no lap closure from m=%d in %d steps" % (m, maxsteps))


# -------------------------------------------------- windowed-run primitives ---
def conc(ex, cfg, bl, br, n, lw, rw):
    """Run a walled window; returns (cfg', entry_window, exit_window)."""
    q, l, h, r = cfg
    lw = len(l) if lw is None else lw
    rw = len(r) if rw is None else rw
    if lw > len(l) or rw > len(r):
        raise Wall("window deeper than tape")
    out = ex.wsteps(bl, br, q, l[:lw], h, r[:rw], n)
    ent = (q, tuple(l[:lw]), h, tuple(r[:rw]))
    ext = (out[0], tuple(out[1]), out[2], tuple(out[3]))
    return (out[0], out[1] + l[lw:], out[2], out[3] + r[rw:]), ent, ext


def cyc_l(ex, cfg, ulen, rwlen, P, k):
    """cycL: unit (q,u,h,rw) -P-> (q,[],h,rw++w); applied k times."""
    q, l, h, r = cfg
    if k == 0:
        return cfg, None, None, None
    if ulen > len(l) or rwlen > len(r):
        raise Wall("cycL window deeper than tape")
    u, rw = l[:ulen], r[:rwlen]
    out = ex.wsteps(True, True, q, u, h, rw, P)
    if not (out[0] == q and out[2] == h and out[1] == [] and out[3][:rwlen] == rw):
        raise Wall("not a cycL unit")
    w = out[3][rwlen:]
    if l[:ulen * k] != u * k:
        raise Wall("left is not u^k")
    ent = (q, tuple(u), h, tuple(rw))
    ext = (q, (), h, tuple(out[3]))
    return (q, l[ulen * k:], h, rw + w * k + r[rwlen:]), ent, ext, w


def cyc_r(ex, cfg, ulen, P, k):
    """cycR: unit (q,[],h,u) -P-> (q,w,h,[]); applied k times."""
    q, l, h, r = cfg
    if k == 0:
        return cfg, None, None, None
    if ulen > len(r):
        raise Wall("cycR window deeper than tape")
    u = r[:ulen]
    out = ex.wsteps(True, True, q, [], h, u, P)
    if not (out[0] == q and out[2] == h and out[3] == []):
        raise Wall("not a cycR unit")
    w = out[1]
    if r[:ulen * k] != u * k:
        raise Wall("right is not u^k")
    ent = (q, (), h, tuple(u))
    ext = (q, tuple(w), h, ())
    return (q, w * k + l, h, r[ulen * k:]), ent, ext, w


# ------------------------------------------------------------- the skeleton --
MAXP1, MAXRIP, MAXSTP, MAXRET, MAXFIN = 14, 14, 20, 14, 10


def chain_int(ex, E, encf, m, j, s, tail):
    """Interior chain: P1 . RIP^j . STPI . RET^(2j) . FIN."""
    cfg = (E, encf(m) + tail, HEAD, [])
    steps = 0
    U = {}
    cfg, U['P1e'], U['P1x'] = conc(ex, cfg, True, True, s['nP1'], s['lwP1'], 0)
    steps += s['nP1']
    cfg, U['RIPe'], U['RIPx'], w = cyc_l(ex, cfg, s['ulen'], s['rwR'],
                                         s['nRIP'], j)
    steps += s['nRIP'] * j
    cfg, U['STPIe'], U['STPIx'] = conc(ex, cfg, True, True, s['nSTP'],
                                       s['lwS'], s['rwS'])
    steps += s['nSTP']
    m1 = len(U['P1x'][3])
    k = len(cfg[3]) - m1
    if k < 0 or k % s['uret']:
        raise Wall("return count does not divide the deposit")
    k //= s['uret']
    cfg, U['RETe'], U['RETx'], _ = cyc_r(ex, cfg, s['uret'], s['nRET'], k)
    steps += s['nRET'] * k
    cfg, U['FINe'], U['FINx'] = conc(ex, cfg, True, True, s['nFIN'], 0, m1)
    steps += s['nFIN']
    U['kret'] = k
    U['w'] = w
    return steps, cfg, U


def chain_ov(ex, E, encf, m, j, s, tail):
    """Overflow chain: P1 . RIP^(j-1) . STPO . RET^(|wo|+2(j-1)) . FIN."""
    cfg = (E, encf(m) + tail, HEAD, [])
    steps = 0
    U = {}
    cfg, U['P1e'], U['P1x'] = conc(ex, cfg, True, True, s['nP1'], s['lwP1'], 0)
    steps += s['nP1']
    cfg, _, _, _ = cyc_l(ex, cfg, s['ulen'], s['rwR'], s['nRIP'], j - 1)
    steps += s['nRIP'] * (j - 1)
    cfg, U['STPOe'], U['STPOx'] = conc(ex, cfg, False, True, s['nSTPO'],
                                       None, s['rwO'])
    steps += s['nSTPO']
    m1 = len(U['P1x'][3])
    k = len(cfg[3]) - m1
    if k < 0 or k % s['uret']:
        raise Wall("overflow return count does not divide")
    k //= s['uret']
    cfg, _, _, _ = cyc_r(ex, cfg, s['uret'], s['nRET'], k)
    steps += s['nRET'] * k
    cfg, _, _ = conc(ex, cfg, True, True, s['nFIN'], 0, m1)
    steps += s['nFIN']
    U['kret'] = k
    return steps, cfg, U


def derive(spec, edge, encname, p0, tail):
    """Search the comb-free skeleton; returns (skeleton, units)."""
    encf = ENC[encname]
    E = LAB.index(edge)
    raw = Raw(spec)
    ex = Exec(spec)

    JI, KO = 3, 4
    m_int = (1 << (JI + 1)) + (1 << JI) - 1      # JI trailing ones, then 0
    m_ov = (1 << KO) - 1                          # all ones (overflow)
    n_int, _ = raw_lap(raw, E, encf, m_int, tail)
    n_ov, _ = raw_lap(raw, E, encf, m_ov, tail)
    tgt_int = nrm((E, encf(m_int + 1) + tail, HEAD, []))
    tgt_ov = nrm((E, encf(m_ov + 1) + tail, HEAD, []))

    sols = []
    for nP1 in range(1, MAXP1 + 1):
        for lwP1 in range(1, 4):
            for nRIP in range(1, MAXRIP + 1):
                for ulen in (2,):
                    for rwR in range(0, 3):
                        s0 = dict(nP1=nP1, lwP1=lwP1, nRIP=nRIP, ulen=ulen,
                                  rwR=rwR)
                        try:
                            cfg = (E, encf(m_int) + tail, HEAD, [])
                            cfg, _, _ = conc(ex, cfg, True, True, nP1, lwP1, 0)
                            cyc_l(ex, cfg, ulen, rwR, nRIP, JI)
                        except (Wall, KeyError, IndexError):
                            continue
                        for nSTP in range(1, MAXSTP + 1):
                            for lwS in range(0, 5):
                                for rwS in range(0, 3):
                                    for uret in (1, 2):
                                        for nRET in range(1, MAXRET + 1):
                                            for nFIN in range(1, MAXFIN + 1):
                                                s = dict(s0, nSTP=nSTP,
                                                         lwS=lwS, rwS=rwS,
                                                         uret=uret, nRET=nRET,
                                                         nFIN=nFIN)
                                                if (nP1 + nRIP * JI + nSTP
                                                        + nFIN) >= n_int:
                                                    continue
                                                try:
                                                    st, cfg2, U = chain_int(
                                                        ex, E, encf, m_int,
                                                        JI, s, tail)
                                                except (Wall, KeyError,
                                                        IndexError):
                                                    continue
                                                if st != n_int:
                                                    continue
                                                if nrm(cfg2) != tgt_int:
                                                    continue
                                                sols.append((s, U))
                        if sols:
                            break
                    if sols:
                        break
                if sols:
                    break
            if sols:
                break
        if sols:
            break
    if not sols:
        raise DeriveError("no interior skeleton fits the raw lap")

    for (s, U) in sols:
        for nSTPO in range(1, MAXSTP + 2):
            for rwO in range(0, 3):
                s2 = dict(s, nSTPO=nSTPO, rwO=rwO)
                try:
                    st, cfg2, UO = chain_ov(ex, E, encf, m_ov, KO, s2, tail)
                except (Wall, KeyError, IndexError):
                    continue
                if st != n_ov or nrm(cfg2) != tgt_ov:
                    continue
                UU = dict(U)
                UU.update(UO)
                return s2, UU
    raise DeriveError("no overflow stop fits the raw lap")


# --------------------------------------------------------- symbolic replay ---
def sym_lap(ex, s, E, encf, m, tail):
    j, ov = carry(m)
    if ov:
        return chain_ov(ex, E, encf, m, j, s, tail)
    return chain_int(ex, E, encf, m, j, s, tail)


def validate(spec, s, U, edge, encname, tail, hi=160):
    """Differential: symbolic lap == raw lap, landing, counts, exactness."""
    encf = ENC[encname]
    E = LAB.index(edge)
    raw = Raw(spec)
    ex = Exec(spec)
    nwo = len(U['STPOx'][3])
    ms = sorted(set(list(range(1, hi + 1))
                    + [(1 << k) - 1 for k in range(1, 13)]
                    + [(1 << k) for k in range(1, 13)]
                    + [(1 << k) + (1 << (k - 3)) - 1 for k in range(4, 13)]
                    + [(1 << 12) + (1 << 9) - 1, (1 << 14) - 1]))
    exact_int, exact_ov, nchk = True, True, 0
    for m in ms:
        n_sym, cfg_sym, Um = sym_lap(ex, s, E, encf, m, tail)
        n_raw, _ = raw_lap(raw, E, encf, m, tail)
        tgt = (E, encf(m + 1) + tail, HEAD, [])
        if n_sym != n_raw:
            raise DeriveError("m=%d: sym %d != raw %d steps" % (m, n_sym, n_raw))
        if nrm(cfg_sym) != nrm(tgt):
            raise DeriveError("m=%d: sym config %s != Cc(m+1)"
                              % (m, nrm(cfg_sym)))
        j, ov = carry(m)
        want = (nwo + 2 * (j - 1)) if ov else 2 * j
        if Um['kret'] != want:
            raise DeriveError("m=%d: return count %d != %d (%s)"
                              % (m, Um['kret'], want,
                                 "overflow" if ov else "interior"))
        ok = (list(cfg_sym[1]) == list(tgt[1])
              and list(cfg_sym[3]) == list(tgt[3]))
        if ov:
            exact_ov &= ok
        else:
            exact_int &= ok
        nchk += 1
    return exact_int, exact_ov, nchk


# ------------------------------------------------------- shape requirements --
def shape_check(s, U, encname, edge, tail):
    """The emitted Coq proof script needs exactly these symbol shapes."""
    msgs = []
    if encname != 'Jp':
        return ["encoding %s unsupported (this emitter is Jp-only)" % encname]
    E = LAB.index(edge)
    P1e, P1x = U['P1e'], U['P1x']
    Re, Rx = U['RIPe'], U['RIPx']
    Se, Sx = U['STPIe'], U['STPIx']
    Te, Tx = U['RETe'], U['RETx']
    Fe, Fx = U['FINe'], U['FINx']
    Oe, Ox = U['STPOe'], U['STPOx']
    if P1e[1] != (1,) or P1e[3] != () or P1x[1] != ():
        msgs.append("P1 %s -> %s is not [S1]|[] -> []" % (P1e, P1x))
    if P1x[3] != (0,):
        msgs.append("P1 deposit %s is not [S0]" % (P1x[3],))
    if Re[1] != (0, 1) or Re[3] != ():
        msgs.append("RIP entry %s is not ([S0;S1],[])" % (Re,))
    if len(Rx[3]) != 2 or Rx[3][0] != Rx[3][1]:
        msgs.append("RIP deposit %s is not a doubled cell" % (Rx[3],))
    if Se[1] != (1,) or Se[3] != () or Sx[1] != (0,) or Sx[3] != ():
        msgs.append("STPI %s -> %s is not [S1]|[] -> [S0]|[]" % (Se, Sx))
    if s['uret'] != 1:
        msgs.append("return unit consumes %d cells (need 1)" % s['uret'])
    if Te[3] != (Rx[3][0],) or Tx[1] != (1,) or Tx[3] != ():
        msgs.append("RET %s -> %s does not consume the RIP cell into [S1]"
                    % (Te, Tx))
    if Fe[1] != () or Fe[3] != (0,):
        msgs.append("FIN entry %s is not ([],[S0])" % (Fe,))
    if Fx[1] != (1,) or Fx[3] != () or Fx[2] != 0 or Fx[0] != E:
        msgs.append("FIN exit %s is not the anchor (edge,[S1],S0,[])" % (Fx,))
    if Oe[1] != tuple(tail) or Oe[3] != ():
        msgs.append("STPO entry %s is not (tail %s, [])" % (Oe, tail))
    cell = Rx[3][0] if len(Rx[3]) == 2 else None
    if any(c != cell for c in Ox[3]):
        msgs.append("STPO deposit %s is not a run of the RIP cell %s"
                    % (Ox[3], Rx[3]))
    lo = ov_split(Ox[1], tail)
    if lo is None:
        msgs.append("STPO exit left %s is not S1^a ++ (tail %s, maybe short one "
                    "blank)" % (Ox[1], tail))
    elif 1 + len(Ox[3]) + lo[0] != 3:
        msgs.append("STPO leaves 1+|dep|+|ones| = %d cells, need 3"
                    % (1 + len(Ox[3]) + lo[0]))
    # frame agreement
    if (Re[0], Re[2]) != (P1x[0], P1x[2]):
        msgs.append("P1 exit frame != ripple frame")
    if (Se[0], Se[2]) != (Re[0], Re[2]):
        msgs.append("stop entry frame != ripple frame")
    if (Oe[0], Oe[2]) != (Re[0], Re[2]):
        msgs.append("overflow stop entry frame != ripple frame")
    if (Te[0], Te[2]) != (Sx[0], Sx[2]):
        msgs.append("return frame != interior stop exit")
    if (Te[0], Te[2]) != (Ox[0], Ox[2]):
        msgs.append("return frame != overflow stop exit")
    if (Fe[0], Fe[2]) != (Tx[0], Tx[2]):
        msgs.append("FIN entry frame != return frame")
    return msgs


def ov_split(lo, tail):
    """Split the overflow stop's exit-left window as S1^a ++ TL, where TL is
    the anchor tail (exact landing) or the tail minus its trailing blank (the
    reached anchor is then short one blank: lift-equal only)."""
    lo = list(lo)
    for tl in (list(tail), list(tail[:-1])):
        n = len(lo) - len(tl)
        if n < 0:
            continue
        if tl and lo[n:] != tl:
            continue
        if any(c != 1 for c in lo[:n]):
            continue
        return n, tl
    return None


# ------------------------------------------------------------------- boot ----
def boot_probe(spec, edge, encname, p0, tail, maxT=20000):
    encf = ENC[encname]
    E = LAB.index(edge)
    raw = Raw(spec)
    tgt = nrm((E, encf(p0) + tail, HEAD, []))
    cfg = (0, [], 0, [])
    for t in range(maxT):
        if nrm(cfg) == tgt:
            return t
        cfg = raw.step(cfg)
        if cfg is None:
            raise DeriveError("halts during bootstrap at t=%d" % t)
    raise DeriveError("no bootstrap to Cc(%d) in %d steps" % (p0, maxT))


# ------------------------------------------------------------------ visits ---
OPQ = 'L'          # opaque left tail
XCELL = 'X'        # the free second cell of the anchor


def sym_prefix(spec, E, kmax=3):
    """Run the anchor prefix (E,([S1;X] ++ L, S0, R)) with X free.

    Returns a list indexed by step of (state, left tokens, head, right tokens)
    while no read touches X or the opaque tail; stops early otherwise."""
    tab = parse(spec)
    q, l, h, r = E, [1, XCELL], HEAD, []
    out = [(q, list(l), h, list(r))]
    for _ in range(kmax):
        if h in (XCELL,):
            break
        e = tab[(q, h)]
        if e is None:
            break
        w, d, ns = e
        if d > 0:
            if not r:
                break                       # would pop the opaque right tail
            q, l, h, r = ns, [w] + l, r[0], r[1:]
        else:
            if not l:
                break                       # would pop the opaque left tail
            q, l, h, r = ns, l[1:], l[0], [w] + r
        out.append((q, list(l), h, list(r)))
    return out


def concrete_prefix(spec, E, left, kmax=12):
    """States along the run from (E,(left,S0,[])) with a real tape."""
    raw = Raw(spec)
    cfg = (E, list(left), HEAD, [])
    out = [cfg[0]]
    for _ in range(kmax):
        cfg = raw.step(cfg)
        if cfg is None:
            break
        out.append(cfg[0])
    return out


def deep_probe(spec, s, U, E, encname, tail, kmax=None):
    """Offsets of each state inside the overflow stop (uniformly in j)."""
    encf = ENC[encname]
    ex = Exec(spec)
    raw = Raw(spec)
    kmax = s['nSTPO'] if kmax is None else kmax
    seenall = {}
    for k in (2, 3, 4, 5, 6):
        m = (1 << k) - 1
        cfg = (E, encf(m) + tail, HEAD, [])
        cfg, _, _ = conc(ex, cfg, True, True, s['nP1'], s['lwP1'], 0)
        cfg, _, _, _ = cyc_l(ex, cfg, s['ulen'], s['rwR'], s['nRIP'], k - 1)
        seen = {}
        c = cfg
        for t in range(0, kmax + 1):
            seen.setdefault(c[0], t)
            if t == kmax:
                break
            c = raw.step(c)
            if c is None:
                break
        for q, t in seen.items():
            seenall.setdefault(q, set()).add(t)
    return {q: min(v) for q, v in seenall.items() if len(v) == 1}


def deep_unit(spec, s, U, E, encname, tail, k):
    """The k-step prefix of the overflow stop, as a windowed unit."""
    ex = Exec(spec)
    encf = ENC[encname]
    m = (1 << 5) - 1
    cfg = (E, encf(m) + tail, HEAD, [])
    cfg, _, _ = conc(ex, cfg, True, True, s['nP1'], s['lwP1'], 0)
    cfg, _, _, _ = cyc_l(ex, cfg, s['ulen'], s['rwR'], s['nRIP'], 4)
    q, l, h, r = cfg
    assert l == list(tail), "overflow stop entry left %s != tail %s" % (l, tail)
    out = ex.wsteps(False, True, q, list(tail), h, [], k)
    return ((q, tuple(tail), h, ()),
            (out[0], tuple(out[1]), out[2], tuple(out[3])))


def visit_plan(spec, s, U, E, encname, tail):
    """Per-state witness plan.  Raises DeriveError if a state is unreachable
    by any supported route."""
    pre = sym_prefix(spec, E, kmax=3)
    plan = {}
    deep = deep_probe(spec, s, U, E, encname, tail)
    for q in range(4):
        # (a) bounded anchor prefix, uniform in p
        k = None
        for i, st in enumerate(pre):
            if st[0] == q:
                k = i
                break
        if k is not None:
            if k == 0:
                plan[q] = ('anchor',)
                continue
            depth = 2 if any(XCELL in (list(pre[i][1]) + [pre[i][2]]
                                       + list(pre[i][3]))
                             for i in range(1, k + 1)) else 1
            # the p = 1 anchor ([S1;S0]) is not covered by the free-cell lemma
            c1 = concrete_prefix(spec, E, [1] + list(tail))
            if q not in c1:
                raise DeriveError("state %s not reached from the p=1 anchor"
                                  % LAB[q])
            k1 = c1.index(q)
            plan[q] = ('prefix', k, depth, pre[k], k1)
            continue
        # (b) deep route through the overflow stop
        if q in deep:
            plan[q] = ('deep', deep[q], deep_unit(spec, s, U, E, encname,
                                                  tail, deep[q]))
            continue
        raise DeriveError("no visit witness for state %s" % LAB[q])
    return plan


# -------------------------------------------------------------- Coq syntax ---
def csym(x):
    return SYM[x] if isinstance(x, int) else 'x'


def clist(xs):
    return "[" + ";".join(csym(x) for x in xs) + "]"


def ccons(xs, tail):
    """Render xs ++ tail in cons form."""
    if not xs:
        return tail
    return "".join("%s::" % csym(x) for x in xs) + tail


def capp(xs, tail):
    if not xs:
        return tail
    return "%s ++ %s" % (clist(xs), tail)


def cwin(c):
    q, l, h, r = c
    return "(%s,(%s,%s,%s))" % (ST[q], clist(l), csym(h), clist(r))


def coq_table(spec):
    tab = parse(spec)
    rows = []
    for si in range(4):
        cells = []
        for yi in range(2):
            e = tab[(si, yi)]
            if e is None:
                cells.append("| %s, %s => None" % (ST[si], SYM[yi]))
            else:
                w, d, ns = e
                cells.append("| %s, %s => mk %s %s %s"
                             % (ST[si], SYM[yi], SYM[w],
                                "DR" if d > 0 else "DL", ST[ns]))
        rows.append("  " + " ".join(cells))
    return "\n".join(rows)


def mach_id(spec):
    return re.sub(r'[^0-9A-Za-z]', '_', spec)


# ------------------------------------------------------------- Coq emission --
HEAD = r'''(** * ILQ_@ID@: comb-free interleaved binary counter, machine
    @SPEC@.

    Auto-emitted by tools/counters/emit_interleave.py (UNTRUSTED emitter; the
    Coq kernel re-checks everything below).  Left-growth counter under the
    complemented interleave encoding [Jp] (JpCounter.v).  The anchor is

      Cc p = (@EDGE@, (Jp p ++ @TAIL@, S0, []))

    -- the counter on the LEFT list nearest-first, a blank head at the fixed
    right frontier, empty right side, no comb.  One lap Cc p -> Cc (p+1) is a
    single sweep:

      P1   prologue: read the frontier, turn left into the counter;
      RIP  leftward carry ripple over the low set-bit pairs (cycL, @NRIP@
           steps per pair, j pairs where cview p = (j, _));
      STPI interior stop -- flip the first clear pair (cview p = (j,Some q));
      STPO overflow stop off the DEEP-LEFT tape edge (cview p = (S j,None)),
           growing the counter by a fresh most-significant pair;
      RET  rightward return over the deposited cells (cycR);
      FIN  close at the frontier.

    All six windows were derived by simulation and the whole decomposition was
    differentially validated against the raw simulator on both cview branches
    for p = 1..160 plus sparse p up to 2^14 (step counts AND configurations).
    Axiom footprint: [functional_extensionality_dep] (via CTape.lift). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH MonoCounter ILCounter JpCounter.
From BBB4.Census Require Import TNF_QH.
Import ListNotations.

Definition mk_@ID@ (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_@ID@.

(** @SPEC@ *)
Definition tm_@ID@ : TM := fun q s => match q, s with
@TABLE@ end.
Local Notation tm := tm_@ID@.

Definition Cc_@ID@ (p : positive) : cconf := (@EDGE@, (Jp p ++ @TAIL@, S0, [])).
Local Notation Cc := Cc_@ID@.

(** ** The six lap unit windows (each closed by [reflexivity]) *)
Lemma U_P1_@ID@ : wsteps true true tm @NP1@ @P1E@ = Some @P1X@. Proof. reflexivity. Qed.
Lemma U_RIP_@ID@ : wsteps true true tm @NRIP@ @RIPE@ = Some @RIPX@. Proof. reflexivity. Qed.
Lemma U_STPI_@ID@ : wsteps true true tm @NSTP@ @STPIE@ = Some @STPIX@. Proof. reflexivity. Qed.
Lemma U_STPO_@ID@ : wsteps false true tm @NSTPO@ @STPOE@ = Some @STPOX@. Proof. reflexivity. Qed.
Lemma U_RET_@ID@ : wsteps true true tm @NRET@ @RETE@ = Some @RETX@. Proof. reflexivity. Qed.
Lemma U_FIN_@ID@ : wsteps true true tm @NFIN@ @FINE@ = Some @FINX@. Proof. reflexivity. Qed.

(** ** Transported phases (framing = each unit's bl/br) *)
Lemma phP1_@ID@ : forall L R, csteps tm @NP1@ (@EDGE@,(S1::L,S0,R)) = Some (@QR@,(L,@HR@,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_P1_@ID@). Qed.
Lemma phRIP_@ID@ : forall k L R, csteps tm (@NRIP@*k) (@QR@,(rep [S0;S1] k ++ L,@HR@,R)) = Some (@QR@,(L,@HR@,rep @WDEP@ k ++ R)).
Proof. intros. pose proof (cycL _ _ _ _ _ _ _ U_RIP_@ID@ k L R) as H; cbn [app] in H; exact H. Qed.
Lemma phSTPI_@ID@ : forall L R, csteps tm @NSTP@ (@QR@,(S1::L,@HR@,R)) = Some (@QT@,(S0::L,@HT@,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STPI_@ID@). Qed.
Lemma phSTPO_@ID@ : forall R, csteps tm @NSTPO@ (@QR@,(@TAIL@,@HR@,R)) = Some (@QT@,(@LO@,@HT@,@WOCONS@R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPO_@ID@). Qed.
Lemma phRET_@ID@ : forall k L R, csteps tm (@NRET@*k) (@QT@,(L,@HT@,rep @WCELL@ k ++ R)) = Some (@QT@,(rep [S1] k ++ L,@HT@,R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U_RET_@ID@ k L R). Qed.
Lemma phFIN_@ID@ : forall L R, csteps tm @NFIN@ (@QT@,(L,@HT@,S0::R)) = Some (@EDGE@,(S1::L,S0,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FIN_@ID@). Qed.

(** ** The lap *)

(** Interior branch: EXACT (the next anchor on the nose) -- the deep-visit
    induction below chains on this equality. *)
Lemma lap_int_@ID@ : forall p j q0, cview p = (j, Some q0) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intros p j q0 Ecv. unfold Cc_@ID@.
  destruct (cview_some_J p j q0 Ecv) as (HJp & HJs).
  do 2 eexists. split; [|split].
  + rewrite HJp, <- app_assoc.
    change (rep [S1;S0] j ++ (S1 :: S1 :: Jp q0) ++ @TAIL@)
      with (rep [S1;S0] j ++ [S1] ++ (S1 :: Jp q0 ++ @TAIL@)).
    rewrite app_assoc, pair_rot.
    eapply csteps_chain. { apply phP1_@ID@. }
    eapply csteps_chain. { apply phRIP_@ID@. }
    eapply csteps_chain. { apply phSTPI_@ID@. }
    rewrite rep_dbl.
    eapply csteps_chain. { apply (phRET_@ID@ (2*j)). }
    apply phFIN_@ID@.
  + rewrite HJs, rep_dbl. cbn [Nat.mul]. rewrite rep_slide, <- !app_assoc. reflexivity.
  + lia.
Qed.
'''

# --- overflow closing (generic): the stop may restore, drop or pre-deposit
#     cells at the deep-left edge; the reached anchor is then equal to the
#     next anchor up to at most one trailing blank, i.e. lift-equal.
OV_GEN = r'''
(** Fold the next anchor's counter into a single run of ones. *)
Lemma fold_tgt_@ID@ : forall k, (rep [S1;S1] k ++ [S1]) ++ @TAIL@ = rep [S1] (S (2*k)) ++ @TAIL@.
Proof. intro k. rewrite rep_dbl, rep_shift. reflexivity. Qed.

(** The lap's last step deposits one more [S1], and the overflow stop leaves
    [@LO@] at the deep edge: fold both into the run of ones. *)
Lemma fold_ov_@ID@ : forall k, S1 :: rep [S1] k ++ @LO@ = rep [S1] (S k + @AONES@) ++ @TL@.
Proof. intro k. rewrite rep_add, <- !app_assoc. reflexivity. Qed.

@LIFTLB@Lemma close_@ID@ : forall a b q h, a = b ->
  lift (q,(rep [S1] a ++ @TL@, h, [])) = lift (q,(rep [S1] b ++ @TAIL@, h, [])).
Proof. @CLOSETAC@ Qed.

Lemma lap_@ID@ : forall p, exists n c', csteps tm n (Cc p) = Some c' /\
  lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv.
  destruct oq as [q0|].
  - destruct (lap_int_@ID@ p j q0 Ecv) as (n & c' & H1 & H2 & H3).
    exists n, c'. split; [exact H1|split; [rewrite H2; reflexivity|exact H3]].
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_J p j' Ecv) as (HJp & HJs).
    unfold Cc_@ID@. do 2 eexists. split; [|split].
    + rewrite HJp, pair_rot.
      eapply csteps_chain. { apply phP1_@ID@. }
      eapply csteps_chain. { apply phRIP_@ID@. }
      eapply csteps_chain. { apply phSTPO_@ID@. }
      rewrite rep_dbl.
      @KOVCHANGE@eapply csteps_chain. { apply (phRET_@ID@ (@KOV@)). }
      apply phFIN_@ID@.
    + rewrite HJs, fold_tgt_@ID@, fold_ov_@ID@.
      apply close_@ID@. lia.
    + lia.
Qed.
'''

BOOT = r'''
Lemma boot_@ID@ : exists t0, stepn tm t0 InitES = Some (lift (Cc @P0@)).
Proof.
  exists @BOOT@.
  assert (H : match csteps tm @BOOT@ c0 with Some c => ceqb c (Cc @P0@) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm @BOOT@ c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.
'''

DEEP = r'''
(** The deep state @QDEEP@ is only visited inside the OVERFLOW stop; reach an
    all-ones counter by well-founded induction on [tovf] (which strictly
    decreases along the interior laps) and then run the stop prefix. *)
Lemma U_VD@N@_@ID@ : wsteps false true tm @KDEEP@ @VDE@ = Some @VDX@. Proof. reflexivity. Qed.
Lemma phVD@N@_@ID@ : forall R, csteps tm @KDEEP@ (@QR@,(@TAIL@,@HR@,R)) = Some (@QDEEP@,(@VDL@,@VDH@,@VDRCONS@R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_VD@N@_@ID@). Qed.

Lemma vis_deep@N@_@ID@ : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = @QDEEP@.
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.
  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj). rewrite Hjj in Ecv; discriminate. }
    destruct (lap_int_@ID@ p j q0 Ecv) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ p)) (ltac:(rewrite tovf_succ by lia; lia)) (Pos.succ p) eq_refl) as (k & c & Hk & Hq).
    exists (n + k), c. rewrite csteps_add, Hrun. exact (conj Hk Hq).
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_J p j' Ecv) as (HJp & _).
    unfold Cc_@ID@. eexists. eexists. split.
    * rewrite HJp, pair_rot.
      eapply csteps_chain. { apply phP1_@ID@. }
      eapply csteps_chain. { apply phRIP_@ID@. }
      apply phVD@N@_@ID@.
    * reflexivity.
Qed.
'''

TAIL = r'''
Lemma untgt_@ID@ : forall q b tr, tm q b = Some tr -> t_next tr <> StA.
Proof. intros q b tr H. destruct q, b; simpl in H; try discriminate;
       injection H as <-; simpl; discriminate. Qed.

Theorem iqh_@ID@ : NonHalt tm /\ QHBound 1 tm /\ QuasiHaltsSt tm.
Proof.
  apply (glue_qh tm Cc @P0@).
  - exact boot_@ID@.
  - intros p _. apply lap_@ID@.
  - intros p q _ _. apply vis_@ID@.
  - exact untgt_@ID@.
Qed.

Theorem nonhalt_@ID@ : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_@ID@. Qed.
'''


def emit_source(spec, r, s, U, plan, boot, tail, p0):
    ID = mach_id(spec)
    E = LAB.index(r['edge'])
    P1e, P1x = U['P1e'], U['P1x']
    Re, Rx = U['RIPe'], U['RIPx']
    Se, Sx = U['STPIe'], U['STPIx']
    Te, Tx = U['RETe'], U['RETx']
    Fe, Fx = U['FINe'], U['FINx']
    Oe, Ox = U['STPOe'], U['STPOx']
    sub = {
        '@ID@': ID, '@SPEC@': spec, '@EDGE@': ST[E], '@TABLE@': coq_table(spec),
        '@NP1@': str(s['nP1']), '@NRIP@': str(s['nRIP']),
        '@NSTP@': str(s['nSTP']), '@NSTPO@': str(s['nSTPO']),
        '@NRET@': str(s['nRET']), '@NFIN@': str(s['nFIN']),
        '@P1E@': cwin(P1e), '@P1X@': cwin(P1x),
        '@RIPE@': cwin(Re), '@RIPX@': cwin(Rx),
        '@STPIE@': cwin(Se), '@STPIX@': cwin(Sx),
        '@STPOE@': cwin(Oe), '@STPOX@': cwin(Ox),
        '@RETE@': cwin(Te), '@RETX@': cwin(Tx),
        '@FINE@': cwin(Fe), '@FINX@': cwin(Fx),
        '@QR@': ST[Re[0]], '@HR@': csym(Re[2]),
        '@QT@': ST[Te[0]], '@HT@': csym(Te[2]),
        '@WDEP@': clist(Rx[3]), '@WCELL@': clist(Te[3]),
        '@WOCONS@': ccons(Ox[3], ''), '@WDEPCONS@': ccons(Rx[3], ''),
        '@P0@': str(p0), '@BOOT@': str(boot),
    }
    aones, tl = ov_split(Ox[1], tail)
    nwo = len(Ox[3])
    kov = "2*j'"
    for _ in range(nwo):
        kov = "S (%s)" % kov
    sub['@TAIL@'] = clist(tail)
    sub['@TL@'] = clist(tl)
    sub['@LO@'] = clist(Ox[1])
    sub['@KOV@'] = kov
    sub['@AONES@'] = str(aones)
    if list(tl) == list(tail):
        sub['@LIFTLB@'] = ""
        sub['@CLOSETAC@'] = "intros a b q h ->. reflexivity."
    else:
        sub['@LIFTLB@'] = (
            "Lemma lift_l_blank_@ID@ : forall q l h r, "
            "lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).\n"
            "Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.\n\n")
        sub['@CLOSETAC@'] = (
            "intros a b q h ->.\n"
            "  replace (rep [S1] b ++ @TAIL@) with ((rep [S1] b ++ @TL@) ++ [S0])\n"
            "    by (rewrite <- app_assoc; reflexivity).\n"
            "  rewrite lift_l_blank_@ID@. reflexivity.")
    sub['@KOVCHANGE@'] = ("" if nwo == 0 else
                          "change (%srep %s (2*j') ++ [S0]) with (rep %s (%s) ++ [S0]).\n      "
                          % (ccons(Ox[3], ''), clist(Te[3]), clist(Te[3]), kov))

    def fill(t, extra=None):
        d = dict(sub)
        if extra:
            d.update(extra)
        for k, v in sorted(d.items(), key=lambda kv: -len(kv[0])):
            t = t.replace(k, v)
        return t

    src = fill(HEAD)
    src += fill(OV_GEN)
    src += fill(BOOT)
    # --- deep-state lemmas
    ndeep = 0
    for q in range(4):
        if plan[q][0] != 'deep':
            continue
        ndeep += 1
        _, kd, (ve, vx) = plan[q]
        src += fill(DEEP, {'@N@': str(ndeep), '@QDEEP@': ST[q],
                           '@KDEEP@': str(kd), '@VDE@': cwin(ve),
                           '@VDX@': cwin(vx), '@VDL@': clist(vx[1]),
                           '@VDH@': csym(vx[2]),
                           '@VDRCONS@': ccons(vx[3], '')})
    # --- prefix lemmas + the vis dispatcher
    pre_lemmas, cases, seen = [], [], {}
    ndeep = 0
    for q in range(4):
        kind = plan[q][0]
        if kind == 'anchor':
            cases.append("  - (* %s : the anchor state *)\n"
                         "    exists 0. eexists. split; reflexivity." % ST[q])
        elif kind == 'deep':
            ndeep += 1
            cases.append("  - (* %s : deep (overflow) state *)\n"
                         "    apply (vis_deep%d_%s p)." % (ST[q], ndeep, ID))
        else:
            _, k, depth, ex, k1 = plan[q]
            name = "phV%d_%s" % (k, ID)
            if k not in seen:
                seen[k] = True
                exq, exl, exh, exr = ex
                if depth == 2:
                    pre_lemmas.append(
                        "Lemma %s : forall x L R, csteps tm %d (%s,(S1::x::L,S0,R)) = "
                        "Some (%s,(%s,%s,%s)).\nProof. intros. reflexivity. Qed."
                        % (name, k, ST[E], ST[exq], ccons(exl, 'L'), csym(exh),
                           ccons(exr, 'R')))
                else:
                    pre_lemmas.append(
                        "Lemma %s : forall L R, csteps tm %d (%s,(S1::L,S0,R)) = "
                        "Some (%s,(%s,%s,%s)).\nProof. intros. reflexivity. Qed."
                        % (name, k, ST[E], ST[exq], ccons(exl, 'L'), csym(exh),
                           ccons(exr, 'R')))
            if depth == 1:
                cases.append(
                    "  - (* %s : %d steps from the anchor *)\n"
                    "    exists %d. eexists. rewrite Hw. split; [apply %s | reflexivity]."
                    % (ST[q], k, k, name))
            else:
                cases.append(
                    "  - (* %s : %d steps from the anchor (p = 1 apart) *)\n"
                    "    rewrite Hw. destruct w as [|x w'].\n"
                    "    + exists %d. eexists. split; [vm_compute; reflexivity | reflexivity].\n"
                    "    + exists %d. eexists. split.\n"
                    "      * change ((S1 :: x :: w') ++ %s) with (S1 :: x :: (w' ++ %s)).\n"
                    "        apply %s.\n"
                    "      * reflexivity."
                    % (ST[q], k, k1, k, clist(tail), clist(tail), name))
    if pre_lemmas:
        src += "\n(** ** Bounded anchor prefixes for the shallow states *)\n"
        src += "\n".join(pre_lemmas) + "\n"
    src += ("\nLemma vis_%s : forall p q, exists k c, csteps tm k (Cc p) = Some c /\\ fst c = q.\n"
            "Proof.\n  intros p q. destruct (Jp_head p) as (w & Hw). unfold Cc_%s. destruct q.\n"
            % (ID, ID))
    src += "\n".join(cases) + "\nQed.\n"
    src += fill(TAIL)
    return src


# --------------------------------------------------------------- pipeline ----
COQ_ENV = ('export OPAMROOT=/root/.opam; eval $(opam env --switch=census) '
           '2>/dev/null; cd %s; ' % REPO)


def coqc(path, extra=''):
    cmd = COQ_ENV + 'coqc -native-compiler no -Q theories BBB4 %s %s' % (extra, path)
    p = subprocess.run(['bash', '-lc', cmd], capture_output=True, text=True,
                       timeout=1800)
    return p.returncode, p.stdout + p.stderr


def print_assumptions(spec):
    ID = mach_id(spec)
    chk = os.path.join(SCRATCH, 'pa_%s.v' % ID)
    with open(chk, 'w') as f:
        f.write("From BBB4.Machines.Counters Require Import ILQ_%s.\n"
                "Print Assumptions nqh_%s.\n" % (ID, ID))
    rc, out = coqc(chk)
    return rc, out


def process(spec, fp, do_emit=True, quiet=False):
    """Full pipeline for one machine.  Returns a result dict."""
    res = {'spec': spec, 'ok': False}
    r = fp.get(spec)
    if r is None or r.get('cls') != 'COUNTER':
        res['why'] = 'no counter fingerprint'
        return res
    res['fp'] = r
    if r['growth'] != 'L':
        res['why'] = 'growth %s (this emitter targets L)' % r['growth']
        return res
    try:
        edge, tail, p0 = derive_tail(spec, r['edge'])
        res['edge'] = edge
        res['tail'] = tail
        res['p0'] = p0
        enc = 'Jp'
        s, U = derive(spec, edge, enc, p0, tail)
        res['skel'] = s
        msgs = shape_check(s, U, enc, edge, tail)
        if msgs:
            res['why'] = 'shape: ' + '; '.join(msgs)
            return res
        exact_int, exact_ov, nchk = validate(spec, s, U, edge, enc, tail)
        res['nchecked'] = nchk
        if not exact_int:
            res['why'] = 'interior lap is not exact (deep-visit chain needs it)'
            return res
        boot = boot_probe(spec, edge, enc, p0, tail)
        res['boot'] = boot
        E = LAB.index(edge)
        plan = visit_plan(spec, s, U, E, enc, tail)
        res['plan'] = {LAB[q]: plan[q][0] for q in plan}
    except (DeriveError, AssertionError, Wall, KeyError, IndexError) as e:
        res['why'] = '%s: %s' % (type(e).__name__, e)
        return res
    if not do_emit:
        res['ok'] = True
        res['why'] = 'derived+validated (not emitted)'
        return res
    src = emit_source(spec, dict(r, edge=edge, enc=enc), s, U, plan, boot, tail, p0)
    path = os.path.join(OUTDIR, 'ILQ_%s.v' % mach_id(spec))
    with open(path, 'w') as f:
        f.write(src)
    res['file'] = path
    rc, out = coqc(path)
    if rc != 0:
        res['why'] = 'coqc failed'
        res['log'] = out[-4000:]
        return res
    rc, out = print_assumptions(spec)
    res['assumptions'] = out.strip()
    if rc != 0:
        res['why'] = 'Print Assumptions failed'
        res['log'] = out[-2000:]
        return res
    names = set()
    inax = False
    for ln in out.splitlines():
        if ln.startswith('Axioms:'):
            inax = True
            continue
        if not inax:
            continue
        if ln[:1].isspace() or not ln.strip():
            continue
        nm = ln.strip().split(':')[0].strip()
        if not re.match(r'^[A-Za-z_][A-Za-z_0-9.\']*$', nm):
            continue
        names.add(nm.split('.')[-1])
    res['axioms'] = sorted(names)
    res['ok'] = (res['axioms'] == ['functional_extensionality_dep'])
    if not res['ok']:
        res['why'] = 'unexpected axioms: %s' % res['axioms']
    return res


def load_fp(path=DEFAULT_FP):
    fp = {}
    with open(path) as f:
        for line in f:
            r = json.loads(line)
            fp[r['m']] = r
    return fp


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('specs', nargs='*')
    ap.add_argument('--list', help='file of specs')
    ap.add_argument('--fp', default=DEFAULT_FP)
    ap.add_argument('--emit', action='store_true',
                    help='emit Coq, compile, and Print Assumptions')
    ap.add_argument('--json', help='write per-machine results here')
    a = ap.parse_args()
    specs = list(a.specs)
    if a.list:
        specs += [x.strip() for x in open(a.list) if x.strip()]
    fp = load_fp(a.fp)
    out = []
    for spec in specs:
        res = process(spec, fp, do_emit=a.emit)
        out.append(res)
        tag = 'PASS' if res['ok'] else 'FAIL'
        print("%s %s %s" % (tag, spec, res.get('why', '')))
        if res.get('log'):
            for ln in res['log'].splitlines()[-25:]:
                print("      | %s" % ln)
        sys.stdout.flush()
    if a.json:
        with open(a.json, 'w') as f:
            json.dump(out, f, indent=1)
    npass = sum(1 for r in out if r['ok'])
    print("== %d/%d passed" % (npass, len(out)))


if __name__ == '__main__':
    main()
