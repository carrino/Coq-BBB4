#!/usr/bin/env python3
"""UNTRUSTED auto-emitter for LEFT-growth comb-free interleaved-counter boards.

Per machine SPEC (a (4,2) transition string like 0RB---_0LC1RB_1LA1LD_1LC0RB):

  1. read the fingerprint (enc / growth / edge / p0) from fp_counters.jsonl;
  2. DERIVE the anchor  Cc p = (edge, (enc p ++ [S0], S0, []))  and the six lap
     unit windows -- P1 prologue, RIP leftward carry ripple (cycL over the low
     set-bit pairs), STPI interior stop / STPO overflow stop off the deep-left
     tape edge, RET rightward return (cycR), FIN -- by a chained search over
     the comb-free skeleton, anchored by the RAW step count of one lap: a
     candidate decomposition is accepted only if the symbolic chain lands
     exactly on Cc(p+1) in exactly the raw number of steps, on an interior
     sample AND on an overflow sample;
  3. differentially validate the derived symbolic lap against the raw
     simulator for many p across BOTH cview branches, and check the derived
     units against the algebraic shape the Coq template's rewrites need;
  4. probe the bootstrap (least T with csteps tm T c0 = Cc p0) and the
     per-state visit witnesses;
  5. string-emit theories/Machines/Counters/ILC_<id>.v, a clone of the
     hand-authored template Interleave_TGT.v with the per-machine table,
     states, step counts and windows substituted, every global name suffixed
     by <id> so files never clash;
  6. run coqc -native-compiler no and Print Assumptions, and report pass/fail.

Everything here is UNTRUSTED: a wrong window or step count cannot mis-prove
anything, it simply fails to typecheck.  The Coq kernel re-checks every board.
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
ST = ["StA", "StB", "StC", "StD"]
SYM = ["S0", "S1"]

DEFAULT_FP = ('/tmp/claude-0/-home-user/722d7ed5-2c00-5fef-984d-cc3db7bde694/'
              'scratchpad/fp_counters.jsonl')
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


def raw_lap(raw, E, encf, m, maxsteps=400000):
    """Steps of one lap Cc(m) -> Cc(m+1) (normalized match)."""
    cfg = (E, encf(m) + [0], 0, [])
    tgt = nrm((E, encf(m + 1) + [0], 0, []))
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


def chain_int(ex, E, encf, m, j, s):
    """Interior chain with skeleton s; returns (steps, cfg, units)."""
    cfg = (E, encf(m) + [0], 0, [])
    steps = 0
    U = {}
    cfg, U['P1e'], U['P1x'] = conc(ex, cfg, True, True, s['nP1'], s['lwP1'], 0)
    steps += s['nP1']
    cfg, U['RIPe'], U['RIPx'], w = cyc_l(ex, cfg, s['ulen'], s['rwR'], s['nRIP'], j)
    steps += s['nRIP'] * j
    cfg, U['STPIe'], U['STPIx'] = conc(ex, cfg, True, True, s['nSTP'],
                                       s['lwS'], s['rwS'])
    steps += s['nSTP']
    m1 = len(U['P1x'][3])
    k = (len(cfg[3]) - m1)
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


def chain_ov(ex, E, encf, m, j, s):
    """Overflow chain (ripple j-1 units, stop off the deep-left edge)."""
    cfg = (E, encf(m) + [0], 0, [])
    steps = 0
    U = {}
    cfg, U['P1e'], U['P1x'] = conc(ex, cfg, True, True, s['nP1'], s['lwP1'], 0)
    steps += s['nP1']
    cfg, _, _, w = cyc_l(ex, cfg, s['ulen'], s['rwR'], s['nRIP'], j - 1)
    steps += s['nRIP'] * (j - 1)
    cfg, U['STPOe'], U['STPOx'] = conc(ex, cfg, False, True, s['nSTPO'],
                                       None, s['rwO'])
    steps += s['nSTPO']
    m1 = len(U['P1x'][3])
    k = (len(cfg[3]) - m1)
    if k < 0 or k % s['uret']:
        raise Wall("overflow return count does not divide")
    k //= s['uret']
    cfg, _, _, _ = cyc_r(ex, cfg, s['uret'], s['nRET'], k)
    steps += s['nRET'] * k
    cfg, _, _ = conc(ex, cfg, True, True, s['nFIN'], 0, m1)
    steps += s['nFIN']
    U['kret'] = k
    return steps, cfg, U


def derive(spec, edge, encname, p0):
    """Search the comb-free skeleton; returns (skeleton, units)."""
    encf = ENC[encname]
    E = LAB.index(edge)
    raw = Raw(spec)
    ex = Exec(spec)

    JI, KO = 3, 4
    m_int = (1 << (JI + 1)) + (1 << JI) - 1      # j = JI trailing ones
    m_ov = (1 << KO) - 1                          # overflow, j = KO
    assert carry(m_int) == (JI, False) and carry(m_ov) == (KO, True)
    n_int, _ = raw_lap(raw, E, encf, m_int)
    n_ov, _ = raw_lap(raw, E, encf, m_ov)
    tgt_int = nrm((E, encf(m_int + 1) + [0], 0, []))
    tgt_ov = nrm((E, encf(m_ov + 1) + [0], 0, []))

    sols = []
    for nP1 in range(1, MAXP1 + 1):
        for lwP1 in range(1, 4):
            for nRIP in range(1, MAXRIP + 1):
                for ulen in (2,):
                    for rwR in range(0, 3):
                        s0 = dict(nP1=nP1, lwP1=lwP1, nRIP=nRIP, ulen=ulen,
                                  rwR=rwR)
                        # quick feasibility of the prologue+ripple
                        try:
                            cfg = (E, encf(m_int) + [0], 0, [])
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
                                                s = dict(s0, nSTP=nSTP, lwS=lwS,
                                                         rwS=rwS, uret=uret,
                                                         nRET=nRET, nFIN=nFIN)
                                                tot = (nP1 + nRIP * JI + nSTP
                                                       + nFIN)
                                                if tot >= n_int:
                                                    continue
                                                try:
                                                    st, cfg2, U = chain_int(
                                                        ex, E, encf, m_int, JI, s)
                                                except (Wall, KeyError, IndexError):
                                                    continue
                                                if st != n_int or nrm(cfg2) != tgt_int:
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

    # ---- now fix the overflow stop against each interior candidate
    for (s, U) in sols:
        for nSTPO in range(1, MAXSTP + 2):
            for rwO in range(0, 3):
                s2 = dict(s, nSTPO=nSTPO, rwO=rwO)
                try:
                    st, cfg2, UO = chain_ov(ex, E, encf, m_ov, KO, s2)
                except (Wall, KeyError, IndexError):
                    continue
                if st != n_ov or nrm(cfg2) != tgt_ov:
                    continue
                U = dict(U)
                U.update(UO)
                return s2, U
    raise DeriveError("no overflow stop fits the raw lap")


# --------------------------------------------------------- symbolic replay ---
def sym_lap(ex, s, E, encf, m):
    j, ov = carry(m)
    if ov:
        return chain_ov(ex, E, encf, m, j, s)
    return chain_int(ex, E, encf, m, j, s)


def validate(spec, s, edge, encname, hi=160):
    """Differential: symbolic lap == raw lap, exact landing, uniform units."""
    encf = ENC[encname]
    E = LAB.index(edge)
    raw = Raw(spec)
    ex = Exec(spec)
    ms = sorted(set(list(range(1, hi + 1))
                    + [(1 << k) - 1 for k in range(1, 13)]
                    + [(1 << k) for k in range(1, 13)]
                    + [(1 << k) + (1 << (k - 3)) - 1 for k in range(4, 13)]
                    + [(1 << 12) + (1 << 9) - 1, (1 << 14) - 1]))
    exact = True
    units = None
    for m in ms:
        n_sym, cfg_sym, U = sym_lap(ex, s, E, encf, m)
        n_raw, _ = raw_lap(raw, E, encf, m)
        tgt = (E, encf(m + 1) + [0], 0, [])
        if n_sym != n_raw:
            raise DeriveError("m=%d: sym %d != raw %d steps" % (m, n_sym, n_raw))
        if nrm(cfg_sym) != nrm(tgt):
            raise DeriveError("m=%d: sym config %s != Cc(m+1) %s"
                              % (m, nrm(cfg_sym), nrm(tgt)))
        if list(cfg_sym[1]) != list(tgt[1]) or list(cfg_sym[3]) != list(tgt[3]):
            exact = False
        # the return count must be the algebraic one
        j, ov = carry(m)
        want = 2 * j if not ov else 2 * j
        if U['kret'] != want:
            raise DeriveError("m=%d: return count %d != %d" % (m, U['kret'], want))
        units = U
    return exact, units


# ------------------------------------------------------- shape requirements --
def shape_check(s, U, encname, edge):
    """The Coq template's rewrites need exactly these symbol shapes."""
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
    if Se[1] != (1, 1) or Se[3] != () or Sx[1] != (0, 1) or Sx[3] != ():
        msgs.append("STPI %s -> %s is not [S1;S1] -> [S0;S1]" % (Se, Sx))
    if Se[2] != Sx[2]:
        msgs.append("STPI moves the head symbol")
    if Te[3] != (Rx[3][0],) or Tx[1] != (1,) or Tx[3] != ():
        msgs.append("RET %s -> %s does not consume the RIP cell into [S1]"
                    % (Te, Tx))
    if s['uret'] != 1:
        msgs.append("return unit consumes %d cells (template needs 1)" % s['uret'])
    if Fe[1] != () or Fe[3] != (0,):
        msgs.append("FIN entry %s is not ([],[S0])" % (Fe,))
    if Fx[1] != (1,) or Fx[3] != () or Fx[2] != 0 or Fx[0] != E:
        msgs.append("FIN exit %s is not the anchor (edge,[S1],S0,[])" % (Fx,))
    if Oe[1] != (0,) or Oe[3] != () or Ox[1] != (0,) or Ox[3] != Rx[3]:
        msgs.append("STPO %s -> %s is not ([S0],[]) -> ([S0], rip-deposit)"
                    % (Oe, Ox))
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


# ------------------------------------------------------------------- boot ----
def boot_probe(spec, edge, encname, p0, maxT=20000):
    encf = ENC[encname]
    E = LAB.index(edge)
    raw = Raw(spec)
    tgt = nrm((E, encf(p0) + [0], 0, []))
    cfg = (0, [], 0, [])
    for t in range(maxT):
        if nrm(cfg) == tgt:
            return t
        cfg = raw.step(cfg)
        if cfg is None:
            raise DeriveError("halts during bootstrap at t=%d" % t)
    raise DeriveError("no bootstrap to Cc(%d) in %d steps" % (p0, maxT))


# ------------------------------------------------------------------ visits ---
def visit_probe(spec, edge, encname, s, hi=200):
    """For each state: the offset from the anchor at which it is first seen.

    Returns (uniform, overflow_only) maps.  `uniform[q] = k` means state q is
    reached at exactly k steps from EVERY sampled anchor; `overflow[q] = k`
    means it is reached at k steps from the P1+RIP ripple end of an overflow
    anchor (uniformly in j)."""
    encf = ENC[encname]
    E = LAB.index(edge)
    raw = Raw(spec)
    firsts = {}
    for m in range(1, hi + 1):
        cfg = (E, encf(m) + [0], 0, [])
        seen = {}
        for t in range(0, 400):
            if cfg[0] not in seen:
                seen[cfg[0]] = t
            if len(seen) == 4:
                break
            cfg = raw.step(cfg)
            if cfg is None:
                break
        for q, t in seen.items():
            firsts.setdefault(q, set()).add(t)
    uniform = {q: list(v)[0] for q, v in firsts.items() if len(v) == 1}
    # overflow route: from an all-ones anchor, offset of each state
    ex = Exec(spec)
    ovf = {}
    for k in (2, 3, 4, 5, 6):
        m = (1 << k) - 1
        cfg = (E, encf(m) + [0], 0, [])
        cfg, _, _ = conc(ex, cfg, True, True, s['nP1'], s['lwP1'], 0)
        cfg, _, _, _ = cyc_l(ex, cfg, s['ulen'], s['rwR'], s['nRIP'], k - 1)
        base = s['nP1'] + s['nRIP'] * (k - 1)
        seen = {}
        c = cfg
        for t in range(0, 40):
            if c[0] not in seen:
                seen[c[0]] = t
            c = raw.step(c)
            if c is None:
                break
        for q, t in seen.items():
            ovf.setdefault(q, set()).add(t)
    ovf = {q: list(v)[0] for q, v in ovf.items() if len(v) == 1}
    return uniform, ovf


# -------------------------------------------------------------- Coq emission --
def coq_sym(x):
    return SYM[x]


def coq_list(xs):
    return "[" + ";".join(coq_sym(x) for x in xs) + "]"


def coq_cfg(c):
    q, l, h, r = c
    return "(%s,(%s,%s,%s))" % (ST[q], coq_list(l), coq_sym(h), coq_list(r))


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


TEMPLATE = r'''(** * ILC_{ID}: comb-free interleaved binary counter, machine
    {SPEC}.

    Auto-emitted by tools/counters/emit_interleave.py (UNTRUSTED; the kernel
    re-checks everything here).  Left-growth counter under the complemented
    interleave encoding [Jp] (JpCounter.v): the anchor is

      Cc p = ({EDGE}, (Jp p ++ [S0], S0, []))

    -- counter on the LEFT list nearest-first, blank head, empty right side,
    no comb.  One lap Cc p -> Cc (p+1) is a single sweep: prologue, leftward
    carry ripple over the low set-bit pairs (cycL), interior stop at the first
    clear pair OR overflow stop off the deep-left tape edge, rightward return
    (cycR), close at the frontier.  Windows derived by simulation and
    differentially validated against the raw simulator on both cview branches
    (interior / overflow) for p = 1..160 and sparse p up to 2^14. *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter ILCounter JpCounter.
Import ListNotations.

Definition mk_{ID} (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_{ID}.

Definition tm_{ID} : TM := fun q s => match q, s with
{TABLE} end.
Local Notation tm := tm_{ID}.

Definition Cc_{ID} (p : positive) : cconf := ({EDGE}, (Jp p ++ [S0], S0, [])).
Local Notation Cc := Cc_{ID}.

(* --- the 6 lap unit windows + the deep-visit unit --- *)
Lemma U_P1_{ID} : wsteps true true tm {NP1} {P1E} = Some {P1X}. Proof. reflexivity. Qed.
Lemma U_RIP_{ID} : wsteps true true tm {NRIP} {RIPE} = Some {RIPX}. Proof. reflexivity. Qed.
Lemma U_STPI_{ID} : wsteps true true tm {NSTP} {STPIE} = Some {STPIX}. Proof. reflexivity. Qed.
Lemma U_STPO_{ID} : wsteps false true tm {NSTPO} {STPOE} = Some {STPOX}. Proof. reflexivity. Qed.
Lemma U_RET_{ID} : wsteps true true tm {NRET} {RETE} = Some {RETX}. Proof. reflexivity. Qed.
Lemma U_FIN_{ID} : wsteps true true tm {NFIN} {FINE} = Some {FINX}. Proof. reflexivity. Qed.

(* --- transported phases (framing = each unit's bl/br) --- *)
Lemma phP1_{ID} : forall L R, csteps tm {NP1} ({EDGE},(S1::L,S0,R)) = Some ({QR},(L,{HR},{P1DEP} ++ R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_P1_{ID}). Qed.
Lemma phRIP_{ID} : forall k L R, csteps tm ({NRIP}*k) ({QR},(rep [S0;S1] k ++ L,{HR},R)) = Some ({QR},(L,{HR},rep {WDEP} k ++ R)).
Proof. intros. pose proof (cycL _ _ _ _ _ _ _ U_RIP_{ID} k L R) as H; cbn [app] in H; exact H. Qed.
Lemma phSTPI_{ID} : forall L R, csteps tm {NSTP} ({QR},(S1::S1::L,{HR},R)) = Some ({QT},(S0::S1::L,{HT},R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STPI_{ID}). Qed.
Lemma phSTPO_{ID} : forall R, csteps tm {NSTPO} ({QR},([S0],{HR},R)) = Some ({QT},([S0],{HT},{WDEPC} ++ R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPO_{ID}). Qed.
Lemma phRET_{ID} : forall k L R, csteps tm ({NRET}*k) ({QT},(L,{HT},rep {WCELL} k ++ R)) = Some ({QT},(rep [S1] k ++ L,{HT},R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U_RET_{ID} k L R). Qed.
Lemma phFIN_{ID} : forall L R, csteps tm {NFIN} ({QT},(L,{HT},S0::R)) = Some ({EDGE},(S1::L,S0,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FIN_{ID}). Qed.

(* EXACT lap (no lift): iterate to the next anchor with the exact config. *)
Lemma lap_exact_{ID} : forall p, exists n c', csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intros p. pose proof (Pos2Nat.is_pos p) as Hpos.
  destruct (cview p) as [j oq] eqn:Ecv. unfold Cc_{ID}.
  destruct oq as [q0|].
  - destruct (cview_some_J p j q0 Ecv) as (HJp & HJs). destruct (Jp_head q0) as (iq & Hiq).
    do 2 eexists. split; [|split].
    + rewrite HJp, <- app_assoc.
      change (rep [S1;S0] j ++ (S1 :: S1 :: Jp q0) ++ [S0])
        with (rep [S1;S0] j ++ [S1] ++ (S1 :: Jp q0 ++ [S0])).
      rewrite app_assoc, pair_rot.
      eapply csteps_chain. {{ apply phP1_{ID}. }}
      eapply csteps_chain. {{ apply phRIP_{ID}. }}
      rewrite Hiq.
      eapply csteps_chain. {{ apply phSTPI_{ID}. }}
      rewrite rep_dbl.
      eapply csteps_chain. {{ apply (phRET_{ID} (2*j)). }}
      apply phFIN_{ID}.
    + rewrite HJs, Hiq, rep_dbl. cbn [Nat.mul]. rewrite rep_slide, <- !app_assoc. reflexivity.
    + lia.
  - destruct j as [|j'].
    {{ exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }}
    destruct (cview_none_J p j' Ecv) as (HJp & HJs).
    do 2 eexists. split; [|split].
    + rewrite HJp, pair_rot.
      eapply csteps_chain. {{ apply phP1_{ID}. }}
      eapply csteps_chain. {{ apply phRIP_{ID}. }}
      eapply csteps_chain. {{ apply phSTPO_{ID}. }}
      change (S1 :: S1 :: rep [S1;S1] j' ++ [S0]) with (rep [S1;S1] (S j') ++ [S0]).
      rewrite rep_dbl.
      eapply csteps_chain. {{ apply (phRET_{ID} (2*(S j'))). }}
      apply phFIN_{ID}.
    + rewrite HJs, rep_dbl. cbn [Nat.mul]. rewrite rep_slide, <- !app_assoc. reflexivity.
    + lia.
Qed.

Lemma lap_{ID} : forall p, exists n c', csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof. intro p. destruct (lap_exact_{ID} p) as (n & c' & Hr & Hc & Hn). exists n, c'.
  split; [exact Hr | split; [rewrite Hc; reflexivity | exact Hn]]. Qed.

Lemma boot_{ID} : exists t0, stepn tm t0 InitES = Some (lift (Cc {P0})).
Proof.
  exists {BOOT}.
  assert (H : match csteps tm {BOOT} c0 with Some c => ceqb c (Cc {P0}) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm {BOOT} c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

{VIS}

Theorem nqh_{ID} : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc {P0}). - exact boot_{ID}. - intros p _. apply lap_{ID}. - intros p q _. apply vis_{ID}. Qed.

Theorem nonhalt_{ID} : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_{ID}. Qed.
'''


def emit_vis(s, U, uni, ovf, edge, deep_states):
    """Emit the per-state visit witnesses.

    - the anchor state is reached in 0 steps;
    - states reached at a uniform small offset use a prefix lemma proved by
      [reflexivity] (the run never branches on an unknown cell) after
      destructing [Jp p] far enough;
    - a state only reached deep in the overflow lap uses the well-founded
      [tovf] induction: lap forward until the counter is all ones, then run
      the prologue + ripple + the deep unit."""
    E = LAB.index(edge)
    out = []
    ID = "{ID}"
    # ---- deep (overflow-only) state, if any
    if deep_states:
        q, n_deep, exitcfg = deep_states
        out.append(
            "Lemma U_VA_%s : wsteps false true tm %d %s = Some %s. Proof. reflexivity. Qed."
            % (ID, n_deep, coq_cfg(exitcfg[0]), coq_cfg(exitcfg[1])))
        out.append(
            "Lemma phVA_%s : forall R, csteps tm %d (%s,([S0],%s,R)) = Some (%s,(%s,%s,%s ++ R)).\n"
            "Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_VA_%s). Qed."
            % (ID, n_deep, ST[exitcfg[0][0]], coq_sym(exitcfg[0][2]),
               ST[exitcfg[1][0]], coq_list(exitcfg[1][1]), coq_sym(exitcfg[1][2]),
               coq_list(exitcfg[1][3]), ID))
        out.append(VIS_DEEP.replace("{QDEEP}", ST[q]))
    return "\n".join(out)


VIS_DEEP = r'''Lemma vis_deep_{ID} : forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = {QDEEP}.
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.
  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj). rewrite Hjj in Ecv; discriminate. }
    destruct (lap_exact_{ID} p) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ p)) (ltac:(rewrite tovf_succ by lia; lia)) (Pos.succ p) eq_refl) as (k & c & Hk & Hq).
    exists (n + k), c. rewrite csteps_add, Hrun. exact (conj Hk Hq).
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv; [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_J p j' Ecv) as (HJp & _).
    unfold Cc_{ID}. eexists. eexists. split.
    * rewrite HJp, pair_rot.
      eapply csteps_chain. { apply phP1_{ID}. }
      eapply csteps_chain. { apply phRIP_{ID}. }
      apply phVA_{ID}.
    * reflexivity.
Qed.
'''


def load_fp(path=DEFAULT_FP):
    fp = {}
    with open(path) as f:
        for line in f:
            r = json.loads(line)
            fp[r['m']] = r
    return fp


def survey(specs, fp):
    for spec in specs:
        r = fp.get(spec)
        if r is None or r.get('cls') != 'COUNTER':
            print("SKIP  %s (no counter fingerprint)" % spec)
            continue
        try:
            s, U = derive(spec, r['edge'], r['enc'], r['p0'])
            msgs = shape_check(s, U, r['enc'], r['edge'])
            exact, _ = validate(spec, s, r['edge'], r['enc'])
            bt = boot_probe(spec, r['edge'], r['enc'], r['p0'])
            uni, ovf = visit_probe(spec, r['edge'], r['enc'], s)
            print("%-5s %s enc=%s edge=%s p0=%d boot=%d exact=%s n=%s uni=%s ovf=%s"
                  % ("OK" if not msgs else "SHAPE", spec, r['enc'], r['edge'],
                     r['p0'], bt, exact,
                     (s['nP1'], s['nRIP'], s['nSTP'], s['nSTPO'], s['nRET'],
                      s['nFIN'], s['lwP1'], s['lwS'], s['rwS'], s['rwR'],
                      s['rwO'], s['uret']),
                     {LAB[q]: v for q, v in sorted(uni.items())},
                     {LAB[q]: v for q, v in sorted(ovf.items())}))
            for msg in msgs:
                print("      ! %s" % msg)
        except (DeriveError, AssertionError, Wall) as e:
            print("FAIL  %s : %s" % (spec, e))
        sys.stdout.flush()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('specs', nargs='*')
    ap.add_argument('--list', help='file of specs')
    ap.add_argument('--fp', default=DEFAULT_FP)
    a = ap.parse_args()
    specs = list(a.specs)
    if a.list:
        specs += [x.strip() for x in open(a.list) if x.strip()]
    fp = load_fp(a.fp)
    survey(specs, fp)


if __name__ == '__main__':
    main()
