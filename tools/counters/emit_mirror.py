#!/usr/bin/env python3
"""UNTRUSTED auto-emitter for RIGHT-growth comb-free interleaved-counter boards.

The census's interleaved binary counters come in two orientations.  The
LEFT-growth ones carry the [Interleave_TGT.v] template directly.  The
RIGHT-growth ones do not: their counter grows on the right, so the
template's leftward carry ripple / rightward return is reflected.  We
board them through [Mirror.v]:

    mirror_never_qh : NeverQuasiHaltsSt (mirror_tm tm) -> NeverQuasiHaltsSt tm

so it suffices to prove the LEFT-growth lap for the MIRROR of the machine
and transfer.  Per machine SPEC (a (4,2) transition string):

  1. mirror the table (every DR <-> DL) -- the mirror of a right-growth
     counter is a left-growth counter with the same encoding/edge/p0;
  2. DERIVE, from a raw simulation of one lap of the MIRRORED machine, the
     anchor  Cc p = (edge, (Jp p ++ [S0], S0, []))  and the six lap unit
     windows (P1 prologue, RIP leftward carry ripple, STPI interior stop /
     STPO overflow stop off the deep-left edge, RET rightward return, FIN)
     by solving the affine phase-length system across several carry
     depths j, then cutting the windows with the Exec wall discipline;
  3. shape-check the units against the algebraic form the Coq template's
     rewrites need, and differentially validate the symbolic lap against
     the raw simulator over both cview branches;
  4. derive the per-state visit routes (determined prefix from the anchor /
     overflow-branch prefix under the tovf well-founded induction);
  5. probe the bootstrap (least T with csteps tmm T c0 =_lift Cc p0);
  6. string-emit theories/Machines/Counters/ILCM_<id>.v: the original table,
     the explicit mirrored table + [mirror_ok], the lap/visit/boot proofs on
     the mirror, [glue_neverqh], and the [mirror_never_qh] transfer, with
     every global name suffixed by <id> so files never clash;
  7. run coqc -native-compiler no and Print Assumptions, and report.

Everything here is UNTRUSTED: a wrong window, step count or state cannot
mis-prove anything, it simply fails to typecheck.  The Coq kernel
re-checks every board.
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

DEFAULT_FP = ('/tmp/claude-0/-home-user/722d7ed5-2c00-5fef-984d-cc3db7bde694/'
              'scratchpad/fp_counters.jsonl')


class DeriveError(Exception):
    pass


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
    """MonoCounter.cview as (j, overflow?): j low set bits, p = 2^j-1?"""
    j = 0
    while (m >> j) & 1:
        j += 1
    return j, (m == (1 << j) - 1)


# ------------------------------------------------------------ spec algebra ---
def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab


def mirror_spec(spec):
    """mirror_tm on the SPEC string: flip every move direction."""
    out = []
    for part in spec.split('_'):
        s = ''
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            s += e if e == '---' else e[0] + ('L' if e[1] == 'R' else 'R') + e[2]
        out.append(s)
    return '_'.join(out)


def ident(spec):
    """A Coq-identifier-safe, collision-free suffix for the machine."""
    return spec.replace('_', '').replace('-', 'H')


# ------------------------------------------------------------ raw stepping ---
class Raw:
    def __init__(self, spec):
        self.tab = parse(spec)

    def step(self, cfg):
        q, l, h, r = cfg
        e = self.tab[(q, h)]
        if e is None:
            return None, 0
        w, d, ns = e
        if d > 0:
            return (ns, [w] + l, r[0] if r else 0, r[1:]), +1
        return (ns, l[1:], l[0] if l else 0, [w] + r), -1


def strip0(l):
    l = list(l)
    while l and l[-1] == 0:
        l.pop()
    return l


def nrm(cfg):
    q, l, h, r = cfg
    return (q, tuple(strip0(l)), h, tuple(strip0(r)))


def raw_lap(raw, E, encf, m, maxsteps=400000):
    """One lap of the MIRRORED machine from the anchor.

    Returns (T, positions) with positions[t] the head offset from the frontier.
    """
    cfg = (E, encf(m) + [0], 0, [])
    tgt = nrm((E, encf(m + 1) + [0], 0, []))
    pos, positions = 0, [0]
    for t in range(1, maxsteps):
        nxt, d = raw.step(cfg)
        if nxt is None:
            raise DeriveError("halts inside the lap at m=%d t=%d" % (m, t))
        cfg = nxt
        pos += d
        positions.append(pos)
        if nrm(cfg) == tgt:
            return t, positions
    raise DeriveError("no lap closure from m=%d in %d steps" % (m, maxsteps))


# ------------------------------------------------------------ segmentation ---
def cut(positions, T, j, ov):
    """Phase boundary times of one lap, from the head-position profile.

    Interior:  0 -P1-> -1 -RIP*j-> -(1+2j) -STPI-> -(1+2j) -RET*2j-> -1 -FIN-> 0
    Overflow:  0 -P1-> -1 -RIP*(j-1)-> -(2j-1) -STPO-> -(1+2j) -RET*2j-> -1 -FIN
    """
    if max(positions) != 0:
        raise DeriveError("head leaves the frontier rightward (max pos %d)"
                          % max(positions))
    k_rip = j - 1 if ov else j
    p_rip = -(1 + 2 * k_rip)
    p_ret = -(1 + 2 * j)
    try:
        t_rip = next(t for t in range(T + 1) if positions[t] == p_rip)
        t_ret = max(t for t in range(T + 1) if positions[t] == p_ret)
        t_fin = max(t for t in range(T + 1) if positions[t] == -1)
    except (StopIteration, ValueError):
        raise DeriveError("lap profile does not reach the template depths")
    if not (0 < t_rip <= t_ret <= t_fin <= T):
        raise DeriveError("phase times out of order: %d %d %d %d"
                          % (t_rip, t_ret, t_fin, T))
    return t_rip, t_ret, t_fin


def solve_phases(raw, E, encf):
    """Affine solve for (nP1, P_RIP, nSTPI, P_RET, nFIN, nSTPO)."""
    def pint(j):                       # j low set bits under a clear bit
        return (1 << (j + 1)) + (1 << j) - 1

    ints = []
    for j in (2, 3, 4, 5, 6):
        m = pint(j)
        assert carry(m) == (j, False)
        T, ps = raw_lap(raw, E, encf, m)
        ints.append((j, T) + cut(ps, T, j, False))
    (j1, T1, a1, b1, c1), (j2, T2, a2, b2, c2) = ints[0], ints[1]
    if (a2 - a1) % (j2 - j1):
        raise DeriveError("ripple period not integral")
    P_rip = (a2 - a1) // (j2 - j1)
    nP1 = a1 - P_rip * j1
    nSTPI = b1 - a1
    d1, d2 = c1 - b1, c2 - b2
    if (d2 - d1) % (2 * (j2 - j1)):
        raise DeriveError("return period not integral")
    P_ret = (d2 - d1) // (2 * (j2 - j1))
    nFIN = T1 - c1
    for (j, T, a, b, c) in ints:
        if (a != nP1 + P_rip * j or b - a != nSTPI or c - b != P_ret * 2 * j
                or T - c != nFIN):
            raise DeriveError("interior phase model fails at j=%d" % j)

    ovs = []
    for j in (2, 3, 4, 5, 6):
        m = (1 << j) - 1
        assert carry(m) == (j, True)
        T, ps = raw_lap(raw, E, encf, m)
        ovs.append((j, T) + cut(ps, T, j, True))
    nSTPO = ovs[0][3] - ovs[0][2]
    for (j, T, a, b, c) in ovs:
        if (a != nP1 + P_rip * (j - 1) or b - a != nSTPO
                or c - b != P_ret * 2 * j or T - c != nFIN):
            raise DeriveError("overflow phase model fails at j=%d" % j)
    if nP1 != 1:
        raise DeriveError("prologue is %d steps, template needs 1" % nP1)
    if min(P_rip, nSTPI, P_ret, nFIN, nSTPO) <= 0:
        raise DeriveError("degenerate phase length")
    return dict(P1=nP1, RIP=P_rip, STPI=nSTPI, RET=P_ret, FIN=nFIN, STPO=nSTPO)


# --------------------------------------------------------- symbolic replay ---
def sym_lap(ex, ph, E, encf, m):
    """Replay the derived skeleton with the Exec wall discipline."""
    ex.steps = 0
    j, ov = carry(m)
    cfg = (E, encf(m) + [0], 0, [])
    cfg = ex.conc(cfg, True, True, ph['P1'], 1, 0, "P1")
    if not ov:
        cfg = ex.cycL(cfg, 2, 0, ph['RIP'], j, "RIP")
        cfg = ex.conc(cfg, True, True, ph['STPI'], 2, 0, "STPI")
    else:
        cfg = ex.cycL(cfg, 2, 0, ph['RIP'], j - 1, "RIP")
        cfg = ex.conc(cfg, False, True, ph['STPO'], None, 0, "STPO")
    cfg = ex.cycR(cfg, 1, ph['RET'], 2 * j, "RET")
    cfg = ex.conc(cfg, True, True, ph['FIN'], 0, 1, "FIN")
    return ex.steps, cfg


def validate(mspec, ph, E, encf, hi=140):
    raw, ex = Raw(mspec), Exec(mspec)
    ms = set(range(1, hi + 1))
    for k in range(2, 13):
        ms |= {(1 << k) - 1, 1 << k, (1 << k) + 1, (1 << k) - 2}
    ms.add((1 << 11) + (1 << 7) - 1)
    ms.discard(0)
    for m in sorted(ms):
        n_sym, cfg_sym = sym_lap(ex, ph, E, encf, m)
        n_raw, _ = raw_lap(raw, E, encf, m)
        tgt = (E, encf(m + 1) + [0], 0, [])
        if n_sym != n_raw:
            raise DeriveError("m=%d: symbolic %d != raw %d steps"
                              % (m, n_sym, n_raw))
        if nrm(cfg_sym) != nrm(tgt):
            raise DeriveError("m=%d: symbolic lap misses Cc(m+1)" % m)
    return ex.units


def shape_check(u, E):
    """The exact algebraic shape the emitted Coq rewrites depend on."""
    msgs = []

    def unit(name):
        bl, br, n, e, o = u[name]
        return bl, br, n, e, o

    _, _, nP1, eP1, oP1 = unit('P1')
    _, _, nR, eR, oR = unit('RIP')
    _, _, nS, eS, oS = unit('STPI')
    _, _, nO, eO, oO = unit('STPO')
    _, _, nT, eT, oT = unit('RET')
    _, _, nF, eF, oF = unit('FIN')
    qA, qB = oP1[0], oS[0]
    b = oR[3][0] if len(oR[3]) == 2 else None

    if eP1 != (E, (1,), 0, ()) or oP1[1] != () or oP1[2] != 1 or oP1[3] != (0,):
        msgs.append("P1 %s -> %s is not (E,[S1],S0,[]) -> (qA,[],S1,[S0])"
                    % (eP1, oP1))
    if eR != (qA, (0, 1), 1, ()):
        msgs.append("RIP entry %s is not (qA,[S0;S1],S1,[])" % (eR,))
    if oR[0] != qA or oR[1] != () or oR[2] != 1 or len(oR[3]) != 2 \
            or oR[3][0] != oR[3][1]:
        msgs.append("RIP exit %s is not (qA,[],S1,[b;b])" % (oR,))
    if eS != (qA, (1, 1), 1, ()) or oS[1] != (0, 1) or oS[2] != 1 or oS[3] != ():
        msgs.append("STPI %s -> %s is not (qA,[S1;S1],S1,[]) -> (qB,[S0;S1],S1,[])"
                    % (eS, oS))
    if eO != (qA, (0,), 1, ()) or oO != (qB, (0,), 1, oR[3]):
        msgs.append("STPO %s -> %s is not (qA,[S0],S1,[]) -> (qB,[S0],S1,[b;b])"
                    % (eO, oO))
    if eT != (qB, (), 1, (b,)) or oT != (qB, (1,), 1, ()):
        msgs.append("RET %s -> %s is not (qB,[],S1,[b]) -> (qB,[S1],S1,[])"
                    % (eT, oT))
    if eF != (qB, (), 1, (0,)) or oF != (E, (1,), 0, ()):
        msgs.append("FIN %s -> %s is not (qB,[],S1,[S0]) -> (E,[S1],S0,[])"
                    % (eF, oF))
    return msgs, qA, qB, b


# ------------------------------------------------------------------- visits --
def prefix_states(mspec, E, maxk=64):
    """Determined prefix from the anchor: left = S1::x::L, right = [] (blanks).

    Only the frontier blank, the counter's leading [S1] and one further cell
    [x] are known, so the run is symbolically determined until the head lands
    on [x] (or would pop past it).  The right half-tape at the anchor is all
    blank, so rightward excursions stay determined.

    Returns {state: (k, depth, left_tokens_above_L, head_token, right_tokens)},
    least k per state; depth = how many of [S1;x] the statement must expose.
    """
    tab = parse(mspec)
    left, right = [1, 'x'], []          # the tail of `left` are the originals
    n_orig, used = 2, 0
    q, h = E, 0
    out = {E: (0, 0, [], h, [])}
    for k in range(1, maxk + 1):
        if h == 'x':
            break
        e = tab[(q, h)]
        if e is None:
            break
        w, d, ns = e
        if d > 0:
            left.insert(0, w)
            h = right.pop(0) if right else 0
        else:
            if not left:
                break
            popped = left.pop(0)
            if len(left) < n_orig:
                n_orig -= 1
                used = 2 - n_orig
            right.insert(0, w)
            h = popped
        q = ns
        dep = max(used, 2 if h == 'x' else 0)
        # cells below the exposed originals belong to the opaque tail L
        above = left[:len(left) - n_orig]
        if q not in out or out[q][0] > k:
            out[q] = (k, dep, list(above), h, list(right))
    return out


def stpo_states(mspec, qA, nSTPO):
    """States along the overflow stop window (bl=false): the vis_A route."""
    ex = Exec(mspec)
    out = {}
    for k in range(0, nSTPO + 1):
        try:
            q, l, h, r = ex.wsteps(False, True, qA, [0], 1, [], k)
        except (Wall, KeyError):
            break
        if q not in out:
            out[q] = (k, list(l), h, list(r))
    return out


# ----------------------------------------------------------------- bootstrap --
def boot_probe(mspec, E, encf, maxT=200000):
    """Least (T, p) with csteps tmm T c0 blank-equal to Cc p."""
    raw = Raw(mspec)
    dec = {tuple(encf(m)): m for m in range(1, 1 << 14)}
    cfg = (0, [], 0, [])
    for t in range(maxT):
        q, l, h, r = cfg
        if q == E and h == 0 and not strip0(r):
            m = dec.get(tuple(strip0(l)))
            if m is not None:
                return t, m
        nxt, _ = raw.step(cfg)
        if nxt is None:
            raise DeriveError("halts during bootstrap at t=%d" % t)
        cfg = nxt
    raise DeriveError("no bootstrap anchor within %d steps" % maxT)


# -------------------------------------------------------------- Coq rendering --
def sy(x):
    return 'x' if x == 'x' else ('S1' if x == 1 else 'S0')


def lst(xs):
    return '[' + '; '.join(sy(x) for x in xs) + ']' if xs else '[]'


def cons(xs, tail):
    if not xs:
        return tail
    return ''.join('%s :: ' % sy(x) for x in xs) + tail


def tm_body(spec, mk):
    tab = parse(spec)
    rows = []
    for si in range(4):
        cells = []
        for yi in range(2):
            e = tab[(si, yi)]
            if e is None:
                cells.append('| %s, %s => None' % (ST[si], sy(yi)))
            else:
                w, d, ns = e
                cells.append('| %s, %s => %s %s %s %s'
                             % (ST[si], sy(yi), mk, sy(w),
                                'DR' if d > 0 else 'DL', ST[ns]))
        rows.append('  ' + ' '.join(cells))
    return '\n'.join(rows)


HEAD = r'''(** * ILCM_{ID}: {SPEC} -- right-growth interleaved counter via Mirror.

    Comb-free interleaved binary counter growing on the RIGHT, so the
    [Interleave_TGT.v] lap does not apply directly.  Its mirror
    ({MSPEC}) is the same counter grown LEFTward, carrying the
    [JpCounter] anchor

        Cc p = ({EST}, (Jp p ++ [S0], S0, []))

    and the template's single-sweep lap (prologue; leftward carry ripple over
    the low set pairs; interior stop / overflow stop off the deep-left edge;
    rightward return; close at the frontier).  [Mirror.mirror_never_qh] then
    transfers [NeverQuasiHaltsSt] from the mirror back to the machine.

    Auto-emitted by tools/counters/emit_mirror.py (UNTRUSTED -- every line
    below is re-checked by the Coq kernel).  Phase lengths
    P1={nP1} RIP={nRIP} STPI={nSTPI} STPO={nSTPO} RET={nRET} FIN={nFIN};
    bootstrap {BT} steps to Cc {P0}.

    Axiom footprint: [functional_extensionality_dep] only. *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded
     FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From BBB4.Counters Require Import WTape LapGlue MonoCounter ILCounter JpCounter.
Import ListNotations.

Definition mk_{ID} (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** The machine {SPEC}. *)
Definition tm_{ID} : TM := fun q s => match q, s with
{TMBODY} end.

(** Its mirror {MSPEC}: the same counter, grown leftward. *)
Definition tmm_{ID} : TM := fun q s => match q, s with
{TMMBODY} end.

Lemma mirror_ok_{ID} : mirror_tm tm_{ID} = tmm_{ID}.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro s; destruct q, s; reflexivity.
Qed.

Definition Cc_{ID} (p : positive) : cconf := ({EST}, (Jp p ++ [S0], S0, [])).

(* --- the lap unit windows (derived by simulation, closed by reflexivity) --- *)
Lemma U_P1_{ID} : wsteps true true tmm_{ID} {nP1} ({EST},([S1],S0,[]))
  = Some ({QA},([],S1,[S0])). Proof. reflexivity. Qed.
Lemma U_RIP_{ID} : wsteps true true tmm_{ID} {nRIP} ({QA},([S0;S1],S1,[]))
  = Some ({QA},([],S1,[{B};{B}])). Proof. reflexivity. Qed.
Lemma U_STPI_{ID} : wsteps true true tmm_{ID} {nSTPI} ({QA},([S1;S1],S1,[]))
  = Some ({QB},([S0;S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_STPO_{ID} : wsteps false true tmm_{ID} {nSTPO} ({QA},([S0],S1,[]))
  = Some ({QB},([S0],S1,[{B};{B}])). Proof. reflexivity. Qed.
Lemma U_RET_{ID} : wsteps true true tmm_{ID} {nRET} ({QB},([],S1,[{B}]))
  = Some ({QB},([S1],S1,[])). Proof. reflexivity. Qed.
Lemma U_FIN_{ID} : wsteps true true tmm_{ID} {nFIN} ({QB},([],S1,[S0]))
  = Some ({EST},([S1],S0,[])). Proof. reflexivity. Qed.

(* --- transported phases (framing = each unit's bl/br) --- *)
Lemma phP1_{ID} : forall L R,
  csteps tmm_{ID} {nP1} ({EST},(S1::L,S0,R)) = Some ({QA},(L,S1,S0::R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_P1_{ID}). Qed.
Lemma phRIP_{ID} : forall k L R,
  csteps tmm_{ID} ({nRIP}*k) ({QA},(rep [S0;S1] k ++ L,S1,R))
  = Some ({QA},(L,S1,rep [{B};{B}] k ++ R)).
Proof. intros. pose proof (cycL _ _ _ _ _ _ _ U_RIP_{ID} k L R) as H;
  cbn [app] in H; exact H. Qed.
Lemma phSTPI_{ID} : forall L R,
  csteps tmm_{ID} {nSTPI} ({QA},(S1::S1::L,S1,R)) = Some ({QB},(S0::S1::L,S1,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STPI_{ID}). Qed.
Lemma phSTPO_{ID} : forall R,
  csteps tmm_{ID} {nSTPO} ({QA},([S0],S1,R)) = Some ({QB},([S0],S1,{B}::{B}::R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPO_{ID}). Qed.
Lemma phRET_{ID} : forall k L R,
  csteps tmm_{ID} ({nRET}*k) ({QB},(L,S1,rep [{B}] k ++ R))
  = Some ({QB},(rep [S1] k ++ L,S1,R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U_RET_{ID} k L R). Qed.
Lemma phFIN_{ID} : forall L R,
  csteps tmm_{ID} {nFIN} ({QB},(L,S1,S0::R)) = Some ({EST},(S1::L,S0,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FIN_{ID}). Qed.

(** The exact lap: from the anchor at p to the anchor at p+1. *)
Lemma lap_exact_{ID} : forall p, exists n c',
  csteps tmm_{ID} n (Cc_{ID} p) = Some c' /\ c' = Cc_{ID} (Pos.succ p) /\ 0 < n.
Proof.
  intros p. pose proof (Pos2Nat.is_pos p) as Hpos.
  destruct (cview p) as [j oq] eqn:Ecv. unfold Cc_{ID}.
  destruct oq as [q0|].
  - destruct (cview_some_J p j q0 Ecv) as (HJp & HJs).
    destruct (Jp_head q0) as (iq & Hiq).
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
    + rewrite HJs, Hiq, rep_dbl. cbn [Nat.mul].
      rewrite rep_slide, <- !app_assoc. reflexivity.
    + lia.
  - destruct j as [|j'].
    {{ exfalso. destruct p; simpl in Ecv;
       [destruct (cview p); discriminate|discriminate|discriminate]. }}
    destruct (cview_none_J p j' Ecv) as (HJp & HJs).
    do 2 eexists. split; [|split].
    + rewrite HJp, pair_rot.
      eapply csteps_chain. {{ apply phP1_{ID}. }}
      eapply csteps_chain. {{ apply phRIP_{ID}. }}
      eapply csteps_chain. {{ apply phSTPO_{ID}. }}
      change ({B} :: {B} :: rep [{B};{B}] j' ++ [S0])
        with (rep [{B};{B}] (S j') ++ [S0]).
      rewrite rep_dbl.
      eapply csteps_chain. {{ apply (phRET_{ID} (2*(S j'))). }}
      apply phFIN_{ID}.
    + rewrite HJs, rep_dbl. cbn [Nat.mul].
      rewrite rep_slide, <- !app_assoc. reflexivity.
    + lia.
Qed.

Lemma lap_{ID} : forall p, exists n c',
  csteps tmm_{ID} n (Cc_{ID} p) = Some c' /\
  lift c' = lift (Cc_{ID} (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (lap_exact_{ID} p) as (n & c' & Hr & Hc & Hn).
  exists n, c'. split; [exact Hr | split; [rewrite Hc; reflexivity | exact Hn]].
Qed.

Lemma boot_{ID} : exists t0, stepn tmm_{ID} t0 InitES = Some (lift (Cc_{ID} {P0})).
Proof.
  exists {BT}.
  assert (H : match csteps tmm_{ID} {BT} c0 with
              | Some c => ceqb c (Cc_{ID} {P0}) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tmm_{ID} {BT} c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.
'''

VA = r'''
(** The log-rare state {QV}: reached inside the overflow stop, so the anchor
    walks forward (well-founded on [tovf]) until the counter is all ones. *)
Lemma U_VA{TAG}_{ID} : wsteps false true tmm_{ID} {NVA} ({QA},([S0],S1,[]))
  = Some ({QV},({LV},{HV},{RV})). Proof. reflexivity. Qed.
Lemma phVA{TAG}_{ID} : forall R,
  csteps tmm_{ID} {NVA} ({QA},([S0],S1,R)) = Some ({QV},({LV},{HV},{RVR})).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_VA{TAG}_{ID}). Qed.

Lemma vis{TAG}_{ID} : forall p, exists k c,
  csteps tmm_{ID} k (Cc_{ID} p) = Some c /\ fst c = {QV}.
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.
  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    {{ intro H0. destruct (tovf0_allones p H0) as (jj & Hjj).
       rewrite Hjj in Ecv; discriminate. }}
    destruct (lap_exact_{ID} p) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ p)) (ltac:(rewrite tovf_succ by lia; lia))
                 (Pos.succ p) eq_refl) as (k & c & Hk & Hq).
    exists (n + k), c. rewrite csteps_add, Hrun. exact (conj Hk Hq).
  - destruct j as [|j'].
    {{ exfalso. destruct p; simpl in Ecv;
       [destruct (cview p); discriminate|discriminate|discriminate]. }}
    destruct (cview_none_J p j' Ecv) as (HJp & _).
    unfold Cc_{ID}. eexists. eexists. split.
    * rewrite HJp, pair_rot.
      eapply csteps_chain. {{ apply phP1_{ID}. }}
      eapply csteps_chain. {{ apply phRIP_{ID}. }}
      apply phVA{TAG}_{ID}.
    * reflexivity.
Qed.
'''

TAIL = r'''
Lemma vis_{ID} : forall p q, exists k c,
  csteps tmm_{ID} k (Cc_{ID} p) = Some c /\ fst c = q.
Proof.
  intros p q. destruct (Jp_head p) as (w & Hw). unfold Cc_{ID}. destruct q.
{BRANCHES}
Qed.

Lemma nqhm_{ID} : NeverQuasiHaltsSt tmm_{ID}.
Proof.
  apply (glue_neverqh tmm_{ID} Cc_{ID} {P0}).
  - exact boot_{ID}.
  - intros p _. apply lap_{ID}.
  - intros p q _. apply vis_{ID}.
Qed.

Theorem nqh_{ID} : NeverQuasiHaltsSt tm_{ID}.
Proof. apply (mirror_never_qh tm_{ID}). rewrite mirror_ok_{ID}. exact nqhm_{ID}. Qed.

Theorem nonhalt_{ID} : NonHalt tm_{ID}.
Proof. apply never_qh_nonhalt, nqh_{ID}. Qed.
'''


def render(spec, mspec, E, ph, u, qA, qB, b, p0, bt, routes, va):
    ID = ident(spec)
    f = dict(ID=ID, SPEC=spec, MSPEC=mspec, EST=ST[E], QA=ST[qA], QB=ST[qB],
             B=sy(b), P0=p0, BT=bt,
             nP1=ph['P1'], nRIP=ph['RIP'], nSTPI=ph['STPI'],
             nSTPO=ph['STPO'], nRET=ph['RET'], nFIN=ph['FIN'],
             TMBODY=tm_body(spec, 'mk_%s' % ID),
             TMMBODY=tm_body(mspec, 'mk_%s' % ID))
    out = [HEAD.format(**f)]

    # --- the vis_A-style lemmas, one per state routed through the overflow stop
    for q, (nva, lv, hv, rv) in sorted(va.items()):
        out.append(VA.format(TAG=LAB[q], QV=ST[q], NVA=nva,
                             LV=lst(lv), HV=sy(hv), RV=lst(rv),
                             RVR=cons(rv, 'R'), **f))

    # --- the per-state prefix lemmas + the vis_T branches
    pre, branches = [], []
    for q in range(4):
        r = routes[q]
        if r['kind'] == 'edge':
            branches.append("  - exists 0. eexists. split; reflexivity.")
        elif r['kind'] == 'va':
            branches.append("  - apply (vis%s_%s p)." % (LAB[q], ID))
        else:
            d, k = r['depth'], r['k']
            nm = 'phV%s_%s' % (LAB[q], ID)
            lhs = {0: 'L', 1: 'S1::L', 2: 'S1::x::L'}[d]
            binder = 'forall x L,' if d == 2 else 'forall L,'
            pre.append(
                "Lemma %s : %s\n  csteps tmm_%s %d (%s,(%s,S0,[]))\n"
                "  = Some (%s,(%s,%s,%s)).\nProof. reflexivity. Qed.\n"
                % (nm, binder, ID, k, ST[E], lhs, ST[q],
                   cons(r['left'], 'L'), sy(r['head']), lst(r['right'])))
            if d == 2:
                branches.append(
                    "  - rewrite Hw. destruct w as [|x w'].\n"
                    "    + exists %d. eexists. split;\n"
                    "      [ vm_compute; reflexivity | reflexivity ].\n"
                    "    + exists %d. eexists. split.\n"
                    "      * change ((S1 :: x :: w') ++ [S0])\n"
                    "          with (S1 :: x :: (w' ++ [S0])). apply %s.\n"
                    "      * reflexivity." % (k, k, nm))
            elif d == 1:
                branches.append(
                    "  - exists %d. eexists. rewrite Hw.\n"
                    "    split; [apply %s | reflexivity]." % (k, nm))
            else:
                branches.append(
                    "  - exists %d. eexists. split; [apply %s | reflexivity]."
                    % (k, nm))
    if pre:
        out.append("\n(* --- determined prefixes from the anchor --- *)\n"
                   + '\n'.join(pre))
    out.append(TAIL.format(BRANCHES='\n'.join(branches), **f))
    return ''.join(out)


# ------------------------------------------------------------------ pipeline --
def build(spec, fpr):
    if fpr.get('cls') != 'COUNTER':
        raise DeriveError("no counter fingerprint")
    if fpr['growth'] != 'R':
        raise DeriveError("growth=%s: not a mirror-route machine" % fpr['growth'])
    if fpr['enc'] != 'Jp':
        raise DeriveError("encoding %s unsupported (Jp only)" % fpr['enc'])
    mspec = mirror_spec(spec)
    E = LAB.index(fpr['edge'])
    encf = ENC[fpr['enc']]
    raw = Raw(mspec)
    ph = solve_phases(raw, E, encf)
    u = validate(mspec, ph, E, encf)
    msgs, qA, qB, b = shape_check(u, E)
    if msgs:
        raise DeriveError("; ".join(msgs))
    bt, p0 = boot_probe(mspec, E, encf)

    pres = prefix_states(mspec, E)
    stpo = stpo_states(mspec, qA, ph['STPO'])
    routes, va = {}, {}
    for q in range(4):
        if q == E:
            routes[q] = dict(kind='edge')
        elif q in pres and pres[q][0] > 0:
            k, d, l, h, r = pres[q]
            routes[q] = dict(kind='pre', k=k, depth=d, left=l, head=h, right=r)
        elif q in stpo:
            nva, lv, hv, rv = stpo[q]
            va[q] = (nva, lv, hv, rv)
            routes[q] = dict(kind='va')
        else:
            raise DeriveError("state %s unreachable by any derived route"
                              % ST[q])
    return dict(spec=spec, mspec=mspec, E=E, ph=ph, u=u, qA=qA, qB=qB, b=b,
                p0=p0, bt=bt, routes=routes, va=va)


def coqc(path, thm, quiet=True):
    env = dict(os.environ, OPAMROOT='/root/.opam')
    cmd = ['coqc', '-native-compiler', 'no', '-Q', 'theories', 'BBB4', path]
    r = subprocess.run(cmd, cwd=REPO, env=env, capture_output=True, text=True)
    if r.returncode:
        return False, (r.stderr or r.stdout)[-4000:]
    mod = os.path.splitext(os.path.basename(path))[0]
    chk = os.path.join(REPO, 'tools', 'counters', 'axck_%s.v' % mod)
    with open(chk, 'w') as f:
        f.write("From BBB4.Machines.Counters Require Import %s.\n"
                "Print Assumptions %s.\n" % (mod, thm))
    r2 = subprocess.run(['coqc', '-native-compiler', 'no', '-Q', 'theories',
                         'BBB4', chk], cwd=REPO, env=env,
                        capture_output=True, text=True)
    for ext in ('.vo', '.vok', '.vos', '.glob', '.v'):
        try:
            os.remove(chk[:-2] + ext)
        except OSError:
            pass
    if r2.returncode:
        return False, (r2.stderr or r2.stdout)[-4000:]
    ax = r2.stdout.strip()
    if ax.startswith('Closed under the global context'):
        return True, ax
    names = set()
    for ln in ax.splitlines():
        if not ln or ln[0].isspace() or ln.strip() == 'Axioms:':
            continue
        names.add(ln.split()[0].rstrip(':').split('.')[-1])
    ok = bool(names) and names <= {'functional_extensionality_dep'}
    return ok, ' | '.join(sorted(names)) or ax[:200]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('specs', nargs='*')
    ap.add_argument('--list')
    ap.add_argument('--fp', default=DEFAULT_FP)
    ap.add_argument('--emit', action='store_true')
    ap.add_argument('--check', action='store_true')
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--outdir',
                    default=os.path.join(REPO, 'theories', 'Machines', 'Counters'))
    a = ap.parse_args()

    specs = list(a.specs)
    if a.list:
        specs += [x.strip() for x in open(a.list) if x.strip()]
    fp = {}
    with open(a.fp) as f:
        for line in f:
            r = json.loads(line)
            fp[r['m']] = r
    if a.limit:
        specs = specs[:a.limit]

    nok = nfail = ncoq = 0
    for spec in specs:
        try:
            d = build(spec, fp.get(spec, {}))
        except (DeriveError, AssertionError, Wall, KeyError, ZeroDivisionError) as e:
            print("FAIL   %s : %s" % (spec, e))
            nfail += 1
            continue
        nok += 1
        ph = d['ph']
        print("DERIVE %s edge=%s qA=%s qB=%s b=%s p0=%d boot=%d "
              "n=(P1 %d,RIP %d,STPI %d,STPO %d,RET %d,FIN %d) routes=%s"
              % (spec, LAB[d['E']], LAB[d['qA']], LAB[d['qB']], sy(d['b']),
                 d['p0'], d['bt'], ph['P1'], ph['RIP'], ph['STPI'],
                 ph['STPO'], ph['RET'], ph['FIN'],
                 ''.join(d['routes'][q]['kind'][0] for q in range(4))))
        if not a.emit:
            continue
        ID = ident(spec)
        path = os.path.join(a.outdir, 'ILCM_%s.v' % ID)
        with open(path, 'w') as f:
            f.write(render(spec, d['mspec'], d['E'], ph, d['u'], d['qA'],
                           d['qB'], d['b'], d['p0'], d['bt'], d['routes'],
                           d['va']))
        print("EMIT   %s" % path)
        if a.check:
            ok, msg = coqc(path, 'nqh_%s' % ID)
            print("%s  %s\n       %s" % ("COQ-OK" if ok else "COQ-BAD",
                                         path, msg.replace('\n', '\n       ')))
            ncoq += bool(ok)
    print("== derived %d, failed %d, coq-clean %d" % (nok, nfail, ncoq))


if __name__ == '__main__':
    main()
