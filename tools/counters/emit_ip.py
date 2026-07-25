#!/usr/bin/env python3
"""UNTRUSTED emitter for comb-free interleaved counters under the DIRECT
interleave encoding [ILCounter.Ip].

Clones theories/Machines/Counters/ILC_1RB0RC_0LA____0LD1RA_1RC1LD.v, the
wave-9 reference board.  That board is the wave-8 Interleave_TGT template with
four previously hard-coded things turned into parameters:

  enc   Ip (this emitter) vs Jp (emit_interleave.py).  Under Ip the carry
        region reads [rep [S1;S1] j] and is rewritten to [rep [S1;S0] j]; under
        Jp it is the other way round.  So the ripple pair, the interior stop's
        flip direction, the return unit's WIDTH (2 cells, not 1) and the return
        COUNT (j, not 2j) all swap with the encoding.
  head  the frontier cell, S0 or S1.
  tail  the fixed suffix under the counter, e.g. [] or [S1].
  far   the anchor's far side, [] or [S0].  A blank CELL is not the empty
        LIST: when the closing phase steps one cell past the frontier, [S0]
        keeps that excursion inside an ordinary closed window while [] forces
        an open-right transport.  [glue_neverqh] takes an arbitrary anchor, so
        carrying the blank costs nothing.

Everything here is UNTRUSTED: a wrong constant cannot mis-prove anything, it
fails to typecheck.  The Coq kernel re-checks every emitted board.

Usage
  emit_ip.py --list FILE [--emit] [--json OUT]
  emit_ip.py SPEC... [--emit]
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

from executor import Exec, Wall                                   # noqa: E402
from emit_qh import (anchor_candidates, Raw, LAB, ST, SYM, ENC,   # noqa: E402
                     carry, mach_id, coq_table, DeriveError)

OUTDIR = os.path.join(REPO, 'theories', 'Machines', 'Counters')


def mirror_spec(spec):
    """mirror_tm at the level of the SPEC string: flip every move direction."""
    out = []
    for part in spec.split('_'):
        t = ''
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            t += e if e == '---' else e[0] + ('L' if e[1] == 'R' else 'R') + e[2]
        out.append(t)
    return '_'.join(out)
FARS = ([0], [])
MAXN = 10


# ------------------------------------------------------------------ traces ---
def lap_len(spec, E, encf, head, tail, far, m, maxsteps=200000):
    raw = Raw(spec)
    cfg = (E, encf(m) + list(tail), head, list(far))
    tgt = (E, encf(m + 1) + list(tail), head, list(far))
    for n in range(1, maxsteps):
        cfg = raw.step(cfg)
        if cfg is None:
            return None
        if cfg == tgt:
            return n
    return None


def affine(pts):
    js = sorted(pts)
    if len(js) < 2:
        return None
    j0, j1 = js[0], js[1]
    n0, n1 = pts[j0], pts[j1]
    if (n1 - n0) % (j1 - j0):
        return None
    b = (n1 - n0) // (j1 - j0)
    a = n0 - b * j0
    return (a, b) if all(pts[j] == a + b * j for j in js) else None


def m_int(j):
    """Smallest value whose cview is (j, Some _): j low ones under a clear bit."""
    return (1 << (j + 1)) + (1 << j) - 1 if j else 2


def profile(spec, E, encf, head, tail, far):
    inter, over = {}, {}
    for j in range(0, 4):
        n = lap_len(spec, E, encf, head, tail, far, m_int(j))
        if n is None:
            return None
        inter[j] = n
    for j in range(2, 5):
        n = lap_len(spec, E, encf, head, tail, far, (1 << j) - 1)
        if n is None:
            return None
        over[j] = n
    ai, ao = affine(inter), affine(over)
    return None if (ai is None or ao is None) else (ai, ao)


# ------------------------------------------------- windowed-run primitives ---
def conc(ex, cfg, bl, br, n, lw, rw):
    q, l, h, r = cfg
    lw = len(l) if lw is None else lw
    rw = len(r) if rw is None else rw
    if lw > len(l) or rw > len(r):
        raise Wall('window deeper than tape')
    out = ex.wsteps(bl, br, q, l[:lw], h, r[:rw], n)
    ent = (q, tuple(l[:lw]), h, tuple(r[:rw]))
    ext = (out[0], tuple(out[1]), out[2], tuple(out[3]))
    return (out[0], out[1] + l[lw:], out[2], out[3] + r[rw:]), (ent, ext)


def cycl(ex, cfg, ulen, P, k):
    q, l, h, r = cfg
    if k == 0:
        # no unit to check: an even value has no carry pair to ripple
        return cfg, ((q, (), h, ()), (q, (), h, ()))
    if ulen > len(l):
        raise Wall('cycL window')
    u = l[:ulen]
    out = ex.wsteps(True, True, q, u, h, [], P)
    if not (out[0] == q and out[2] == h and out[1] == []):
        raise Wall('not a cycL unit')
    w = out[3]
    if k and l[:ulen * k] != u * k:
        raise Wall('left is not u^k')
    return ((q, l[ulen * k:], h, w * k + r),
            ((q, tuple(u), h, ()), (q, (), h, tuple(w))))


def cycr(ex, cfg, ulen, P, k):
    q, l, h, r = cfg
    if k == 0:
        return cfg, ((q, (), h, ()), (q, (), h, ()))
    if ulen > len(r):
        raise Wall('cycR window')
    u = r[:ulen]
    out = ex.wsteps(True, True, q, [], h, u, P)
    if not (out[0] == q and out[2] == h and out[3] == []):
        raise Wall('not a cycR unit')
    w = out[1]
    if k and r[:ulen * k] != u * k:
        raise Wall('right is not u^k')
    return ((q, w * k + l, h, r[ulen * k:]),
            ((q, (), h, tuple(u)), (q, tuple(w), h, ())))


def replay_int(ex, E, encf, head, tail, far, m, j, s):
    cfg = (E, encf(m) + list(tail), head, list(far))
    U = {}
    cfg, U['P1'] = conc(ex, cfg, True, True, s['nP1'], 1, 0)
    ndep = len(cfg[3]) - len(far)
    cfg, U['RIP'] = cycl(ex, cfg, 2, s['nRIP'], j)
    cfg, U['STPI'] = conc(ex, cfg, True, True, s['nSTP'], 1, 0)
    k = len(cfg[3]) - len(far) - ndep
    if k < 0 or k % 2:
        raise Wall('return count')
    cfg, U['RET'] = cycr(ex, cfg, 2, s['nRET'], k // 2)
    U['kint'] = k // 2
    cfg, U['FINI'] = conc(ex, cfg, True, True, s['nFIN'], 0, None)
    return cfg, U


def replay_ov(ex, E, encf, head, tail, far, m, j, s):
    cfg = (E, encf(m) + list(tail), head, list(far))
    U = {}
    cfg, _ = conc(ex, cfg, True, True, s['nP1'], 1, 0)
    cfg, _ = cycl(ex, cfg, 2, s['nRIP'], j - 1)
    cfg, U['STPO'] = conc(ex, cfg, False, True, s['nSTPO'], None, 0)
    k = len(cfg[3]) - len(far)
    if k < 0 or k % 2:
        raise Wall('overflow return count')
    cfg, U['RET2'] = cycr(ex, cfg, 2, s['nRET'], k // 2)
    U['kov'] = k // 2
    cfg, U['FINO'] = conc(ex, cfg, True, False, s['nFINO'], 0, None)
    return cfg, U


def derive(spec, E, encf, head, tail, far, ai, ao):
    """Fit the step counts, then confirm by exact symbolic replay."""
    a, b = ai
    ao0, _ = ao
    ex = Exec(spec)
    JI, KO = 3, 4
    tgt_i = (E, encf(m_int(JI) + 1) + list(tail), head, list(far))
    tgt_o = (E, encf((1 << KO)) + list(tail), head, list(far))
    for nP1 in range(1, MAXN):
        for nRIP in range(1, MAXN):
            nRET = b - nRIP
            if nRET < 1:
                continue
            for nSTP in range(1, MAXN + 4):
                nFIN = a - nP1 - nSTP
                if nFIN < 1:
                    continue
                s = dict(nP1=nP1, nRIP=nRIP, nSTP=nSTP, nRET=nRET, nFIN=nFIN)
                try:
                    cfg, U = replay_int(ex, E, encf, head, tail, far,
                                        m_int(JI), JI, s)
                except (Wall, KeyError, IndexError):
                    continue
                if cfg != tgt_i or U['kint'] != JI:
                    continue
                # ao(j) = nP1 + nRIP*(j-1) + nSTPO + nRET*j + nFINO
                for nSTPO in range(1, MAXN + 4):
                    nFINO = ao0 - nP1 + nRIP - nSTPO
                    if nFINO < 1:
                        continue
                    s2 = dict(s, nSTPO=nSTPO, nFINO=nFINO)
                    try:
                        cfg2, UO = replay_ov(ex, E, encf, head, tail, far,
                                             (1 << KO) - 1, KO, s2)
                    except (Wall, KeyError, IndexError):
                        continue
                    if cfg2 != tgt_o or UO['kov'] != KO:
                        continue
                    U.update(UO)
                    return s2, U
    raise DeriveError('no skeleton fits both lap branches')


def validate(spec, E, encf, head, tail, far, s, hi=100):
    """Differential check of the symbolic lap against the raw lap, every m."""
    ex = Exec(spec)
    n = 0
    for m in range(2, hi):
        j, ov = carry(m)
        raw = lap_len(spec, E, encf, head, tail, far, m)
        if raw is None:
            raise DeriveError('raw lap does not close at m=%d' % m)
        tgt = (E, encf(m + 1) + list(tail), head, list(far))
        if ov:
            cfg, _ = replay_ov(ex, E, encf, head, tail, far, m, j, s)
            got = (s['nP1'] + s['nRIP'] * (j - 1) + s['nSTPO']
                   + s['nRET'] * j + s['nFINO'])
        else:
            cfg, _ = replay_int(ex, E, encf, head, tail, far, m, j, s)
            got = (s['nP1'] + s['nRIP'] * j + s['nSTP']
                   + s['nRET'] * j + s['nFIN'])
        if cfg != tgt:
            raise DeriveError('m=%d: symbolic lap misses the next anchor' % m)
        if got != raw:
            raise DeriveError('m=%d: symbolic %d != raw %d' % (m, got, raw))
        n += 1
    return n


def shape_check(U, tail, far):
    """The emitted proof script needs exactly these shapes (Ip algebra)."""
    msgs = []
    (P1e, P1x) = U['P1']
    (Re, Rx) = U['RIP']
    (Se, Sx) = U['STPI']
    (Te, Tx) = U['RET']
    (Oe, Ox) = U['STPO']
    if P1e[1] != (1,) or P1e[3] != () or P1x[1] != ():
        msgs.append('P1 %s -> %s is not [S1]|[] -> []' % (P1e, P1x))
    if Re[1] != (1, 1):
        msgs.append('ripple pair %s is not [S1;S1] (Ip)' % (Re[1],))
    if Se[1] != (0,) or Sx[1] != (1,):
        msgs.append('interior stop %s -> %s is not [S0] -> [S1]' % (Se[1], Sx[1]))
    if Tx[1] != (0, 1):
        msgs.append('return deposit %s is not [S0;S1]' % (Tx[1],))
    if Te[3] != Rx[3]:
        msgs.append('return consumes %s but ripple deposits %s' % (Te[3], Rx[3]))
    if Oe[1] != tuple(tail):
        msgs.append('overflow stop entry left %s is not the tail %s'
                    % (Oe[1], tail))
    if list(Ox[3]) + list(Rx[3]) * 0 and len(Ox[3]) + len(P1x[3]) != 2:
        msgs.append('overflow deposit %s + P1 deposit %s must fill one pair'
                    % (Ox[3], P1x[3]))
    return msgs


def boot_probe(spec, E, encf, head, tail, far, p0, maxT=40000):
    raw = Raw(spec)

    def strip(l):
        l = list(l)
        while l and l[-1] == 0:
            l.pop()
        return l
    tgt = (E, strip(encf(p0) + list(tail)), head, strip(far))
    cfg = (0, [], 0, [])
    for t in range(maxT):
        q, l, h, r = cfg
        if (q, strip(l), h, strip(r)) == tgt:
            return t
        cfg = raw.step(cfg)
        if cfg is None:
            raise DeriveError('halts during bootstrap at t=%d' % t)
    raise DeriveError('no bootstrap to Cc(%d)' % p0)


# ---------------------------------------------------------------- rendering --
def clist(xs):
    return "[" + ";".join(SYM[x] for x in xs) + "]"


def ccons(xs, t):
    return "".join("%s::" % SYM[x] for x in xs) + t if xs else t


def cwin(c):
    q, l, h, r = c
    return "(%s,(%s,%s,%s))" % (ST[q], clist(l), SYM[h], clist(r))


HEAD = r'''(** * ILC_@ID@: comb-free interleaved binary counter, machine @SPEC@.

    Auto-emitted by tools/counters/emit_ip.py (UNTRUSTED emitter; the Coq
    kernel re-checks every line below).  Left-growth counter under the DIRECT
    interleave encoding [Ip] (ILCounter.v), anchored at

      Cc p = (@EDGE@, (Ip p ++ @TAIL@, @AHEAD@, @FAR@))

    -- the counter on the LEFT list nearest-first, the frontier cell @AHEAD@
    under the head, and a far side of @FAR@ (a blank CELL, not the empty list:
    the closing phase steps one cell past the frontier, and carrying the blank
    keeps that excursion inside a closed window).

    One lap Cc p -> Cc (p+1) is a single sweep: P1 prologue; RIP leftward carry
    ripple over the low set-bit pairs (cycL, @NRIP@ steps per pair); STPI
    interior stop / STPO overflow stop off the deep-left edge; RET rightward
    return (cycR, @NRET@ steps per pair); FIN close.  Under [Ip] the ripple
    reads [rep [S1;S1] j] and the return writes [rep [S0;S1] j], so the return
    count is j -- under [Jp] the pairs swap and it is 2j.

    Step counts were derived by simulation and the decomposition was
    differentially validated against the raw simulator on BOTH cview branches
    for p = 2..99 (step counts AND exact configurations).

    Axiom footprint: [functional_extensionality_dep] (via CTape.lift). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape LapGlue MonoCounter ILCounter JpCounter.
Import ListNotations.

Definition mk_@ID@ (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_@ID@.

@TMDEF@
Definition Cc_@ID@ (p : positive) : cconf := (@EDGE@, (Ip p ++ @TAIL@, @AHEAD@, @FAR@)).
Local Notation Cc := Cc_@ID@.

(** ** The lap unit windows (each closed by [reflexivity]) *)
Lemma U_P1_@ID@ : wsteps true true tm @NP1@ @P1E@ = Some @P1X@. Proof. reflexivity. Qed.
Lemma U_RIP_@ID@ : wsteps true true tm @NRIP@ @RIPE@ = Some @RIPX@. Proof. reflexivity. Qed.
Lemma U_STPI_@ID@ : wsteps true true tm @NSTP@ @STPIE@ = Some @STPIX@. Proof. reflexivity. Qed.
Lemma U_STPO_@ID@ : wsteps false true tm @NSTPO@ @STPOE@ = Some @STPOX@. Proof. reflexivity. Qed.
Lemma U_RET_@ID@ : wsteps true true tm @NRET@ @RETE@ = Some @RETX@. Proof. reflexivity. Qed.
Lemma U_FINI_@ID@ : wsteps true true tm @NFIN@ @FINIE@ = Some @FINIX@. Proof. reflexivity. Qed.
Lemma U_FINO_@ID@ : wsteps true false tm @NFINO@ @FINOE@ = Some @FINOX@. Proof. reflexivity. Qed.

(** ** Transported phases (framing = each unit's bl/br) *)
Lemma phP1_@ID@ : forall L R, csteps tm @NP1@ (@EDGE@,(S1::L,@AHEAD@,R)) = Some (@QR@,(L,@HR@,@P1DEP@R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_P1_@ID@). Qed.
Lemma phRIP_@ID@ : forall k L R, csteps tm (@NRIP@*k) (@QR@,(rep [S1;S1] k ++ L,@HR@,R)) = Some (@QR@,(L,@HR@,rep @RIPDEP@ k ++ R)).
Proof. intros. pose proof (cycL _ _ _ _ _ _ _ U_RIP_@ID@ k L R) as H; cbn [app] in H; exact H. Qed.
Lemma phSTPI_@ID@ : forall L R, csteps tm @NSTP@ (@QR@,(S0::L,@HR@,R)) = Some (@QT@,(S1::L,@HT@,R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_STPI_@ID@). Qed.
Lemma phSTPO_@ID@ : forall R, csteps tm @NSTPO@ (@QR@,(@TAIL@,@HR@,R)) = Some (@QT@,(@STPOL@,@HT@,@STPODEP@R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R U_STPO_@ID@). Qed.
Lemma phRET_@ID@ : forall k L R, csteps tm (@NRET@*k) (@QT@,(L,@HT@,rep @RIPDEP@ k ++ R)) = Some (@QT@,(rep [S0;S1] k ++ L,@HT@,R)).
Proof. intros. exact (cycR _ _ _ _ _ _ U_RET_@ID@ k L R). Qed.
Lemma phFINI_@ID@ : forall L R, csteps tm @NFIN@ (@QT@,(L,@HT@,@FINIR@R)) = Some (@EDGE@,(S1::L,@AHEAD@,@FARC@R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R U_FINI_@ID@). Qed.
Lemma phFINO_@ID@ : forall L, csteps tm @NFINO@ (@QT@,(L,@HT@,@FAR@)) = Some (@EDGE@,(S1::L,@AHEAD@,@FAR@)).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L U_FINO_@ID@). Qed.

(** After the overflow stop the deposited run is one cell short of a whole
    pair; fold the prologue's deposit back in so the return cycle applies. *)
Lemma ov_R_@ID@ : forall j, @STPODEP@rep @RIPDEP@ j ++ @P1DEP@@FAR@ = rep @RIPDEP@ (S j) ++ @FAR@.
Proof.
  induction j.
  - reflexivity.
  - cbn [rep] in *. rewrite <- !app_assoc in *. cbn [app] in *.
    f_equal. f_equal. exact IHj.
Qed.

(** ** The lap *)
Lemma lap_int_@ID@ : forall p j q0, cview p = (j, Some q0) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intros p j q0 Ecv. unfold Cc_@ID@.
  destruct (cview_some_I p j q0 Ecv) as (HIp & HIs).
  do 2 eexists. split; [|split].
  - rewrite HIp, <- app_assoc.
    change (rep [S1;S1] j ++ (S1 :: S0 :: Ip q0) ++ @TAIL@)
      with (rep [S1;S1] j ++ [S1] ++ (S0 :: Ip q0 ++ @TAIL@)).
    rewrite app_assoc, pair_rot.
    eapply csteps_chain. { apply phP1_@ID@. }
    eapply csteps_chain. { apply phRIP_@ID@. }
    eapply csteps_chain. { apply phSTPI_@ID@. }
    eapply csteps_chain. { apply (phRET_@ID@ j). }
    apply phFINI_@ID@.
  - rewrite HIs, <- app_assoc.
    change ((S1 :: S1 :: Ip q0) ++ @TAIL@) with ([S1] ++ (S1 :: Ip q0 ++ @TAIL@)).
    rewrite app_assoc, pair_rot. reflexivity.
  - lia.
Qed.

Lemma lap_ov_@ID@ : forall p j', cview p = (S j', None) ->
  exists n c', csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intros p j' Ecv. unfold Cc_@ID@.
  destruct (cview_none_I p j' Ecv) as (HIp & HIs).
  do 2 eexists. split; [|split].
  - rewrite HIp, pair_rot.
    eapply csteps_chain. { apply phP1_@ID@. }
    eapply csteps_chain. { apply phRIP_@ID@. }
    eapply csteps_chain. { apply phSTPO_@ID@. }
    rewrite ov_R_@ID@.
    eapply csteps_chain. { apply (phRET_@ID@ (S j')). }
    apply phFINO_@ID@.
  - rewrite HIs, pair_rot. reflexivity.
  - lia.
Qed.

Lemma lap_exact_@ID@ : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ c' = Cc (Pos.succ p) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - exact (lap_int_@ID@ p j q0 Ecv).
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv;
        [destruct (cview p); discriminate|discriminate|discriminate]. }
    exact (lap_ov_@ID@ p j' Ecv).
Qed.

Lemma lap_@ID@ : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (lap_exact_@ID@ p) as (n & c' & Hr & Hc & Hn).
  exists n, c'. split; [exact Hr | split; [rewrite Hc; reflexivity | exact Hn]].
Qed.

Lemma boot_@ID@ : exists t0, stepn tm t0 InitES = Some (lift (Cc @P0@)).
Proof.
  exists @BOOT@.
  assert (H : match csteps tm @BOOT@ c0 with Some c => ceqb c (Cc @P0@) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm @BOOT@ c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state is witnessed from one common landmark -- the configuration the
    OVERFLOW close starts from -- reached by well-founded induction on [tovf],
    which strictly decreases along interior laps.  That is what covers the
    log-rare carry states (they fire only inside the overflow close, at
    doubling intervals, so no bounded anchor prefix reaches them). *)
Lemma reach_fino_@ID@ : forall p, exists k L, csteps tm k (Cc p) = Some (@QT@,(L,@HT@,@FAR@)).
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.
  destruct (cview p) as [j oq] eqn:Ecv. destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj). rewrite Hjj in Ecv; discriminate. }
    destruct (lap_int_@ID@ p j q0 Ecv) as (n & c' & Hrun & Hc' & _). subst c'.
    destruct (IH (tovf (Pos.succ p)) (ltac:(rewrite tovf_succ by lia; lia))
                 (Pos.succ p) eq_refl) as (k & L & Hk).
    exists (n + k), L. rewrite csteps_add, Hrun. exact Hk.
  - destruct j as [|j'].
    { exfalso. destruct p; simpl in Ecv;
        [destruct (cview p); discriminate|discriminate|discriminate]. }
    destruct (cview_none_I p j' Ecv) as (HIp & _).
    unfold Cc_@ID@. eexists. eexists.
    rewrite HIp, pair_rot.
    eapply csteps_chain. { apply phP1_@ID@. }
    eapply csteps_chain. { apply phRIP_@ID@. }
    eapply csteps_chain. { apply phSTPO_@ID@. }
    rewrite ov_R_@ID@.
    apply (phRET_@ID@ (S j')).
Qed.

@VISLEMMAS@
Lemma vis_@ID@ : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q. destruct q.
@VISCASES@
Qed.

Lemma nqhm_@ID@ : NeverQuasiHaltsSt tm.
Proof.
  apply (glue_neverqh tm Cc @P0@).
  - exact boot_@ID@.
  - intros p _. apply lap_@ID@.
  - intros p q _. apply vis_@ID@.
Qed.

@CLOSE@'''


def visit_plan(spec, E, encf, head, tail, far, s, U):
    """Which states appear how many steps into the overflow close."""
    ex = Exec(spec)
    KO = 5
    cfg = (E, encf((1 << KO) - 1) + list(tail), head, list(far))
    cfg, _ = conc(ex, cfg, True, True, s['nP1'], 1, 0)
    cfg, _ = cycl(ex, cfg, 2, s['nRIP'], KO - 1)
    cfg, _ = conc(ex, cfg, False, True, s['nSTPO'], None, 0)
    k = (len(cfg[3]) - len(far)) // 2
    cfg, _ = cycr(ex, cfg, 2, s['nRET'], k)
    # cfg is the FINO entry: (QT, L, HT, far).  Walk the close, right-open.
    raw = Raw(spec)
    qT, L0, hT = cfg[0], list(cfg[1]), cfg[2]
    offs, c = {}, (qT, [], hT, list(far))
    for t in range(0, s['nFINO'] + 1):
        offs.setdefault(c[0], (t, (c[0], tuple(c[1]), c[2], tuple(c[3]))))
        if t == s['nFINO']:
            break
        c = raw.step(c)
        if c is None:
            break
    return qT, offs


def emit_source(spec, E, encf, edge, head, tail, far, p0, boot, s, U,
                mirror=False, ospec=None):
    ID = mach_id(ospec or spec)
    (P1e, P1x) = U['P1']
    (Re, Rx) = U['RIP']
    (Se, Sx) = U['STPI']
    (Te, Tx) = U['RET']
    (Oe, Ox) = U['STPO']
    (Fe, Fx) = U['FINI']
    (Ge, Gx) = U['FINO']
    sub = {
        '@ID@': ID, '@SPEC@': (ospec or spec), '@TABLE@': coq_table(spec),
        '@EDGE@': ST[E], '@AHEAD@': SYM[head],
        '@TAIL@': clist(tail), '@FAR@': clist(far), '@FARC@': ccons(far, ''),
        '@P0@': str(p0), '@BOOT@': str(boot),
        '@NP1@': str(s['nP1']), '@NRIP@': str(s['nRIP']), '@NSTP@': str(s['nSTP']),
        '@NSTPO@': str(s['nSTPO']), '@NRET@': str(s['nRET']),
        '@NFIN@': str(s['nFIN']), '@NFINO@': str(s['nFINO']),
        '@P1E@': cwin(P1e), '@P1X@': cwin(P1x),
        '@RIPE@': cwin(Re), '@RIPX@': cwin(Rx),
        '@STPIE@': cwin(Se), '@STPIX@': cwin(Sx),
        '@STPOE@': cwin(Oe), '@STPOX@': cwin(Ox),
        '@RETE@': cwin(Te), '@RETX@': cwin(Tx),
        '@FINIE@': cwin(Fe), '@FINIX@': cwin(Fx),
        '@FINOE@': cwin(Ge), '@FINOX@': cwin(Gx),
        '@QR@': ST[Re[0]], '@HR@': SYM[Re[2]],
        '@QT@': ST[Te[0]], '@HT@': SYM[Te[2]],
        '@P1DEP@': ccons(P1x[3], ''), '@RIPDEP@': clist(Rx[3]),
        '@STPOL@': clist(Ox[1]), '@STPODEP@': ccons(Ox[3], ''),
        '@FINIR@': ccons(Fe[3], ''),
    }
    if mirror:
        # The counter grows RIGHT on the real machine; every proof below runs on
        # the MIRRORED table (where it grows left, matching the template) and
        # Mirror.mirror_never_qh transfers the conclusion back.
        sub['@TMDEF@'] = (
            "(** @SPEC@ -- the real machine (its counter grows RIGHT). *)\n"
            "Definition tm_@ID@ : TM := fun q s => match q, s with\n%s end.\n\n"
            "(** Its mirror %s: the same counter, grown leftward. *)\n"
            "Definition tmm_@ID@ : TM := fun q s => match q, s with\n%s end.\n"
            "Local Notation tm := tmm_@ID@.\n\n"
            "Lemma mirror_ok_@ID@ : mirror_tm tm_@ID@ = tmm_@ID@.\n"
            "Proof.\n"
            "  apply functional_extensionality; intro q;\n"
            "    apply functional_extensionality; intro b; destruct q, b; reflexivity.\n"
            "Qed.\n" % (coq_table(ospec), spec, coq_table(spec)))
        sub['@CLOSE@'] = (
            "Theorem nqh_@ID@ : NeverQuasiHaltsSt tm_@ID@.\n"
            "Proof. apply (mirror_never_qh tm_@ID@). rewrite mirror_ok_@ID@. "
            "exact nqhm_@ID@. Qed.\n\n"
            "Theorem nonhalt_@ID@ : NonHalt tm_@ID@.\n"
            "Proof. apply never_qh_nonhalt, nqh_@ID@. Qed.\n")
    else:
        sub['@TMDEF@'] = ("(** @SPEC@ *)\n"
                          "Definition tm_@ID@ : TM := fun q s => match q, s with\n"
                          "%s end.\nLocal Notation tm := tm_@ID@.\n"
                          % coq_table(spec))
        sub['@CLOSE@'] = (
            "Theorem nqh_@ID@ : NeverQuasiHaltsSt tm_@ID@.\n"
            "Proof. exact nqhm_@ID@. Qed.\n\n"
            "Theorem nonhalt_@ID@ : NonHalt tm_@ID@.\n"
            "Proof. apply never_qh_nonhalt, nqh_@ID@. Qed.\n")
    qT, offs = visit_plan(spec, E, encf, head, tail, far, s, U)
    lemmas, cases = [], []
    for q in range(4):
        if q == E:
            cases.append("  - (* %s : the anchor state *)\n"
                         "    exists 0. eexists. split; reflexivity." % ST[q])
            continue
        if q not in offs:
            raise DeriveError('no visit witness for state %s' % LAB[q])
        t, ext = offs[q]
        if t == 0:
            cases.append("  - (* %s : the overflow-close landmark *)\n"
                         "    destruct (reach_fino_%s p) as (k & L & Hk).\n"
                         "    exists k. eexists. split; [exact Hk | reflexivity]."
                         % (ST[q], ID))
            continue
        nm = "phV%s_%s" % (LAB[q], ID)
        lemmas.append(
            "Lemma %s : forall L, csteps tm %d (%s,(L,%s,%s)) = Some (%s,(%s,%s,%s)).\n"
            "Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L\n"
            "  (ltac:(reflexivity) : wsteps true false tm %d (%s,([],%s,%s)) = Some %s)). Qed."
            % (nm, t, ST[qT], SYM[Te[2]], clist(far), ST[ext[0]],
               ccons(ext[1], 'L'), SYM[ext[2]], clist(ext[3]),
               t, ST[qT], SYM[Te[2]], clist(far), cwin(ext)))
        cases.append(
            "  - (* %s : %d steps into the overflow close *)\n"
            "    destruct (reach_fino_%s p) as (k & L & Hk).\n"
            "    exists (k + %d). eexists. rewrite csteps_add, Hk.\n"
            "    split; [apply %s | reflexivity]." % (ST[q], t, ID, t, nm))
    sub['@VISLEMMAS@'] = ("\n".join(lemmas) + "\n") if lemmas else ""
    sub['@VISCASES@'] = "\n".join(cases)
    src = HEAD
    for _ in range(2):          # twice: @TMDEF@/@CLOSE@ carry nested keys
        for k, v in sorted(sub.items(), key=lambda kv: -len(kv[0])):
            src = src.replace(k, v)
    return src


# ----------------------------------------------------------------- pipeline --
def coqc(path):
    p = subprocess.run(
        ['bash', '-lc', 'cd %s && coqc -native-compiler no -Q theories BBB4 %s'
         % (REPO, path)], capture_output=True, text=True, timeout=1800)
    return p.returncode, p.stdout + p.stderr


def print_assumptions(ID, scratch, mirror=False):
    chk = os.path.join(scratch, 'pa_%s.v' % ID)
    with open(chk, 'w') as f:
        f.write("From BBB4.Machines.Counters Require Import %s_%s.\n"
                "Print Assumptions nqh_%s.\n"
                % ('ILCM' if mirror else 'ILC', ID, ID))
    return coqc(chk)


def attempt(spec, do_emit, scratch, mirror=False, ospec=None):
    """Derive+emit for ONE orientation.  [spec] is the table the proof runs
    on (the mirror, when mirror=True); [ospec] is the real machine."""
    res = {'spec': ospec or spec, 'ok': False, 'mirror': mirror}
    try:
        cands = anchor_candidates(spec, 'A')
    except Exception as e:
        res['why'] = 'anchor: %s' % e
        return res
    tried = []
    for (edge, encname, head, tail, p0) in cands[:10]:
        if encname != 'Ip':
            continue
        E = LAB.index(edge)
        encf = ENC[encname]
        for far in FARS:
            pr = profile(spec, E, encf, head, tail, far)
            if pr is None:
                tried.append('%s/%s far=%s: laps not affine on both branches'
                             % (edge, encname, far))
                continue
            ai, ao = pr
            try:
                s, U = derive(spec, E, encf, head, tail, far, ai, ao)
                msgs = shape_check(U, tail, far)
                if msgs:
                    tried.append('%s far=%s shape: %s' % (edge, far, '; '.join(msgs)))
                    continue
                nchk = validate(spec, E, encf, head, tail, far, s)
                boot = boot_probe(spec, E, encf, head, tail, far, p0)
            except (DeriveError, Wall, AssertionError, KeyError, IndexError) as e:
                tried.append('%s far=%s: %s' % (edge, far, e))
                continue
            res.update({'edge': edge, 'enc': encname, 'head': head,
                        'tail': list(tail), 'far': list(far), 'p0': p0,
                        'boot': boot, 'skel': s, 'nchecked': nchk})
            if not do_emit:
                res['ok'] = True
                res['why'] = 'derived+validated (not emitted)'
                return res
            try:
                src = emit_source(spec, E, encf, edge, head, tail, far,
                                  p0, boot, s, U, mirror, ospec)
            except DeriveError as e:
                tried.append('%s far=%s emit: %s' % (edge, far, e))
                continue
            ID = mach_id(ospec or spec)
            path = os.path.join(OUTDIR, '%s_%s.v'
                                % ('ILCM' if mirror else 'ILC', ID))
            with open(path, 'w') as f:
                f.write(src)
            res['file'] = path
            rc, out = coqc(path)
            if rc != 0:
                res['why'] = 'coqc failed'
                res['log'] = out[-2500:]
                os.remove(path)
                return res
            rc, out = print_assumptions(ID, scratch, mirror)
            names = set()
            inax = False
            for ln in out.splitlines():
                if ln.startswith('Axioms:'):
                    inax = True
                    continue
                if not inax or not ln.strip() or ln[:1].isspace():
                    continue
                nm = ln.strip().split(':')[0].strip()
                if re.match(r"^[A-Za-z_][A-Za-z_0-9.']*$", nm):
                    names.add(nm.split('.')[-1])
            res['axioms'] = sorted(names)
            res['ok'] = (res['axioms'] == ['functional_extensionality_dep'])
            if not res['ok']:
                res['why'] = 'unexpected axioms: %s' % res['axioms']
                os.remove(path)
            return res
    res['why'] = tried[0] if tried else 'no Ip anchor candidate'
    res['tried'] = tried
    return res



def process(spec, do_emit, scratch):
    """Try the machine as a LEFT-growth counter, then as the mirror of one.

    About half the template-shaped core machines grow rightward; the proof then
    runs on mirror_tm and Mirror.mirror_never_qh transfers it back, which needs
    no new theory (see docs/COUNTER_EMITTER_WAVE9.md).
    """
    r = attempt(spec, do_emit, scratch)
    if r['ok']:
        return r
    m = attempt(mirror_spec(spec), do_emit, scratch, mirror=True, ospec=spec)
    if m['ok']:
        return m
    r['why_mirror'] = m.get('why')
    return r


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('specs', nargs='*')
    ap.add_argument('--list')
    ap.add_argument('--emit', action='store_true')
    ap.add_argument('--json')
    ap.add_argument('--scratch', default='/tmp')
    a = ap.parse_args()
    specs = list(a.specs)
    if a.list:
        specs += [x.strip() for x in open(a.list) if x.strip()]
    out = []
    for spec in specs:
        r = process(spec, a.emit, a.scratch)
        out.append(r)
        print("%s %s %s" % ('PASS' if r['ok'] else 'FAIL', spec,
                            r.get('why', '')))
        if r.get('log'):
            for ln in r['log'].splitlines()[-12:]:
                print("      | %s" % ln)
        sys.stdout.flush()
    if a.json:
        with open(a.json, 'w') as f:
            json.dump(out, f, indent=1)
    print("== %d/%d passed" % (sum(1 for r in out if r['ok']), len(out)))


if __name__ == '__main__':
    main()
