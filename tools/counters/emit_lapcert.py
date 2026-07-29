#!/usr/bin/env python3
"""UNTRUSTED emitter: lap CERTIFICATES for theories/Checkers/LapDecider.v.

This replaces the five per-machine emitters (emit_shape1/shape4/ixp/wall/wallj)
with ONE that emits DATA.  Where those emitted a hand-shaped proof script per
machine -- window lemmas, transported phases, an assembled lap, a bespoke
[reach_fin2] induction -- this emits two lists of small numbers and lets
[LapDecider.srun_sound] discharge them, once, for every machine.

Per machine the Coq file now contains exactly:
  * the TM table and the anchor [Cc p = (E, (Enc p ++ tail, S0, []))];
  * two [srun ... = Some (..., ca, cb)] facts, closed by [vm_compute];
  * four ANCHOR GLUE lemmas -- the only per-machine mathematics -- each a
    [cview] rewrite plus [app_assoc];
  * boot, visits (via [LapCertGlue.vis_via_ovf]) and the two theorems.

ENCODINGS ARE DIGIT ALPHABETS.  [Ip] and [Jp] differ only in which digit the
carry writes, so they are two rows of ENCDATA rather than two emitters; the
encoding is SEARCHED at derive time (emit_interleave.derive_tail_best), never
hard-coded.

Everything here is untrusted: the Coq kernel re-runs [srun] on every chain.

Usage
  emit_lapcert.py --list FILE [--emit] [--json OUT] [--jobs N]
  emit_lapcert.py --spec SPEC [--emit]
"""
import argparse
import collections
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

from emit_interleave import (parse, carry, ENC, LAB, ST, SYM,          # noqa: E402
                             DeriveError, derive_tail_best,
                             derive_tail_best_far, mach_id, coq_table,
                             clist)
from mirror_common import mirror_spec, mirrorize                       # noqa: E402
import lapcert as LC
import nestcert as NC                                                   # noqa: E402

OUTDIR = os.path.join(REPO, 'theories', 'Machines', 'Counters')
PREFIX = 'LAPC'
# Boards whose overflow branch is the NESTED composition get their own prefix,
# so a wave is legible at a glance (and cannot collide with a concurrent
# session's files).  inventory.py maps rows to theorems by PARSING THE TM
# BODIES, so the prefix carries no meaning downstream.
NEST_PREFIX = 'NLAP'
# Quasihalters closed by the state-AVOIDANCE route (LapAvoid/LapGlueQuiet):
# StA is targeted but never fires after the bootstrap, and the kernel
# recomputes that from the SAME chains.
AVOID_PREFIX = 'LAPQ'
# Boards whose overflow branch is PEELED (stated at j = S j', with p = 1 a
# concrete lap -- [_peel_ovf]).  Its own prefix for the same reason as the
# others: a wave stays legible and cannot collide with a concurrent session.
PEEL_PREFIX = 'PEEL'

# ---------------------------------------------------------------------------
# The digit alphabets.  For every encoding E and every p,
#
#   interior  (cview p = (j, Some q0)):
#       E p         = rep uS j ++ sS ++ E q0
#       E (succ p)  = rep uD j ++ sD ++ E q0
#   overflow  (cview p = (S j, None)):
#       E p         = rep uS j ++ so
#       E (succ p)  = rep uD (S j) ++ so
#
# which is exactly ILCounter.cview_some_I/cview_none_I and their Jp twins.
# ---------------------------------------------------------------------------
# obS is the overflow SOURCE count offset (E p = rep uS (j+obS) ++ soS); the
# destination is always rep uD (S j) ++ soD.  Mp/Kp/Dp differ from Ip/Jp only
# in these rows -- they are digit alphabets, not emitter forks.
ENCDATA = {
    'Ip': dict(uS=(1, 1), sS=(1, 0), uD=(1, 0), sD=(1, 1),
               obS=0, soS=(1,), soD=(1,),
               mod='ILCounter', some='cview_some_I', none='cview_none_I'),
    'Jp': dict(uS=(1, 0), sS=(1, 1), uD=(1, 1), sD=(1, 0),
               obS=0, soS=(1,), soD=(1,),
               mod='JpCounter', some='cview_some_J', none='cview_none_J'),
    'Kp': dict(uS=(1,), sS=(0,), uD=(0,), sD=(1,),
               obS=1, soS=(), soD=(1,),
               mod='KpCounter', some='cview_some_K', none='cview_none_K'),
    'Dp': dict(uS=(1, 1), sS=(0, 0), uD=(0, 0), sD=(1, 1),
               obS=1, soS=(), soD=(1, 1),
               mod='DpCounter', some='cview_some_D', none='cview_none_D'),
    'Mp': dict(uS=(1, 1), sS=(0, 1), uD=(0, 1), sD=(1, 1),
               obS=1, soS=(), soD=(1, 1),
               mod='MpCounter', some='cview_some_M', none='cview_none_M'),
    # The BLANK-separated alphabet.  Every other row separates with S1 or
    # not at all, which is why the anchor search reported "no anchor family"
    # on this population rather than a shape mismatch.  Added from John's
    # reading of 1RB0RB_1LC1RA_1RA0LD_0LB0LD; measured to decode 26% of a
    # 120-machine sample of the no-anchor bucket.
    'Bp': dict(uS=(0, 1), sS=(0, 0), uD=(0, 0), sD=(0, 1),
               obS=1, soS=(), soD=(0, 1),
               mod='BpCounter', some='cview_some_B', none='cview_none_B'),
}


def _Kp(m):
    out = []
    while m > 1:
        out.append(m & 1)
        m >>= 1
    return out + [1]


def _Dp(m):
    out = []
    while m > 1:
        b = m & 1
        out += [b, b]
        m >>= 1
    return out + [1, 1]


def _Mp(m):
    out = []
    while m > 1:
        out += [m & 1, 1]
        m >>= 1
    return out + [1, 1]


def _Bp(m):
    out = []
    while m:
        out += [0, m & 1]
        m >>= 1
    return out


ENC.setdefault('Kp', _Kp)
ENC.setdefault('Dp', _Dp)
ENC.setdefault('Mp', _Mp)
ENC.setdefault('Bp', _Bp)
ENCS = ('Ip', 'Jp', 'Kp', 'Dp', 'Mp', 'Bp')

# ---------------------------------------------------------------------------
# The INFERRED alphabets.  tools/counters/alphabet_infer.py reads a counter's
# word family off its own tape as a triple (A, B, C) with
#
#     E xH = C      E (xO q) = A ++ E q      E (xI q) = B ++ E q
#
# which determines the row completely (uS = B, sS = A, uD = A, sD = B,
# obS = 0, soS = soD = C).  gen_alphabet.py turns each triple into a Coq
# module whose two decomposition lemmas are PROVED by the same induction as
# ILCounter's, so a wrong triple fails to compile rather than mis-proving.
#
# This is not the "widen the encoding table and hope" that WAVE13 put on
# do-not-retry: nothing is guessed.  Each row exists because a family was
# measured on a machine's tape and verified against 100+ consecutive anchor
# words.
# ---------------------------------------------------------------------------
try:
    import alphabets_gen as _AG                                    # noqa: E402
    for _k, _row in _AG.ENCROWS.items():
        ENCDATA.setdefault(_k, _row)
        ENC.setdefault(_k, _AG.ENCFN[_k])
    ENCS = ENCS + tuple(k for k in sorted(_AG.ENCROWS) if k not in ENCS)
except ImportError:                                                # pragma: no cover
    pass


FLAT = ((), (), 0, 0, ())
Halt_ = LC.Halt


def branches(enc, tail):
    """The four symbolic configurations: start/target of each branch."""
    d = ENCDATA[enc]
    tail = tuple(tail)
    return dict(
        int_start=(d['uS'], d['sS']),
        int_end=(d['uD'], d['sD']),
        ovf_start=(d['uS'], d['so'] + tail),
        ovf_end=(d['uD'], d['so'] + tail),
    )


def confs(enc, st0, tail, far=()):
    """[far] is the anchor's FAR side -- empty for a plain counter, a fixed
    wall for the wall families.  Either way nothing is written beyond it, so
    the right opaque tail is empty and open-right windows are available."""
    d = ENCDATA[enc]
    tail, far = tuple(tail), tuple(far)
    F = (far, (), 0, 0, ())
    A0 = (st0, ((), d['uS'], 1, 0, d['sS']), 0, F)
    A1 = (st0, ((), d['uD'], 1, 0, d['sD']), 0, F)
    # overflow: E p = rep uS j ++ so, and E (succ p) = rep uD (S j) ++ so,
    # i.e. uD ++ rep uD j ++ so -- so the target carries uD in its prefix.
    # When obS >= 1 the overflow block is NEVER empty, so peel one copy into
    # the prefix: rep uS (S j) = uS ++ rep uS j.  That gives the head a
    # concrete cell to step onto, which is what the un-peeled form denies it.
    if d['obS'] >= 1:
        B0 = (st0, (d['uS'], d['uS'], 1, d['obS'] - 1, d['soS'] + tail), 0, F)
    else:
        B0 = (st0, ((), d['uS'], 1, 0, d['soS'] + tail), 0, F)
    B1 = (st0, ((), d['uD'], 1, 1, d['soD'] + tail), 0, F)
    return A0, A1, B0, B1


# ------------------------------------------------------------- validation ---

def sim(tab, cfg, n):
    """The REAL machine (both sides open = CTape.cstep) for n steps."""
    for _ in range(n):
        cfg = LC.wstep(tab, False, False, cfg)
    return cfg


def eqlift(a, b):
    """Configurations equal up to blank padding ([CTape.lift])."""
    return (a[0] == b[0] and a[2] == b[2]
            and LC.rstrip0(a[1]) == LC.rstrip0(b[1])
            and LC.rstrip0(a[3]) == LC.rstrip0(b[3]))


def validate(tab, st0, encf, tail, far, cost, co, hi=200, peel=None):
    """Differentially check both branches against the raw simulator: exact
    step counts AND exact configurations, on every p in range.

    [peel] is the peeled overflow route's concrete [p = 1] step count: the
    branch's chain then starts one index up, so the affine law is read at
    [j - 2] and [p = 1] is checked against that one number."""
    tail, far = tuple(tail), tuple(far)
    n = 0
    for p in range(1 if peel is not None else 2, hi):
        j, ov = carry(p)
        if ov and peel is not None:
            steps = peel if j == 1 else co[0] * (j - 2) + co[1]
        elif ov:
            steps = co[0] * (j - 1) + co[1]
        else:
            steps = cost(j)
        start = (st0, tuple(encf(p)) + tail, 0, far)
        want = (st0, tuple(encf(p + 1)) + tail, 0, far)
        got = sim(tab, start, steps)
        if not eqlift(got, want):
            return False, 'p=%d %s branch: %d steps -> %r want %r' % (
                p, 'ovf' if ov else 'int', steps, got, want)
        n += 1
    return True, '%d anchors' % n


def validate_int(tab, st0, encf, tail, far, cost, hi=200):
    """The INTERIOR branch alone, against the raw simulator.  Used by the
    nested route, whose overflow branch is not one chain and is validated
    piecewise by [nestcert.validate]."""
    tail, far = tuple(tail), tuple(far)
    n = 0
    for p in range(2, hi):
        j, ov = carry(p)
        if ov:
            continue
        start = (st0, tuple(encf(p)) + tail, 0, far)
        want = (st0, tuple(encf(p + 1)) + tail, 0, far)
        got = sim(tab, start, cost(j))
        if not eqlift(got, want):
            return False, 'p=%d int branch: %d steps -> %r want %r' % (
                p, cost(j), got, want)
        n += 1
    return True, '%d interior anchors' % n


# ------------------------------------------------------------ Coq emission ---

def cstep_str(st):
    if st[0] == 'SCycL':
        return 'SCycL %d %d' % (st[1], st[2])
    return '%s %d' % (st[0], st[1])


def cchain(ch):
    return '[' + '; '.join(cstep_str(s) for s in ch) + ']'


def cside(s):
    pre, u, a, b, post = s
    return 'mkS %s %s %d %d %s' % (clist(pre), clist(u), a, b, clist(post))


def cconf(c):
    return 'mkC %s (%s) %s (%s)' % (ST[c[0]], cside(c[1]), SYM[c[2]],
                                    cside(c[3]))


NQH_CLOSE = '''Theorem nqh_@ID@ : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc @P0@). - exact boot_@ID@. - intros p _. apply lap_@ID@. - intros p q _. apply vis_@ID@. Qed.

Theorem nonhalt_@ID@ : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_@ID@. Qed.'''

NQH_CLOSE_LIFT = '''(** The interior lap closes only up to [lift] (one trailing blank past the
    anchor's far side), so the closer is [LapCertGlueLift.glue_neverqh_lift]:
    [LapGlue.glue_neverqh] with the visit premise in [stepn] space, which is
    what its own proof consumes. *)
Theorem nqh_@ID@ : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh_lift tm Cc @P0@). - exact boot_@ID@. - intros p _. apply lap_@ID@. - intros p q _. apply vis_@ID@. Qed.

Theorem nonhalt_@ID@ : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_@ID@. Qed.'''

QH_CLOSE = '''(** StA is TARGETED BY NOTHING, so its only visit is at configuration index
    0 and the quiet bound is 1 -- weakened to the census tier's 2000. *)
Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.

Theorem iqh_@ID@ : iqh tm.
Proof.
  destruct (glue_qh tm Cc @P0@ boot_@ID@ (fun p _ => lap_@ID@ p)
                    (fun p q _ Hq => vis_@ID@ p q Hq)
                    (ltac:(intros q b tr Ht; destruct q, b; cbn in Ht;
                           try discriminate; injection Ht as <-; discriminate)))
    as (Hn & Hb & Hq).
  split; [exact Hn | split; [| exact Hq]].
  apply (qhbound_mono 1 2000); [lia | exact Hb].
Qed.

Theorem nonhalt_@ID@ : NonHalt tm.
Proof. apply (proj1 iqh_@ID@). Qed.'''


ABS_CLOSE = '''(** The lap reaches only @SSETC@, which is CLOSED under the table, and the
    machine is already inside it at configuration index @ABSD@ -- so every state
    outside made all of its visits before @ABSD@ ([LapGlueAbs.glue_qh_abs]).
    @QUIETC@ is therefore quiet, with a last visit before @ABSD@; the bound is
    weakened to the census tier\'s 2000. *)
Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.

Theorem iqh_@ID@ : iqh tm.
Proof.
  destruct (glue_qh_abs tm Cc @P0@ @SSET@ @ABSD@
                    boot_@ID@ (fun p _ => lap_@ID@ p)
                    (fun p q _ Hq => vis_@ID@ p q Hq)
                    (closed_b_sound tm @SSET@ ltac:(vm_compute; reflexivity))
                    ltac:(eexists; split;
                          [vm_compute; reflexivity | cbn; tauto])
                    ltac:(cbn; intuition discriminate))
    as (Hn & Hb & Hq).
  split; [exact Hn | split; [| exact Hq]].
  apply (qhbound_mono @ABSD@ 2000); [lia | exact Hb].
Qed.

Theorem nonhalt_@ID@ : NonHalt tm.
Proof. apply (proj1 iqh_@ID@). Qed.'''


AVOID_DEFS_ONE = r'''Lemma av_int_@ID@ : srun_avoid tm false true StA chi_@ID@ A0_@ID@ = true.
Proof. vm_compute. reflexivity. Qed.'''

AVOID_DEFS_SPLIT = r'''Lemma av_z_@ID@ : srun_avoid tm false true StA chz_@ID@ Z0_@ID@ = true.
Proof. vm_compute. reflexivity. Qed.

Lemma av_p_@ID@ : srun_avoid tm false true StA chp_@ID@ P0_@ID@ = true.
Proof. vm_compute. reflexivity. Qed.'''

AVOID_LAPI_ONE = r'''  - exists (@CAI@ * j + @CBI@), (Cc (Pos.succ p)).
    split.
    { rewrite (gsi_@ID@ p j q0 E).
      rewrite (srun_sound tm false true chi_@ID@ A0_@ID@ A1_@ID@ @CAI@ @CBI@
                 run_int_@ID@ (@ENC@ q0 ++ @TAIL@) [] j
                 ltac:(discriminate) ltac:(reflexivity)).
      f_equal. exact (gei_@ID@ p j q0 E). }
    split; [reflexivity|]. split; [lia|].
    exact (avoid_of_run tm Cc false true StA chi_@ID@ A0_@ID@ A1_@ID@
             @CAI@ @CBI@ p j (@ENC@ q0 ++ @TAIL@) [] run_int_@ID@ av_int_@ID@
             ltac:(discriminate) ltac:(reflexivity) (gsi_@ID@ p j q0 E)).'''

AVOID_LAPI_SPLIT = r'''  - destruct j as [|j'].
    + destruct (gz_@ID@ p q0 E) as (HA & HB).
      exists (@CAZ@ * 0 + @CBZ@), (Cc (Pos.succ p)).
      split.
      { rewrite HA.
        rewrite (srun_sound tm false true chz_@ID@ Z0_@ID@ Z1_@ID@ @CAZ@ @CBZ@
                   run_z_@ID@ (@ENC@ q0 ++ @TAIL@) [] 0
                   ltac:(discriminate) ltac:(reflexivity)).
        f_equal. exact HB. }
      split; [reflexivity|]. split; [lia|].
      exact (avoid_of_run tm Cc false true StA chz_@ID@ Z0_@ID@ Z1_@ID@
               @CAZ@ @CBZ@ p 0 (@ENC@ q0 ++ @TAIL@) [] run_z_@ID@ av_z_@ID@
               ltac:(discriminate) ltac:(reflexivity) HA).
    + destruct (gp_@ID@ p j' q0 E) as (HA & HB).
      exists (@CAP@ * j' + @CBP@), (Cc (Pos.succ p)).
      split.
      { rewrite HA.
        rewrite (srun_sound tm false true chp_@ID@ P0_@ID@ P1_@ID@ @CAP@ @CBP@
                   run_p_@ID@ (@ENC@ q0 ++ @TAIL@) [] j'
                   ltac:(discriminate) ltac:(reflexivity)).
        f_equal. exact HB. }
      split; [reflexivity|]. split; [lia|].
      exact (avoid_of_run tm Cc false true StA chp_@ID@ P0_@ID@ P1_@ID@
               @CAP@ @CBP@ p j' (@ENC@ q0 ++ @TAIL@) [] run_p_@ID@ av_p_@ID@
               ltac:(discriminate) ltac:(reflexivity) HA).'''

AVOID_CLOSE = r'''(** StA IS a transition target, so [LapGlueQH.glue_qh]'s syntactic argument
    is out; and [LapGlueAbs.closed_b] is a digraph fact, so no absorbing set
    can exclude StA either.  What is true is trajectory-level: StA's last
    visit is at index @S0@ (checked), the window (@S0@, @BOOT@) is StA-free
    (checked), and EVERY lap avoids StA -- recomputed from the SAME chains by
    the kernel ([av_*] below, [Checkers/LapAvoid.v]).
    [LapGlueQuiet.glue_qh_quiet] closes with the exact bound S @S0@,
    weakened to the census tier's 2000. *)
@AVDEFS@

Lemma av_ovf_@ID@ : srun_avoid tm true true StA cho_@ID@ B0_@ID@ = true.
Proof. vm_compute. reflexivity. Qed.

(** The full lap, avoidance carried on both branches. *)
Lemma lapav_@ID@ : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n
  /\ AvoidRun tm StA n (Cc p).
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
@AVLAPI@
  - destruct (cview_pos p j E) as (j' & ->).
    exists (@CAO@ * j' + @CBO@), (cden [] [] j' B1_@ID@).
    split.
    { rewrite (gso_@ID@ p j' E).
      exact (srun_sound tm true true cho_@ID@ B0_@ID@ B1_@ID@ @CAO@ @CBO@
               run_ovf_@ID@ [] [] j'
               ltac:(reflexivity) ltac:(reflexivity)). }
    split; [exact (geo_@ID@ p j' E)|]. split; [lia|].
    exact (avoid_of_run tm Cc true true StA cho_@ID@ B0_@ID@ B1_@ID@
             @CAO@ @CBO@ p j' [] [] run_ovf_@ID@ av_ovf_@ID@
             ltac:(reflexivity) ltac:(reflexivity) (gso_@ID@ p j' E)).
Qed.

(** The bootstrap at its CONCRETE index, StA's last visit, and the checked
    StA-free window between them. *)
Lemma bootc_@ID@ : stepn tm @BOOT@ InitES = Some (lift (Cc @P0@)).
Proof.
  assert (H : match csteps tm @BOOT@ c0 with
              | Some c => ceqb c (Cc @P0@) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm @BOOT@ c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

Lemma bvis_@ID@ : VisitsAt tm StA @S0@.
Proof. apply bootvis_chk_sound. vm_compute. reflexivity. Qed.

Lemma bq_@ID@ : forall n c, @S0@ < n < @BOOT@ ->
  stepn tm n InitES = Some c -> fst c <> StA.
Proof.
  intros n c Hn Hc.
  refine (bootquiet_chk_sound tm StA (S @S0@) @DD@ _ n c _ Hc);
    [vm_compute; reflexivity | lia].
Qed.

Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.

Theorem iqh_@ID@ : iqh tm.
Proof.
  destruct (glue_qh_quiet tm Cc @P0@ StA @BOOT@ @S0@
              bootc_@ID@
              (fun p _ => lapav_@ID@ p)
              (fun p q _ Hq => vis_@ID@ p q Hq)
              bvis_@ID@
              bq_@ID@)
    as (Hn & Hb & Hq).
  split; [exact Hn | split; [| exact Hq]].
  apply (qhbound_mono (S @S0@) 2000); [lia | exact Hb].
Qed.

Theorem nonhalt_@ID@ : NonHalt tm.
Proof. apply (proj1 iqh_@ID@). Qed.'''


# ---------------------------------------------------------------------------
# The interior branch, in two shapes.
#
# ONE: a single chain covering every j.  Works when the head never has to step
# into the repeated block's first cell -- otherwise that cell is AMBIGUOUS at
# j = 0 (the block vanishes and the neighbour is post's first cell instead),
# and the symbolic run stalls with no legal move.
#
# SPLIT: two chains, j = 0 and j = S j'.  In the j = S j' chain one copy of the
# unit sits in the PREFIX, so the head always has a concrete cell to step onto.
# Measured wave-13 section 9a: this alone unlocks ~31% of the machines whose
# single chain fails.  No new soundness surface -- the glue gains a destruct.
# ---------------------------------------------------------------------------

INT_ONE = r"""Definition A0_@ID@ : sconf := @A0@.
Definition A1_@ID@ : sconf := @A1@.
Definition chi_@ID@ : list lstep := @CHI@.

Lemma run_int_@ID@ : srun tm false true chi_@ID@ A0_@ID@ = Some (A1_@ID@, @CAI@, @CBI@).
Proof. vm_compute. reflexivity. Qed."""

GLUE_ONE = r"""Lemma gsi_@ID@ : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (@ENC@ q0 ++ @TAIL@) [] j A0_@ID@.
Proof.
  intros p j q0 E. destruct (@ENCMOD@.@SOME@ p j q0 E) as (H1 & _).
  unfold Cc_@ID@, cden, A0_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep @US@ j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gei_@ID@ : forall p j q0, cview p = (j, Some q0) ->
  cden (@ENC@ q0 ++ @TAIL@) [] j A1_@ID@ = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (@ENCMOD@.@SOME@ p j q0 E) as (_ & H2).
  unfold Cc_@ID@, cden, A1_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. first [ rewrite <- (app_assoc (rep @UD@ j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_@ID@ : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (@CAI@ * j + @CBI@). split; [lia|].
  rewrite (gsi_@ID@ p j q0 E).
  rewrite (srun_sound tm false true chi_@ID@ A0_@ID@ A1_@ID@ @CAI@ @CBI@
             run_int_@ID@ (@ENC@ q0 ++ @TAIL@) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_@ID@ p j q0 E).
Qed."""

# ---------------------------------------------------------------------------
# The INTERIOR branch, up to [lift].
#
# The lap is complete and in model, but lands one trailing blank past the
# anchor's far side -- invisible to [lift] ([CTape.lift_side l = fun n =>
# nth n l S0]), which is all [LapDecider.lap_of_run] and [LapGlue]'s [Hlap]
# ever ask for.  Only the emitter's EXACT glue ([gei_*] by [reflexivity]) and
# [LapCertGlue.reach_ovf] (which chains interior laps by cconf equality) want
# the syntactic form; [Counters/LapCertGlueLift.v] supplies the [lift] twins.
#
# The exact route is still preferred whenever it derives -- it is cheaper and
# it keeps [reach_ovf] available.  This is the fallback.
# ---------------------------------------------------------------------------

GLUE_ONE_LIFT = r"""Lemma gsi_@ID@ : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (@ENC@ q0 ++ @TAIL@) [] j A0_@ID@.
Proof.
  intros p j q0 E. destruct (@ENCMOD@.@SOME@ p j q0 E) as (H1 & _).
  unfold Cc_@ID@, cden, A0_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep @US@ j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

(** The lap ends on @FARB@ where the anchor has @FAR@ -- one trailing blank,
    which [lift] cannot see. *)
Lemma gei_@ID@ : forall p j q0, cview p = (j, Some q0) ->
  lift (cden (@ENC@ q0 ++ @TAIL@) [] j A1_@ID@) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (@ENCMOD@.@SOME@ p j q0 E) as (_ & H2).
  unfold Cc_@ID@, cden, A1_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change (@FARB@) with (@FARNEST@).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep @UD@ j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_@ID@ : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  exists (@CAI@ * j + @CBI@), (cden (@ENC@ q0 ++ @TAIL@) [] j A1_@ID@).
  split; [lia|]. split; [| exact (gei_@ID@ p j q0 E)].
  rewrite (gsi_@ID@ p j q0 E).
  exact (srun_sound tm false true chi_@ID@ A0_@ID@ A1_@ID@ @CAI@ @CBI@
           run_int_@ID@ (@ENC@ q0 ++ @TAIL@) [] j
           ltac:(discriminate) ltac:(reflexivity)).
Qed."""

INT_SPLIT = r"""(** j = 0: the repeated block is absent, so the whole lap is concrete. *)
Definition Z0_@ID@ : sconf := @Z0@.
Definition Z1_@ID@ : sconf := @Z1@.
Definition chz_@ID@ : list lstep := @CHZ@.

Lemma run_z_@ID@ : srun tm false true chz_@ID@ Z0_@ID@ = Some (Z1_@ID@, @CAZ@, @CBZ@).
Proof. vm_compute. reflexivity. Qed.

(** j = S j': one copy of the unit sits in the PREFIX, so the head always has
    a concrete cell to step onto. *)
Definition P0_@ID@ : sconf := @P0C@.
Definition P1_@ID@ : sconf := @P1C@.
Definition chp_@ID@ : list lstep := @CHP@.

Lemma run_p_@ID@ : srun tm false true chp_@ID@ P0_@ID@ = Some (P1_@ID@, @CAP@, @CBP@).
Proof. vm_compute. reflexivity. Qed."""

GLUE_SPLIT = r"""Lemma gz_@ID@ : forall p q0, cview p = (0, Some q0) ->
  Cc p = cden (@ENC@ q0 ++ @TAIL@) [] 0 Z0_@ID@ /\
  cden (@ENC@ q0 ++ @TAIL@) [] 0 Z1_@ID@ = Cc (Pos.succ p).
Proof.
  intros p q0 E. destruct (@ENCMOD@.@SOME@ p 0 q0 E) as (H1 & H2).
  unfold Cc_@ID@, cden, Z0_@ID@, Z1_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gp_@ID@ : forall p j q0, cview p = (S j, Some q0) ->
  Cc p = cden (@ENC@ q0 ++ @TAIL@) [] j P0_@ID@ /\
  cden (@ENC@ q0 ++ @TAIL@) [] j P1_@ID@ = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (@ENCMOD@.@SOME@ p (S j) q0 E) as (H1 & H2).
  unfold Cc_@ID@, cden, P0_@ID@, P1_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_@ID@ : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct j as [|j'].
  - destruct (gz_@ID@ p q0 E) as (HA & HB).
    exists (@CAZ@ * 0 + @CBZ@). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chz_@ID@ Z0_@ID@ Z1_@ID@ @CAZ@ @CBZ@
               run_z_@ID@ (@ENC@ q0 ++ @TAIL@) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gp_@ID@ p j' q0 E) as (HA & HB).
    exists (@CAP@ * j' + @CBP@). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chp_@ID@ P0_@ID@ P1_@ID@ @CAP@ @CBP@
               run_p_@ID@ (@ENC@ q0 ++ @TAIL@) [] j'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
Qed."""


FLAT_OVF_DEFS = r"""Definition cho_@ID@ : list lstep := @CHO@.

Lemma run_ovf_@ID@ : srun tm true true cho_@ID@ B0_@ID@ = Some (B1_@ID@, @CAO@, @CBO@).
Proof. vm_compute. reflexivity. Qed."""

FLAT_OVF_CASE = r"""  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_@ID@ B0_@ID@ B1_@ID@ @CAO@ @CBO@ p j' [] []).
    + exact run_ovf_@ID@.
    + reflexivity.
    + reflexivity.
    + exact (gso_@ID@ p j' E).
    + exact (geo_@ID@ p j' E).
    + lia."""

# --------------------------------------------------------------- the PEEL ---
# The overflow branch stated at [j = S j'], with one more unit copy standing
# in the chain's PREFIX -- and the case it leaves behind, [p = 1], discharged
# as one concrete run.  See [_peel_ovf].
LAPZ_LEMMA = r"""(** The smallest overflow anchor, [p = 1]: one concrete run.  The peeled
    branch below states its chain at [j = S j'], so this case is what the
    reindex leaves behind -- the [j = 0] device of the offset route, at the
    OUTER anchor. *)
Lemma lapz_@ID@ : exists n c', csteps tm n (Cc 1) = Some c'
  /\ lift c' = lift (Cc 2) /\ 0 < n.
Proof.
  exists @NZ@.
  assert (H : match csteps tm @NZ@ (Cc 1) with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm @NZ@ (Cc 1)) as [c|] eqn:Ez; [|discriminate].
  exists c. split; [reflexivity|]. split; [apply ceqb_lift; exact H | lia].
Qed."""

VISZ_LEMMA = r"""(** State @STQ@'s visit witness at the peeled branch's [p = 1] case. *)
Lemma visz_@STQ@_@ID@ : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = @STQ@.
Proof. exists @KQ@. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed."""

FLAT_OVF_CASE_PEEL = r"""  - destruct (cview_pos p j E) as (j' & ->).
    destruct j' as [|j''].
    + rewrite (cview_none_shape p 0 E). exact lapz_@ID@.
    + apply (lap_of_run tm Cc true true cho_@ID@ B0_@ID@ B1_@ID@ @CAO@ @CBO@ p j'' [] []).
      * exact run_ovf_@ID@.
      * reflexivity.
      * reflexivity.
      * exact (gso_@ID@ p j'' E).
      * exact (geo_@ID@ p j'' E).
      * lia."""


HEADER = r'''(** * @PREF@_@ID@: machine @SPEC@, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the @ENC@ digit alphabet (@ENCMOD@.v), anchored at

      Cc p = (@ST0@, (@ENC@ p ++ @TAIL@, S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  @NI@ steps
      overflow  (cview p = (S j, None)):   @NO@

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for @VAL@.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter @ENCMOD@ LapCertGlue@GLUELIFT@@NESTIMPORT@@AVIMP@.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider@AVIMP2@.
Import ListNotations.

Definition mk_@ID@ (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_@ID@.

(** @SPEC@ *)
Definition tm_@ID@ : TM := fun q s => match q, s with
@TABLE@ end.
Local Notation tm := tm_@ID@.

Definition Cc_@ID@ (p : positive) : cconf := (@ST0@, (@ENC@ p ++ @TAIL@, S0, @FAR@)).
Local Notation Cc := Cc_@ID@.

(** ** The certificate *)

@INTERIOR@

Definition B0_@ID@ : sconf := @B0@.
Definition B1_@ID@ : sconf := @B1@.
@OVFDEFS@

(** ** Anchor glue -- the only per-machine mathematics *)

@GLUEI@

Lemma gso_@ID@ : forall p j, cview p = (@CVSJ@, None) ->
  Cc p = cden [] [] j B0_@ID@.
Proof.
  intros p j E. destruct (@ENCMOD@.@NONE@ p @NNJ@ E) as (H1 & _).
  unfold Cc_@ID@, cden, B0_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + @OBSP@) with (@CNTP@) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_@ID@ : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_@ID@ : forall p j, cview p = (@CVSJ@, None) ->
  lift (cden [] [] j B1_@ID@) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (@ENCMOD@.@NONE@ p @NNJ@ E) as (_ & H2).
  assert (HD : cden [] [] j B1_@ID@
             = (@ST0@, (@HDLEFT@, S0, @OVFAR@))).
  { unfold cden, B1_@ID@, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + @B1B@) with @B1SJ@ by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (@ST0@, (@HCLEFT@, S0, @FAR@))).
  { unfold Cc_@ID@. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. @CLOSE@
Qed.

@NESTGLUE@(** ** The lap *)

Lemma lap_@ID@ : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
@LAPICASE@
@OVFCASE@
Qed.

(** ** Bootstrap *)

Lemma boot_@ID@ : exists t0, stepn tm t0 InitES = Some (lift (Cc @P0@)).
Proof.
  exists @BOOT@.
  assert (H : match csteps tm @BOOT@ c0 with
              | Some c => ceqb c (Cc @P0@) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm @BOOT@ c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma viso_@ID@ : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_@ID@ = Some q ->
  forall p j, cview p = (@CVSJ@, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_@ID@ p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_@ID@ p j E)].
Qed.

@VISIL@Lemma vis_@ID@ : @VISHYP@ @VISCONC@.
Proof.
  @VISINTRO@.
  assert (Hi : @VISHI@)
    by exact lapi_@ID@.
  destruct q.
@VISA@
@VISITS@
Qed.

@FINAL@
'''


def tclosure(tab, q0):
    """Every state reachable from [q0] in the transition digraph (all
    symbols, since which one is read is not known syntactically)."""
    S, work = {q0}, [q0]
    while work:
        q = work.pop()
        for b in (0, 1):
            t = tab.get((q, b))
            if t is not None and t[2] not in S:
                S.add(t[2]); work.append(t[2])
    return S


def avoid_probe(tab, t0, maxT=200000):
    """The AVOID route's empirical gate: StA's last visit is at some s0 < t0
    and StA never fires at any index in [t0, maxT).  Returns dict(s0=..) or
    None.  UNTRUSTED like everything here -- the kernel re-checks the window
    by [vm_compute] and the laps by [srun_avoid]; this only proposes s0 and
    fails fast on machines the route cannot take."""
    cfg = (0, (), 0, ())
    s0 = None
    for t in range(maxT):
        if cfg[0] == 0:
            if t >= t0:
                return None
            s0 = t
        try:
            cfg = LC.wstep(tab, False, False, cfg)
        except Halt_:
            return None
    if s0 is None or s0 >= t0:
        return None
    return dict(s0=s0)


def absorb_search(tab, have, maxd=64):
    """Smallest [d] whose reachable closure is covered by the states the lap
    actually visits ([have]) and excludes StA.

    Soundness note: the closure is an OVER-approximation of the states
    possible from index [d] on, so a set that passes here really is closed
    under the table -- which is all [LapGlueAbs.glue_qh_abs] asks.  The Coq
    side re-checks it with [closed_b]; this search only proposes."""
    tape, pos, q = collections.defaultdict(int), 0, 0
    for d in range(maxd):
        S = tclosure(tab, q)
        if 0 not in S and S <= set(have):
            return d, sorted(S)
        t = tab.get((q, tape[pos]))
        if t is None:
            return None
        tape[pos] = t[0]; pos += t[1]; q = t[2]
    return None


def _peel_ovf(tab, st0, encf, d, tail, far, Rr):
    """THE PEEL, on the overflow branch -- the standing first move.

    [confs] hands the overflow chain a count that can be EMPTY whenever the
    alphabet's [obS] is 0 (every INFERRED alphabet, and Ip/Jp): at [j = 0] the
    anchor is [p = 1], the smallest overflow word, and the head has no
    concrete cell to step onto.  A machine whose [p = 1] lap is a different
    length -- John's read of 0RB0LB_1LC1RD_0RD0LC_1RB1LA, "the carry has to
    alternate states to cross these 0s", 8 steps where the law says 10 --
    then has NO single chain covering the branch, and the row is filed under
    [no inner family] or [no anchor] with an exact affine law sitting in
    plain sight.

    So state the branch at [j = S j'] with one more unit copy standing in the
    chain's prefix, and discharge [p = 1] as one CONCRETE run: the offset
    route's [j = 0] device, at the OUTER anchor.  Returns the peeled sides,
    the chain, the concrete [p = 1] step count and its per-state visit
    witnesses, or None when the peeled chain does not derive either."""
    uS, uD = tuple(d['uS']), tuple(d['uD'])
    tail, far = tuple(tail), tuple(far)
    B0 = (st0, (uS * (d['obS'] + 1), uS, 1, 0, d['soS'] + tail), 0, Rr)
    B1 = (st0, (uD, uD, 1, 1, d['soD'] + tail), 0, Rr)
    cho = LC.derive_chain(tab, True, True, B0, B1)
    slack = False
    if cho is None:
        cho = LC.derive_chain(tab, True, True, B0, B1, lift=True)
        slack = cho is not None
    if cho is None:
        return None
    c1 = (st0, tuple(encf(1)) + tail, 0, far)
    c2 = (st0, tuple(encf(2)) + tail, 0, far)
    n0, cfg, visz = None, c1, {c1[0]: 0}
    for t in range(1, 20000):
        try:
            cfg = LC.wstep(tab, False, False, cfg)
        except Halt_:
            break
        if cfg[0] not in visz:
            visz[cfg[0]] = t
        if n0 is None and eqlift(cfg, c2):
            n0 = t
        if n0 is not None and len(visz) == 4:
            break
    if n0 is None:
        return None
    return dict(B0=B0, B1=B1, cho=cho, slack=slack, n0=n0, visz=visz)


def boot_probe(tab, st0, encf, tail, far, p0, maxT=200000):
    """Steps from the blank tape to the anchor at p0 (up to blank padding)."""
    want = (st0, tuple(encf(p0)) + tuple(tail), 0, tuple(far))
    cfg = (0, (), 0, ())
    for t in range(maxT):
        if eqlift(cfg, want):
            return t
        cfg = LC.wstep(tab, False, False, cfg)
    return None


def derive(spec, edge, tail, p0, enc, far=()):
    tab = parse(spec)
    st0 = LAB.index(edge)
    encf = ENC[enc]
    d = ENCDATA[enc]
    A0, A1, B0, B1 = confs(enc, st0, tail, far)

    Rr = (tuple(far), (), 0, 0, ())
    Z0 = (st0, (d['sS'], (), 0, 0, ()), 0, Rr)
    Z1 = (st0, (d['sD'], (), 0, 0, ()), 0, Rr)
    P0 = (st0, (d['uS'], d['uS'], 1, 0, d['sS']), 0, Rr)
    P1 = (st0, (d['uD'], d['uD'], 1, 0, d['sD']), 0, Rr)

    chi = LC.derive_chain(tab, False, True, A0, A1)
    islack = False
    if chi is None:
        chz = LC.derive_chain(tab, False, True, Z0, Z1)
        chp = LC.derive_chain(tab, False, True, P0, P1)
    if chi is not None:
        mode = 'one'
        ri = LC.srun(tab, False, True, chi, A0)
        if ri[2] == 0:
            raise DeriveError('lap of zero length at j=0')
        cost = lambda j, c=(ri[1], ri[2]): c[0] * j + c[1]
        chz = chp = rz = rp = None
    elif chz is None or chp is None:
        # LAST RESORT: the single chain up to [lift].  [LapDecider.lap_of_run]
        # and [LapGlue]'s [Hlap] only ever ask for a [lift] equality, and a
        # trailing blank is invisible to [lift]; it is the emitter's EXACT
        # anchor glue -- not the theorem -- that wants the syntactic form.
        # Rendered through the [lift] route, closed by
        # [Counters/LapCertGlueLift.v].  Measured wave-16: 0 -> 11 on the
        # AFFINE/AFFINE bucket, whose laps are in model but end one blank out.
        chi = LC.derive_chain(tab, False, True, A0, A1, lift=True)
        if chi is None:
            raise DeriveError('no interior chain')
        if LC.chain_is_exact(tab, False, True, chi, A0, A1):
            raise DeriveError('internal: exact chain found only under lift')
        islack = True
        mode = 'one'
        ri = LC.srun(tab, False, True, chi, A0)
        if ri[2] == 0:
            raise DeriveError('lap of zero length at j=0')
        # the reached configuration is what [run_int_*] states, so the board
        # must name IT, not the canonical anchor form
        A1 = ri[0]
        cost = lambda j, c=(ri[1], ri[2]): c[0] * j + c[1]
        chz = chp = rz = rp = None
    else:
        mode = 'split'
        rz = LC.srun(tab, False, True, chz, Z0)
        rp = LC.srun(tab, False, True, chp, P0)
        if rz[2] == 0 or rp[2] == 0:
            raise DeriveError('lap of zero length at j=0')
        ri = None
        cost = (lambda j, z=(rz[1], rz[2]), q=(rp[1], rp[2]):
                z[0] * 0 + z[1] if j == 0 else q[0] * (j - 1) + q[1])

    cho = LC.derive_chain(tab, True, True, B0, B1)
    oslack = False
    nest = None
    peel = None
    if cho is None:
        # The same trailing blank, on the overflow branch.  This one costs NO
        # new Coq: [geo_*] already closes the overflow up to [lift] (that is
        # what [lap_of_run] takes), and [WTape.lift_app_blank] strips a blank
        # from the RIGHT side -- the glue just has to say so.
        cho = LC.derive_chain(tab, True, True, B0, B1, lift=True)
        oslack = cho is not None
    if cho is None:
        # PEEL BEFORE ANYTHING ELSE (the standing lesson, five waves running).
        # One more unit copy in the overflow chain's prefix, [p = 1] concrete.
        peel = _peel_ovf(tab, st0, encf, d, tail, far, Rr)
        if peel is not None:
            B0, B1, cho, oslack = (peel['B0'], peel['B1'], peel['cho'],
                                   peel['slack'])
    if cho is None:
        # NO single chain covers the overflow, and for 492 of the 883 rows
        # that is not a search gap: the overflow costs [Theta(2^j)] and an
        # [srun] returns [ca*j+cb].  It decomposes into boot + an INDUCTION
        # over the inner counter + exit ([Counters/NestedLapLift.v]); the two
        # affine halves are ordinary chains and the exponent stays inside an
        # existential.  See docs/NESTED_LAP_PLAN.md.
        try:
            nest = NC.derive_nested(tab, ENCDATA, ENCS, ENC, enc, st0, tail,
                                    far, B0, B1)
        except NC.NestError as e:
            # the OFFSET route: the inner count starts at 2^(j+1)+c rather
            # than a power of two, and the branch reindexes at j = S j'.
            try:
                nest = NC.derive_offset(tab, ENCDATA, ENCS, ENC, enc, st0,
                                        tail, far)
            except NC.NestError:
                raise DeriveError('no overflow chain (nested: %s)' % e)
        if nest.get('route') == 'offset':
            # every overflow-side piece lives at the reindexed sides
            B0, B1 = nest['B0R'], nest['B1R']
        cho = nest['che']
        ro = LC.srun(tab, True, True, cho, nest['BE0'])
    else:
        ro = LC.srun(tab, True, True, cho, B0)
    if ro[2] == 0:
        raise DeriveError('lap of zero length at j=0')

    if nest is None:
        ok, why = validate(tab, st0, encf, tail, far, cost, (ro[1], ro[2]),
                           peel=peel['n0'] if peel else None)
        if not ok:
            raise DeriveError('validation: ' + why)
        if peel:
            why += ' (overflow PEELED at j = S j\', p = 1 concrete)'
    else:
        # the flat validate() assumes ONE overflow chain covers the branch;
        # nestcert.validate replays all three pieces (and every inner lap)
        ok, why = validate_int(tab, st0, encf, tail, far, cost)
        if not ok:
            raise DeriveError('validation: ' + why)
        why = '%s (interior); %s (nested overflow)' % (why, nest['nval'])
        oslack = nest['efar'] > 0

    # StA may genuinely go quiet: these are the residue's QUASIHALTING
    # counters.  [LapGlueQH.glue_qh] closes them provided nothing targets
    # StA (then its only visit is at index 0, so the bound is 1) -- far
    # inside the census tier, and inside the champion's 32.8M prefix.
    untargeted = all(t is None or t[2] != 0 for t in tab.values())
    vis, visi, qh, absd, sset = {}, {}, False, None, None
    avoid = None
    missing = []
    chov = nest['chb'] if nest is not None else cho
    for q in range(4):
        pre = LC.reach_state(tab, True, True, B0, chov, q)
        if pre is None:
            missing.append(q)
            continue
        vis[q] = pre
    if missing and mode == 'one':
        # A state can be genuinely LIVE and still never fire in the OVERFLOW
        # lap, which is the only branch [vis_via_ovf] can see.  Look for it in
        # the INTERIOR chain instead and close through
        # [LapCertGlueLift.vis_via_int_lift] -- reaching an interior anchor
        # costs at most ONE lap, because the successor of an all-ones
        # positive is [xO _] and so always interior.
        still = []
        for q in missing:
            pre = LC.reach_state(tab, False, True, A0, chi, q)
            if pre is None:
                still.append(q)
            else:
                visi[q] = pre
        missing = still
    visx = {}
    if missing and nest is not None:
        # The overflow lap is boot + inner + exit, and [vis_of_run] only sees
        # a prefix of ONE chain.  Look in the EXIT chain and close through
        # [NestedLapLift.vis_via_fill], which supplies the exponentially long
        # middle.  Measured: this is what 8 of 30 sampled machines need.
        still = []
        for q in missing:
            pre = LC.reach_state(tab, True, True, nest['BE0'], nest['che'], q)
            if pre is None:
                still.append(q)
            else:
                visx[q] = pre
        missing = still
    if missing:
        # The lap is complete but some state never fires inside it.  Two
        # closers apply, cheapest first:
        #   glue_qh   -- StA alone is missing AND nothing targets it;
        #   glue_qh_abs -- the states the lap DOES reach are closed under the
        #                  table from some index d on, so everything else is
        #                  quiet before d.  Strictly more general (it is the
        #                  d>0 case), and it is what settles the machines whose
        #                  quiet state is targeted during the bootstrap.
        if missing == [0] and untargeted:
            qh = True
        else:
            found = absorb_search(tab, sorted(set(vis) | set(visi) | set(visx)))
            if found is not None:
                absd, sset = found
            elif missing == [0]:
                # StA is TARGETED, so neither glue_qh nor an absorbing set can
                # exclude it -- but it may be a genuine quasihalter whose
                # targeting transition never fires after the boot.  The AVOID
                # route (LapAvoid/LapGlueQuiet) proves that from the chains
                # themselves; verified against boot below.
                avoid = 'pending'
            else:
                raise DeriveError('no visit witness for state %s%s' % (
                    LAB[missing[0]],
                    '' if missing[0] or untargeted else ' (StA is targeted)'))

    boot = boot_probe(tab, st0, encf, tail, far, p0)
    if boot is None:
        raise DeriveError('no bootstrap to p0=%d' % p0)

    if avoid is not None:
        if nest is not None or islack or oslack or peel is not None:
            raise DeriveError('avoid route: only flat exact boards are wired')
        avoid = avoid_probe(tab, boot)
        if avoid is None:
            raise DeriveError(
                'no visit witness for state A (StA is targeted)')

    # the overflow close: reached post vs wanted post, up to trailing blanks
    got = ro[0][1][4]
    want = tuple(d['soD']) + tuple(tail)
    if LC.rstrip0(got) != LC.rstrip0(want):
        raise DeriveError('overflow close mismatch %r vs %r' % (got, want))

    return dict(spec=spec, enc=enc, st0=st0, tail=list(tail),
                far=list(far), p0=p0, mode=mode,
                chi=chi, cho=cho, co=(ro[1], ro[2]),
                ci=((ri[1], ri[2]) if ri else None),
                chz=chz, chp=chp, Z0=Z0, Z1=Z1, P0=P0, P1=P1,
                cz=((rz[1], rz[2]) if rz else None),
                cp=((rp[1], rp[2]) if rp else None),
                A0=A0, A1=A1, B0=B0, B1=ro[0], vis=vis, visi=visi, visx=visx,
                qh=qh, boot=boot, avoid=avoid,
                absd=absd, sset=sset, islack=islack, oslack=oslack,
                nest=nest, opeel=peel,
                ovpost=list(got), ovwant=list(want), val=why)


def slist(qs):
    """A [list St] literal, e.g. [StB; StC; StD]."""
    return '[' + '; '.join(ST[q] for q in (qs or [])) + ']'


def slistc(qs):
    """The same set, for prose: "StB, StC, StD"."""
    return ', '.join(ST[q] for q in (qs or [])) or 'nothing'


def quiet_of(qs):
    return [q for q in range(4) if q not in (qs or [])]


VISI_LEMMA = r"""(** A state that fires ONLY inside the interior lap: [vis_via_ovf] runs to an
    OVERFLOW anchor, so it cannot see one.  This is the interior witness, and
    [LapCertGlueLift.vis_via_int_lift] carries it to every anchor. *)
Lemma visi_@ID@ : forall (l : list lstep) (q : St),
  srun_st tm false true l A0_@ID@ = Some q ->
  forall p j q0, cview p = (j, Some q0) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j q0 E.
  apply (vis_of_run tm Cc false true l A0_@ID@ p j (@ENC@ q0 ++ @TAIL@) []);
    [exact Hst | discriminate | reflexivity | exact (gsi_@ID@ p j q0 E)].
Qed.

"""


def _lift_vis(D):
    """Is [vis_*] stated in [stepn]/[lift] space?  Only for the plain closer:
    [glue_neverqh_lift] takes it that way, while [glue_qh]/[glue_qh_abs] want
    the concrete [csteps] premise and reach it via [vis_csteps_of_lift]."""
    return bool(D.get('islack')) and not (D['qh'] or D['absd'] is not None)


def render(D):
    spec = D['spec']
    ID = mach_id(spec)
    d = ENCDATA[D['enc']]
    N = D.get('nest')
    offset = bool(N and N.get('route') == 'offset')
    P = D.get('opeel')
    # BOTH reindexing routes state the overflow branch at [j = S j'] and hand
    # [p = 1] a concrete lap: the offset route (nested overflow, inner count
    # entering off a power of two) and the PEEL (flat overflow, one more unit
    # copy in the chain's prefix).  Everything that only cares about the
    # INDEX is shared; the two differ in the count each side denotes.
    reix = offset or bool(P)
    # the reindexed branch's outer successor is two up from the lemma's index
    sj = '(S (S j))' if reix else '(S j)'
    ovpost, ovwant = tuple(D['ovpost']), tuple(D['ovwant'])
    body = 'rep %s %s ++ %s' % (clist(d['uD']), sj, clist(ovpost))
    pad = len(ovwant) - len(ovpost)
    if pad < 0:
        # The REACHED post is the longer one -- the lap stopped past the
        # anchor rather than short of it.  Same blank, other side of the
        # equation: nest the surplus on [HD] instead of on [HC].  (The nested
        # route reaches this: its exit chain lands on the outer successor,
        # and landing one blank OVER is as common there as landing one under.)
        n = -pad
        if ovpost[:len(ovwant)] != ovwant or any(ovpost[len(ovwant):]):
            raise DeriveError('overflow close %r vs %r' % (ovpost, ovwant))
        body = ('(' * n + 'rep %s %s ++ %s' % (clist(d['uD']), sj,
                                               clist(ovwant))
                + ''.join(') ++ [S0]' for _ in range(n)))
        hcleft = 'rep %s %s ++ %s' % (clist(d['uD']), sj, clist(ovwant))
        close = 'rewrite !lbl_%s. reflexivity.' % ID
    elif ovwant[:len(ovpost)] != ovpost or any(ovwant[len(ovpost):]):
        raise DeriveError('overflow close %r vs %r' % (ovpost, ovwant))
    elif pad == 0:
        hcleft, close = body, 'reflexivity.'
    else:
        # each surplus cell is one trailing blank, invisible to [lift]
        hcleft = '(' * pad + body + ''.join(') ++ [S0]' for _ in range(pad))
        close = 'rewrite !lbl_%s. reflexivity.' % ID
    # the overflow lap can also stop one blank past the anchor's FAR side;
    # [WTape.lift_app_blank] is that strip on the right
    def far_slack(side, what):
        """The reached FAR word, and how many blanks it carries past the
        anchor's.  [sden] of a rep-free side is [pre ++ post]."""
        if side[1]:
            raise DeriveError('%s far slack: unit run on the far side' % what)
        got, wnt = tuple(side[0]) + tuple(side[4]), tuple(D['far'])
        n = len(got) - len(wnt)
        if n < 1 or got != wnt + (0,) * n:
            raise DeriveError('%s far slack %r vs %r' % (what, got, wnt))
        # nest so each [lift_app_blank] rewrite peels exactly one blank
        return got, ('(' * n + clist(wnt)
                     + ''.join(') ++ [S0]' for _ in range(n)))

    if D.get('oslack'):
        _, ovfar = far_slack(D['B1'][3], 'overflow')
        close = 'rewrite !lift_app_blank. ' + close
    else:
        ovfar = clist(D['far'])
    # [destruct q] makes FOUR goals, so there must be four bullets in state
    # order -- including one per state the lap never reaches.  (An earlier
    # version prepended a single StA bullet and then listed only the reached
    # states, which silently misaligns as soon as TWO states are missing.)
    vis = []
    for q in range(4):
        if q in D.get('visx', {}):
            # the state fires only in the EXIT half of a NESTED overflow;
            # vis_via_fill supplies the exponentially long middle
            pull = ('' if _lift_vis(D) else
                    '    apply (vis_csteps_of_lift tm Cc).\n')
            if reix:
                # the reindexed anchor: destruct the outer index; p = 1 gets
                # the concrete witness
                vis.append('  - (* %s: fires in the exit half of the overflow *)\n'
                           '%s'
                           '    apply (vis_via_ovf_lift tm Cc lapil_%s %s).\n'
                           '    intros p1 j1 E1. destruct j1 as [|j1\'].\n'
                           '    + rewrite (cview_none_shape p1 0 E1).\n'
                           '      apply (vis_lift_of_csteps tm Cc). exact visz_%s_%s.\n'
                           '    + exact (visx_%s %s %s ltac:(vm_compute; reflexivity)\n'
                           '                   p1 j1\' E1).'
                           % (ST[q], pull, ID, ST[q], ST[q], ID, ID,
                              cchain(D['visx'][q]), ST[q]))
                continue
            vis.append('  - (* %s: fires in the exit half of the overflow *)\n'
                       '%s'
                       '    apply (vis_via_ovf_lift tm Cc lapil_%s %s).\n'
                       '    intros p1 j1 E1.\n'
                       '    exact (visx_%s %s %s ltac:(vm_compute; reflexivity)\n'
                       '                   p1 j1 E1).'
                       % (ST[q], pull, ID, ST[q], ID, cchain(D['visx'][q]),
                          ST[q]))
            continue
        if q not in D['vis'] and q not in D.get('visi', {}):
            if D['absd'] is not None:
                vis.append('  - (* %s: not in the reached set *)\n'
                           '    exfalso; cbn in Hq; intuition discriminate.' % ST[q])
            else:
                vis.append('  - (* %s: quiet -- see the closing theorem *)\n'
                           '    exfalso; exact (Hq eq_refl).' % ST[q])
            continue
        if q in D.get('visi', {}):
            # interior-only: the witness is a prefix of the INTERIOR chain,
            # carried to every anchor by vis_via_int_lift (which needs the
            # FULL lap, i.e. lap_*, not just the interior branch)
            vis.append('  - (* %s: fires only in the interior lap *)\n'
                       '    apply (vis_csteps_of_lift tm Cc).\n'
                       '    apply (vis_via_int_lift tm Cc lap_%s %s).\n'
                       '    intros p1 j1 r1 E1. apply (vis_lift_of_csteps tm Cc).\n'
                       '    apply (visi_%s %s %s ltac:(vm_compute; reflexivity)\n'
                       '                   p1 j1 r1 E1).'
                       % (ST[q], ID, ST[q], ID, cchain(D['visi'][q]), ST[q]))
            continue
        pre = D['vis'][q]
        if not pre:
            vis.append('  - (* %s: the anchor state *)\n'
                       '    exists 0. eexists. split; reflexivity.' % ST[q])
        elif D.get('islack'):
            # the [lift] twin: [vis_via_ovf_lift] chains the interior laps in
            # [stepn] space, and the per-state witness is the SAME [viso_*]
            # run pushed through [vis_lift_of_csteps].  When the closer is
            # [glue_qh]/[glue_qh_abs] -- which have no lift twin and need none
            # -- [vis_csteps_of_lift] pulls the result back to their concrete
            # premise.
            pull = ('' if _lift_vis(D) else
                    '    apply (vis_csteps_of_lift tm Cc).\n')
            if reix:
                vis.append('  - (* %s *)\n'
                           '%s'
                           '    apply (vis_via_ovf_lift tm Cc Hi %s).\n'
                           '    intros p1 j1 E1. destruct j1 as [|j1\'].\n'
                           '    + rewrite (cview_none_shape p1 0 E1).\n'
                           '      apply (vis_lift_of_csteps tm Cc). exact visz_%s_%s.\n'
                           '    + apply (vis_lift_of_csteps tm Cc).\n'
                           '      apply (viso_%s %s %s ltac:(vm_compute; reflexivity)\n'
                           '                   p1 j1\' E1).'
                           % (ST[q], pull, ST[q], ST[q], ID, ID,
                              cchain(pre), ST[q]))
            else:
                vis.append('  - (* %s *)\n'
                           '%s'
                           '    apply (vis_via_ovf_lift tm Cc Hi %s).\n'
                           '    intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).\n'
                           '    apply (viso_%s %s %s ltac:(vm_compute; reflexivity)\n'
                           '                   p1 j1 E1).'
                           % (ST[q], pull, ST[q], ID, cchain(pre), ST[q]))
        elif reix:
            vis.append('  - (* %s *)\n'
                       '    apply (vis_via_ovf tm Cc Hi %s).\n'
                       '    intros p1 j1 E1. destruct j1 as [|j1\'].\n'
                       '    + rewrite (cview_none_shape p1 0 E1). exact visz_%s_%s.\n'
                       '    + exact (viso_%s %s %s ltac:(vm_compute; reflexivity)\n'
                       '                   p1 j1\' E1).'
                       % (ST[q], ST[q], ST[q], ID, ID, cchain(pre), ST[q]))
        else:
            vis.append('  - (* %s *)\n'
                       '    apply (vis_via_ovf tm Cc Hi %s), viso_%s\n'
                       '      with (l := %s).\n'
                       '    vm_compute; reflexivity.'
                       % (ST[q], ST[q], ID, cchain(pre)))
    # the peeled branch's two leftovers, both at p = 1: the concrete lap and
    # one concrete visit witness per state the overflow bullets cover
    peelglue = ''
    if P:
        peelglue = LAPZ_LEMMA.replace('@NZ@', str(P['n0'])) + '\n\n'
        for q in sorted(set(D.get('vis') or {})):
            if not D['vis'][q]:
                continue                     # the anchor state needs no run
            if q not in P['visz']:
                raise DeriveError('peel: no p=1 witness for state %s' % LAB[q])
            peelglue += (VISZ_LEMMA.replace('@STQ@', ST[q])
                         .replace('@KQ@', str(P['visz'][q])) + '\n\n')
    islack = bool(D.get('islack'))
    if islack and D['mode'] != 'one':
        raise DeriveError('lift route: only mode=one is wired')
    # [glue_neverqh_lift] takes the visit premise in [stepn] space;
    # [glue_qh]/[glue_qh_abs] want it concrete and get there through
    # [vis_csteps_of_lift], so they need no lift twin.
    lift_vis = _lift_vis(D)
    if islack:
        igot, ifarnest = far_slack(D['A1'][3], 'interior')
        farb, farnest = clist(igot), ifarnest
    else:
        farb = farnest = clist(D['far'])
    reps = {
        '@OVFDEFS@': (((NC.nest_defs_offset if offset else NC.nest_defs)
                       (D, ENCDATA, clist, cconf, cchain, ST, ID))
                      if N else FLAT_OVF_DEFS),
        '@OVFCASE@': (NC.NEST_OVFCASE if N
                      else FLAT_OVF_CASE_PEEL if P else FLAT_OVF_CASE),
        '@NESTGLUE@': (((NC.nest_glue_offset if offset else NC.nest_glue)
                        (D, ENCDATA, clist, cconf, cchain, ST, ID))
                       + '\n\n' if N else peelglue),
        # [cview_none_shape] (p = 1 from cview p = (1, None)) lives in
        # IXPGadgets, and the peeled branch is the only FLAT route that needs
        # it -- the nested routes pull it in through @NESTIMPORT@ already.
        '@NESTIMPORT@': ' IXPGadgets' if P else '',
        '@PREF@': (NEST_PREFIX if N
                   else AVOID_PREFIX if D.get('avoid')
                   else PEEL_PREFIX if P else PREFIX),
        '@ID@': ID, '@SPEC@': spec,
        '@GLUELIFT@': ' LapCertGlueLift' if islack else '',
        '@FARB@': farb, '@FARNEST@': farnest,
        '@VISIL@': VISI_LEMMA if D.get('visi') else '',
        '@LAPICASE@': (
            '  - destruct (lapi_@ID@ p j q0 E) as (n & c\' & Hn & Hrun & Hlift).\n'
            '    exists n, c\'. split; [exact Hrun | split; [exact Hlift | exact Hn]].'
            if islack else
            '  - destruct (lapi_@ID@ p j q0 E) as (n & Hn & Hrun).\n'
            '    exists n, (Cc (Pos.succ p)).\n'
            '    split; [exact Hrun | split; [reflexivity | exact Hn]].'),
        '@VISCONC@': ('exists k e, stepn tm k (lift (Cc p)) = Some e /\\ fst e = q'
                      if lift_vis else
                      'exists k c, csteps tm k (Cc p) = Some c /\\ fst c = q'),
        '@VISHI@': (
            'forall p0 j q0, cview p0 = (j, Some q0) ->\n'
            '            exists n c\', 0 < n /\\ csteps tm n (Cc p0) = Some c\'\n'
            '                         /\\ lift c\' = lift (Cc (Pos.succ p0))'
            if islack else
            'forall p0 j q0, cview p0 = (j, Some q0) ->\n'
            '            exists n, 0 < n /\\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0))'),
        # the Coq FIXPOINT name; for the generated alphabets it is Ap_<tag>,
        # not the ENCDATA key
        '@ENC@': d.get('fn', D['enc']),
        '@CVSJ@': 'S (S j)' if reix else 'S j',
        '@NNJ@': '(S j)' if reix else 'j',
        '@B1B@': '2' if offset else '1',
        '@B1SJ@': '(S (S j))' if offset else '(S j)',
        '@ENCMOD@': d['mod'], '@SOME@': d['some'], '@NONE@': d['none'],
        '@ST0@': ST[D['st0']], '@TAIL@': clist(D['tail']),
        '@FAR@': clist(D['far']),
        '@TABLE@': coq_table(spec),
        '@B0@': cconf(D['B0']), '@B1@': cconf(D['B1']),
        '@CHO@': cchain(D['cho']),
        '@CAO@': str(D['co'][0]), '@CBO@': str(D['co'][1]),
        '@US@': clist(d['uS']), '@UD@': clist(d['uD']),
        '@OBSP@': ('1' if offset
                   else str(d['obS'] - 1 if d['obS'] >= 1 else 0)),
        '@CNTP@': '(S j)' if offset else 'j',
        '@HDLEFT@': body, '@HCLEFT@': hcleft, '@OVFAR@': ovfar,
        '@CLOSE@': close, '@P0@': str(D['p0']), '@BOOT@': str(D['boot']),
        '@VISHYP@': ('forall p q, In q %s ->' % slist(D['sset'])
                     if D['absd'] is not None
                     else 'forall p q, q <> StA ->'
                       if D['qh'] or D.get('avoid')
                     else 'forall p q,'),
        '@VISINTRO@': ('intros p q Hq'
                       if D['qh'] or D['absd'] is not None or D.get('avoid')
                       else 'intros p q'),
        '@VISA@': '',
        '@AVIMP@': ' LapGlueQuiet' if D.get('avoid') else '',
        '@AVIMP2@': ' LapAvoid' if D.get('avoid') else '',
        '@AVDEFS@': (AVOID_DEFS_ONE if D['mode'] == 'one'
                     else AVOID_DEFS_SPLIT) if D.get('avoid') else '',
        '@AVLAPI@': (AVOID_LAPI_ONE if D['mode'] == 'one'
                     else AVOID_LAPI_SPLIT) if D.get('avoid') else '',
        '@S0@': str(D['avoid']['s0']) if D.get('avoid') else '',
        '@DD@': (str(D['boot'] - D['avoid']['s0'] - 1)
                 if D.get('avoid') else ''),
        '@FINAL@': (ABS_CLOSE if D['absd'] is not None
                    else AVOID_CLOSE if D.get('avoid')
                    else QH_CLOSE if D['qh']
                    else NQH_CLOSE_LIFT if lift_vis else NQH_CLOSE)
                    .replace('@ID@', ID).replace('@P0@', str(D['p0']))
                    .replace('@SSETC@', slistc(D['sset']))
                    .replace('@SSET@', slist(D['sset']))
                    .replace('@QUIETC@', slistc(quiet_of(D['sset'])))
                    .replace('@ABSD@', str(D['absd'])),
        '@NI@': ('%d*j+%d' % D['ci'] if D['mode'] == 'one'
                 else 'j=0: %d ; j=S j\': %d*j\'+%d'
                      % (D['cz'][1], D['cp'][0], D['cp'][1])),
        '@NO@': ('boot %d*j+%d, then the inner counter\'s own laps to the\n'
                 '                                           all-ones fill, then exit %d*j+%d'
                 % (D['nest']['cb'][0], D['nest']['cb'][1],
                    D['co'][0], D['co'][1]) if D.get('nest')
                 else '%d*j+%d steps at j = S j\', %d at p = 1'
                      % (D['co'] + (P['n0'],)) if P
                 else '%d*j+%d steps' % D['co']),
        '@NZ@': str(P['n0']) if P else '',
        '@INTERIOR@': (INT_ONE if D['mode'] == 'one' else INT_SPLIT),
        '@GLUEI@': (GLUE_ONE_LIFT if islack
                    else GLUE_ONE if D['mode'] == 'one' else GLUE_SPLIT),
        '@A0@': cconf(D['A0']), '@A1@': cconf(D['A1']),
        '@CHI@': cchain(D['chi']) if D['chi'] else '[]',
        '@CAI@': str(D['ci'][0]) if D['ci'] else '0',
        '@CBI@': str(D['ci'][1]) if D['ci'] else '0',
        '@Z0@': cconf(D['Z0']), '@Z1@': cconf(D['Z1']),
        '@P0C@': cconf(D['P0']), '@P1C@': cconf(D['P1']),
        '@CHZ@': cchain(D['chz']) if D['chz'] else '[]',
        '@CHP@': cchain(D['chp']) if D['chp'] else '[]',
        '@CAZ@': str(D['cz'][0]) if D['cz'] else '0',
        '@CBZ@': str(D['cz'][1]) if D['cz'] else '0',
        '@CAP@': str(D['cp'][0]) if D['cp'] else '0',
        '@CBP@': str(D['cp'][1]) if D['cp'] else '0',
        '@VAL@': D['val'], '@VISITS@': '\n'.join(vis),
    }
    if N:
        reps.update((NC.nest_reps_offset if offset else NC.nest_reps)
                    (D, ENCDATA, clist, cconf, cchain, ST, ID))
    out = HEADER
    for _ in range(3):          # the INTERIOR/GLUEI blocks themselves hold holes
        for k, v in reps.items():
            out = out.replace(k, v)
    return out


def coqc(path):
    r = subprocess.run(['coqc', '-native-compiler', 'no', '-Q', 'theories',
                        'BBB4', path], cwd=REPO, capture_output=True, text=True)
    return r.returncode == 0, (r.stderr or r.stdout)[-1500:]


def anchors(spec):
    """Candidate (edge, tail, p0, enc) anchor families, cheapest first.  The
    ENCODING IS SEARCHED, never hard-coded -- wave-12's lesson."""
    out = []
    for finder in (derive_tail_best, derive_tail_best_far):
        try:
            a = finder(spec, encnames=ENCS)
        except (DeriveError, Halt_):
            continue
        except Exception:                                     # noqa: BLE001
            continue
        a = tuple(a) + ((),) if len(a) == 4 else tuple(a[:4]) + (tuple(a[4]),)
        if a[3] in ENCDATA and a not in out:
            out.append(a)
    return out


def _cost_str(D):
    """The interior cost, in whichever shape this machine derived.

    The j = 0 split (wave-13 section 9a) leaves [ci] None, so formatting it
    unconditionally raised TypeError -- OUTSIDE the try, so it killed the
    whole run at the first split-mode machine rather than skipping it.  Any
    list containing one boarded nothing after it."""
    if D['mode'] == 'one':
        return '%d*j+%d' % D['ci']
    return "j=0:%d,%d*j'+%d" % (D['cz'][1], D['cp'][0], D['cp'][1])


def process(spec, do_emit, force=False):
    """Try the machine directly (counter grows LEFT); if that finds nothing,
    try its MIRROR and transfer the conclusion back through
    Mirror.mirror_never_qh -- the wave-9 route, no new theory.  Growth
    direction is thus searched, not declared."""
    last = None
    for mirrored in (False, True):
        dspec = mirror_spec(spec) if mirrored else spec
        for (edge, tail, p0, enc, far) in anchors(dspec):
            try:
                D = derive(dspec, edge, tail, p0, enc, far)
            except (DeriveError, Halt_) as e:
                last = str(e)
                continue
            except Exception as e:                            # noqa: BLE001
                last = '%s: %s' % (type(e).__name__, e)
                continue
            tag = enc + ('/mirror' if mirrored else '')
            if not do_emit:
                return dict(spec=spec, ok=True, enc=tag,
                            ni=_cost_str(D), no='%d*j+%d' % D['co'])
            pref = (NEST_PREFIX if D.get('nest')
                    else AVOID_PREFIX if D.get('avoid')
                    else PEEL_PREFIX if D.get('opeel') else PREFIX)
            path = os.path.join(OUTDIR, '%s_%s.v' % (pref, mach_id(spec)))
            if os.path.exists(path) and not force:
                return dict(spec=spec, ok=True, enc=tag, file=path,
                            skipped=True, ni=_cost_str(D),
                            no='%d*j+%d' % D['co'])
            try:
                src = render(D)
                if mirrored:
                    src = mirrorize(src, spec, dspec)
            except (DeriveError, RuntimeError) as e:
                last = str(e)
                continue
            open(path, 'w').write(src)
            ok, log = coqc(os.path.relpath(path, REPO))
            if not ok:
                os.remove(path)
                lg = [l for l in log.strip().splitlines() if l.strip()]
                last = 'coqc: ' + (lg[-1] if lg else '?')
                continue
            return dict(spec=spec, ok=True, enc=tag, file=path,
                        ni=_cost_str(D), no='%d*j+%d' % D['co'])
    # The CASCADE route (wave-24 built, wave-25 boards): the overflow phase
    # is a descending-octave cascade, so neither one chain nor the
    # nested/offset compositions can express it -- the level induction in
    # [Counters/NestedLapCascade.v] can.  Tried LAST: its extractor replays
    # whole overflow phases against the raw simulator and is by far the most
    # expensive derive.  (Imported lazily; cascade_emit imports this module.)
    try:
        import cascade_emit as CE
        r = CE.process_board(spec, do_emit, force)
        if r.get('ok'):
            return r
        last = r.get('why') or last
    except Exception as e:                                     # noqa: BLE001
        last = 'cascade: %s' % e
    return dict(spec=spec, ok=False, why=last or 'no anchor')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list')
    ap.add_argument('--spec')
    ap.add_argument('--emit', action='store_true')
    ap.add_argument('--json')
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--force', action='store_true')
    a = ap.parse_args()

    specs = ([a.spec] if a.spec else
             [l.strip() for l in open(a.list) if l.strip()])
    if a.limit:
        specs = specs[:a.limit]

    res, nok = [], 0
    for i, spec in enumerate(specs):
        r = process(spec, a.emit, a.force)
        res.append(r)
        nok += bool(r['ok'])
        print('%5d/%d %-40s %s' % (i + 1, len(specs), spec,
                                   ('OK %s %s %s' % (r['enc'], r['ni'], r['no']))
                                   if r['ok'] else 'no: %s' % r['why'][:90]),
              flush=True)
    print('\n%d / %d derived' % (nok, len(specs)))
    if a.json:
        json.dump(res, open(a.json, 'w'), indent=1)


if __name__ == '__main__':
    main()
