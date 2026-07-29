#!/usr/bin/env python3
"""UNTRUSTED: the CASCADE overflow branch, emitted.

`docs/CASCADE_EXIT.md`.  One overflow phase of the exp-counter bucket runs
`2j+1` inner counts down a descending octave cascade, so no fixed list of
chains expresses it and `nestcert.MAXCOUNTS` measured 0 of 87.  What does is
the level induction in `theories/Counters/NestedLapCascade.v`, whose per-level
step this module emits: the family is stated at an ARBITRARY TAIL, the two
per-level chains are ordinary single-index chains, and the growing part of the
tail is the sside's own opaque region.

The endpoints and every chain come from `nestcert.cascade_endpoints`, which
reads them off a measured phase and gates them; this module only renders them.
Like every emitter here it is untrusted -- the kernel re-runs `srun` on each
chain and re-checks each glue lemma, so a wrong framing fails to compile
rather than proving something false.

Usage:
  cascade_emit.py --proto SPEC [-K 7] [-o FILE]
"""
import argparse
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

import emit_lapcert as E                                       # noqa: E402
import nestcert as NC                                          # noqa: E402
import cascade_probe as CP                                     # noqa: E402
from emit_interleave import (LAB, ST, clist, coq_table)        # noqa: E402


def _fill(tpl, reps):
    for k, v in reps.items():
        tpl = tpl.replace(k, v)
    return tpl


def _cat(parts):
    """A Coq list expression for a concatenation of concrete chunks."""
    return ' ++ '.join(p for p in parts if p and p != '[]') or '[]'


# --------------------------------------------------------------- the module ---

PROTO_DOC = r'''(** * CASC_@ID@: the CASCADE overflow branch of @SPEC@.

    Auto-emitted by tools/counters/cascade_emit.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  This module carries the
    OVERFLOW branch alone -- the piece `docs/CASCADE_EXIT.md` is about -- and
    proves it in the form [LapDecider.LapStep] asks for, so a full board is
    this plus the unchanged interior branch, bootstrap, visits and closer.

    One overflow phase is a DESCENDING-OCTAVE CASCADE: @NLEV@ inner counts,
    `2j+1` of them, down from level j to level 0, each level's tail one unit
    longer than the last, then a closing sweep to the outer successor.  The
    number of counts is AFFINE IN j, which is why no fixed list of chains
    expresses it; the induction is [NestedLapCascade.cascade_overflow].

    Every level runs the SAME counter over the SAME digits.  What grows is the
    region past them, and the counter never reads it -- so [Cin] below is
    stated at an ARBITRARY TAIL [T], one interior-lap certificate discharges
    every level at once, and the two per-level chains are ordinary
    single-index chains with the growth in the sside's opaque region.

      inner lap        @CAN@*i+@CBN@ steps, at any tail
      boot             @CAB@*j+@CBB@         -> the level-j count
      B(l+1) -> A(l)   @CABA@*l+@CBBA@       [the chain section 4c left open]
      A(l)   -> B(l)   @CAAB@*l+@CBAB@
      close            @CACL@*j+@CBCL@       -> the outer successor

    Differentially validated against the raw simulator -- step counts AND
    exact configurations, every count of every level of every phase:
    @NVAL@.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
'''

# The board header.  Same machine facts, different framing: this one IS a
# board -- the whole [NeverQuasiHaltsSt] theorem -- not an overflow-branch
# regression.
BOARD_DOC = r'''(** * CASB_@ID@: machine @SPEC@, boarded by the CASCADE route.

    Auto-emitted by tools/counters/cascade_emit.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the @ENC@ digit alphabet, anchored at

      Cc p = (@ST0@, (@ENC@ p ++ @TAIL@, S0, @FAR@))

    The INTERIOR branch is an ordinary lap certificate (@NI@ steps,
    closing @ICLO@).  The OVERFLOW branch is a DESCENDING-OCTAVE
    CASCADE: @NLEV@ inner counts, `2j+1` of them, down from level j to
    level 0, each level's tail one unit longer than the last, then a
    closing sweep to the outer successor.  The number of counts is
    AFFINE IN j, which is why no fixed list of chains expresses it; the
    induction is [NestedLapCascade.cascade_overflow].

    Every level runs the SAME counter over the SAME digits.  What grows is the
    region past them, and the counter never reads it -- so [Cin] below is
    stated at an ARBITRARY TAIL [T], one interior-lap certificate discharges
    every level at once, and the two per-level chains are ordinary
    single-index chains with the growth in the sside's opaque region.

      inner lap        @CAN@*i+@CBN@ steps, at any tail
      boot             @CAB@*j+@CBB@         -> the level-j count
      B(l+1) -> A(l)   @CABA@*l+@CBBA@
      A(l)   -> B(l)   @CAAB@*l+@CBAB@
      close            @CACL@*j+@CBCL@       -> the outer successor

    VISITS: only the boot and the closing sweep fire at EVERY outer index
    (at j = 0 there is no descent), so a state firing in neither the boot
    chain nor the interior lap must fire in the sweep, reached through the
    whole cascade by [NestedLapCascade.cascade_vis].

    Differentially validated against the raw simulator -- step counts AND
    exact configurations: @IVAL@ (interior); every count of every level of
    every overflow phase, @NVAL@.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
'''

# The octave-down board header.
BOARD_DOC_LOW = r'''(** * CASB_@ID@: machine @SPEC@, boarded by the CASCADE route (octave down).

    Auto-emitted by tools/counters/cascade_emit.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the @ENC@ digit alphabet, anchored at

      Cc p = (@ST0@, (@ENC@ p ++ @TAIL@, S0, @FAR@))

    The INTERIOR branch is an ordinary lap certificate (@NI@ steps,
    closing @ICLO@).  The OVERFLOW branch is a DESCENDING-OCTAVE CASCADE
    sitting ONE OCTAVE DOWN: at outer index S j' the boot lands on the top
    level's FIRST count A(j'), one A->B hop enters the standard descent
    ([fill_hop] hides the count), and after level 0 the machine runs ONE
    MORE ASCENDING COUNT at octave j+1 -- the same inner family over the
    constant tail [BT] -- before the outer successor.  The p = 1 overflow
    (outer index 0) has no cascade at all and is a concrete lap.  The
    induction is [NestedLapCascade.cascade_overflow] at [d0 = 1].

      inner lap        @CAN@*i+@CBN@ steps, at any tail
      boot             @CAB@*j+@CBB@  at the REINDEXED anchor -> A(top)
      B(l+1) -> A(l)   @CABA@*l+@CBBA@
      A(l)   -> B(l)   @CAAB@*l+@CBAB@
      closeA           @CACA@*j+@CBCA@  level 0 -> the closing count
      closeB           @CACB@*j+@CBCB@  its fill -> the outer successor

    VISITS: every state fires inside the boot chain, whose witness covers
    the reindexed anchors; the p = 1 anchor gets concrete [visz_]
    witnesses (the offset route's device).

    Differentially validated against the raw simulator -- step counts AND
    exact configurations: @IVAL@ (interior); @NVAL@.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
'''

PROTO_CORE = r'''From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape MonoCounter JpCounter IXPGadgets
                                  LapCertGlue LapCertGlueLift NestedLap
                                  NestedLapLift NestedLapCascade@EXTRAMOD@.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_@ID@ (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).
Local Notation mk := mk_@ID@.

(** @DSPEC@ -- the table every lemma below runs on. *)
Definition tm_@ID@ : TM := fun q s => match q, s with
@TABLE@ end.
Local Notation tm := tm_@ID@.

Definition Cc_@ID@ (p : positive) : cconf := (@ST0@, (@ENC@ p ++ @TAIL@, S0, @FAR@)).
Local Notation Cc := Cc_@ID@.

(** A chain accepted up to [lift] can stop a blank past the anchor -- the
    leniency [NestedLapLift] measured to be the binding one on this bucket --
    and [CTape.lift_side] cannot see it.  Every landing bridge below ends
    here, so it is stated before the first of them. *)
Lemma lbl_@ID@ : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.


(** ** The inner family, at an ARBITRARY tail

    [T] is the cascade's growing region.  The counter's own laps never read
    it, so quantifying over it costs nothing and buys every level. *)
Definition Cin_@ID@ (T : list Sym) (v : positive) : cconf :=
  (@STI@, (@ENCI@ v ++ T, S0, @FARI@)).
Local Notation Cin := Cin_@ID@.

Definition Uc_@ID@ : list Sym := @UNIT@.
Local Notation Uc := Uc_@ID@.

(** The two tails a level carries: the count that ENTERS it and the count the
    level's own transition produces.  One unit longer per level down. *)
Definition TB_@ID@ (m : nat) : list Sym := @HEADB@ ++ rep Uc (m + @D0@).
Definition TA_@ID@ (m : nat) : list Sym := @HEADA@ ++ rep Uc (m + @D0@).
Local Notation TB := TB_@ID@.
Local Notation TA := TA_@ID@.

(** The level-[l] entry configuration, with [m] units of tail beyond the
    top level's.  Both indices are explicit and both are built by [S]: a
    single index would force [j - l] into an anchor, which is the wave-15
    index-shift trap. *)
Definition Dc_@ID@ (l m : nat) : cconf := Cin (TB m) (pow2 l).
Local Notation Dc := Dc_@ID@.

(** [E (2^n)] and [E (2^(n+1)-1)]: the value each count starts and ends at. *)
Lemma epow2_@ID@ : forall n, @ENCI@ (pow2 n) = rep @UDI@ n ++ @SODI@.
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma efill_@ID@ : forall n, @ENCI@ (fill (pow2 n)) = rep @USI@ n ++ @SOSI@.
Proof.
  intro n.
  destruct (@ENCMODI@.@NONEI@ (fill (pow2 n)) n (cview_fill_pow2 n)) as (H & _).
  exact H.
Qed.

(** ** The inner family's own interior lap -- ordinary, affine, tail-blind *)

Definition AI0_@ID@ : sconf := @AI0@.
Definition AI1_@ID@ : sconf := @AI1@.
Definition chn_@ID@ : list lstep := @CHN@.

Lemma run_inner_@ID@ :
  srun tm false true chn_@ID@ AI0_@ID@ = Some (AI1_@ID@, @CAN@, @CBN@).
Proof. vm_compute. reflexivity. Qed.

Lemma gsn_@ID@ : forall T v i q0, cview v = (i, Some q0) ->
  Cin T v = cden (@ENCI@ q0 ++ T) [] i AI0_@ID@.
Proof.
  intros T v i q0 Ev. destruct (@ENCMODI@.@SOMEI@ v i q0 Ev) as (H1 & _).
  unfold Cin_@ID@, cden, AI0_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. rewrite H1.
  cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
  reflexivity.
Qed.

Lemma gen_@ID@ : forall T v i q0, cview v = (i, Some q0) ->
  lift (cden (@ENCI@ q0 ++ T) [] i AI1_@ID@) = lift (Cin T (Pos.succ v)).
Proof.
  intros T v i q0 Ev. destruct (@ENCMODI@.@SOMEI@ v i q0 Ev) as (_ & H2).
  unfold Cin_@ID@, cden, AI1_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H2. cbn [rep app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?app_nil_r.
@FARN@  rewrite ?lift_app_blank. reflexivity.
Qed.

(** The lap, up to [lift] and at every tail at once -- this is
    [NestedLapCascade]'s [Hin]. *)
Lemma lapin_@ID@ : forall T v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin T v) = Some c'
               /\ lift c' = lift (Cin T (Pos.succ v)).
Proof.
  intros T v i q0 Ev.
  exists (@CAN@ * i + @CBN@), (cden (@ENCI@ q0 ++ T) [] i AI1_@ID@).
  split; [lia|]. split; [| exact (gen_@ID@ T v i q0 Ev)].
  rewrite (gsn_@ID@ T v i q0 Ev).
  exact (srun_sound tm false true chn_@ID@ AI0_@ID@ AI1_@ID@ @CAN@ @CBN@
           run_inner_@ID@ (@ENCI@ q0 ++ T) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** ** The four chains *)

Definition B0_@ID@ : sconf := @B0@.
Definition B1_@ID@ : sconf := @B1@.

(** *** boot: the outer overflow anchor -> the level-j count *)
Definition BB1_@ID@ : sconf := @BB1@.
Definition chb_@ID@ : list lstep := @CHB@.

Lemma run_boot_@ID@ :
  srun tm true true chb_@ID@ B0_@ID@ = Some (BB1_@ID@, @CAB@, @CBB@).
Proof. vm_compute. reflexivity. Qed.

(** *** B(S l) fill -> A(l) start.  Section 4c of the brief left this one
    open: its turnaround walks back out over cells it has just written and
    runs one short unless a whole unit is PEELED out of the count, and its eat
    reads one cell INTO the growing region -- that misread is what ends the
    eat -- so its opaque split sits one cell deeper than A->B's. *)
Definition BA0_@ID@ : sconf := @BA0@.
Definition BA1_@ID@ : sconf := @BA1@.
Definition chBA_@ID@ : list lstep := @CHBA@.

Lemma run_BA_@ID@ :
  srun tm @ELBA@ true chBA_@ID@ BA0_@ID@ = Some (BA1_@ID@, @CABA@, @CBBA@).
Proof. vm_compute. reflexivity. Qed.

(** *** A(l) fill -> B(l) start, the level's second half. *)
Definition AB0_@ID@ : sconf := @AB0@.
Definition AB1_@ID@ : sconf := @AB1@.
Definition chAB_@ID@ : list lstep := @CHAB@.

Lemma run_AB_@ID@ :
  srun tm @ELAB@ true chAB_@ID@ AB0_@ID@ = Some (AB1_@ID@, @CAAB@, @CBAB@).
Proof. vm_compute. reflexivity. Qed.

(** *** the closing sweep: the level-0 count -> the outer successor.  Unlike
    the per-level chains this one READS the whole grown tail, so it is affine
    in [j] and its tail is a rep rather than an opaque region. *)
Definition CL0_@ID@ : sconf := @CL0@.
Definition CL1_@ID@ : sconf := @CL1@.
Definition chCL_@ID@ : list lstep := @CHCL@.

Lemma run_close_@ID@ :
  srun tm true true chCL_@ID@ CL0_@ID@ = Some (CL1_@ID@, @CACL@, @CBCL@).
Proof. vm_compute. reflexivity. Qed.

(** The sweep stops @CPAD@/@CFARP@ trailing blanks past the outer successor's
    anchor -- [lift] cannot see them, but the syntactic form has to be
    bridged, and after normalisation the side is one fused literal, so the
    blanks are re-split rather than rewritten away. *)
Lemma gcx_@ID@ : forall j,
  lift (cden [] [] j CL1_@ID@) = lift (cden [] [] j B1_@ID@).
Proof.
  intro j.
  assert (HD : cden [] [] j CL1_@ID@ = (@ST0@, (@CLEFT@, S0, @CFARE@))).
  { unfold cden, CL1_@ID@, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (j + 1) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HE : cden [] [] j B1_@ID@ = (@ST0@, (@CLBASE@, S0, @CFARB@))).
  { unfold cden, B1_@ID@, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (j + 1) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  rewrite HD, HE. rewrite ?lbl_@ID@. rewrite ?lift_app_blank. reflexivity.
Qed.

(** ** The per-level glue

    The opaque region each chain carries, as a function of the level's tail
    length.  Every exponent is built by [S] and [+]; none is a subtraction. *)
Definition XBA_@ID@ (m : nat) : list Sym := @XBA@.
Definition XAB_@ID@ (m : nat) : list Sym := @XAB@.

Lemma gBAs_@ID@ : forall l m,
  Cin (TB m) (fill (pow2 (S l))) = cden (XBA_@ID@ m) [] l BA0_@ID@.
Proof.
  intros l m.
  unfold Cin_@ID@, TB_@ID@, XBA_@ID@, Uc_@ID@, cden, BA0_@ID@, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite efill_@ID@.
@IXBAS@  rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma gBAd_@ID@ : forall l m,
  lift (cden (XBA_@ID@ m) [] l BA1_@ID@) = lift (Cin (TA (S m)) (pow2 l)).
Proof.
  intros l m.
  unfold Cin_@ID@, TA_@ID@, XBA_@ID@, Uc_@ID@, cden, BA1_@ID@, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite epow2_@ID@.
@IXBAD@  rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r.
@FARBA@  rewrite ?lift_app_blank. reflexivity.
Qed.

Lemma gABs_@ID@ : forall l m,
  Cin (TA (S m)) (fill (pow2 l)) = cden (XAB_@ID@ m) [] l AB0_@ID@.
Proof.
  intros l m.
  unfold Cin_@ID@, TA_@ID@, XAB_@ID@, Uc_@ID@, cden, AB0_@ID@, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite efill_@ID@.
@IXABS@  rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma gABd_@ID@ : forall l m,
  lift (cden (XAB_@ID@ m) [] l AB1_@ID@) = lift (Cin (TB (S m)) (pow2 l)).
Proof.
  intros l m.
  unfold Cin_@ID@, TB_@ID@, XAB_@ID@, Uc_@ID@, cden, AB1_@ID@, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite epow2_@ID@.
@IXABD@  rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r.
@FARAB@  rewrite ?lift_app_blank. reflexivity.
Qed.

(** ONE LEVEL.  Two counts, each an [exists n] hiding a [Theta(2^l)], and the
    two chains between them -- and it is the SAME step at every level, which
    is the whole content of the cascade. *)
Lemma hstep_@ID@ : forall l m,
  exists n, stepn tm n (lift (Dc (S l) m)) = Some (lift (Dc l (S m))).
Proof.
  intros l m. unfold Dc_@ID@.
  apply (level_hop tm Cin lapin_@ID@ (TB m) (TA (S m))
                   (pow2 (S l)) (pow2 l)).
  - exists (@CABA@ * l + @CBBA@). rewrite gBAs_@ID@, <- gBAd_@ID@.
    apply csteps_lift.
    exact (srun_sound tm @ELBA@ true chBA_@ID@ BA0_@ID@ BA1_@ID@ @CABA@ @CBBA@
             run_BA_@ID@ (XBA_@ID@ m) [] l
             ltac:(@ELBAT@) ltac:(reflexivity)).
  - exists (@CAAB@ * l + @CBAB@). rewrite gABs_@ID@, <- gABd_@ID@.
    apply csteps_lift.
    exact (srun_sound tm @ELAB@ true chAB_@ID@ AB0_@ID@ AB1_@ID@ @CAAB@ @CBAB@
             run_AB_@ID@ (XAB_@ID@ m) [] l
             ltac:(@ELABT@) ltac:(reflexivity)).
Qed.

(** ** The outer glue: boot in, sweep out *)

Lemma gso_@ID@ : forall p j, cview p = (S j, None) -> Cc p = cden [] [] j B0_@ID@.
Proof.
  intros p j Ev. destruct (@ENCMOD@.@NONE@ p j Ev) as (H1 & _).
  unfold Cc_@ID@, cden, B0_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + @OBSP@) with (@CNTP@) by lia.
  rewrite H1; cbn [rep app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?app_nil_r. reflexivity.
Qed.

Lemma geo_@ID@ : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_@ID@) = lift (Cc (Pos.succ p)).
Proof.
  intros p j Ev. destruct (@ENCMOD@.@NONE@ p j Ev) as (_ & H2).
  unfold Cc_@ID@, cden, B1_@ID@; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 1) with (S j) by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. cbn [rep app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?app_nil_r. rewrite ?lift_app_blank. reflexivity.
Qed.

(** The boot lands on the level-j count's anchor, up to @BPAD@/@BFAR@
    trailing blanks -- the [lift] leniency [NestedLapLift] measured to be the
    binding one on this whole bucket. *)
Lemma gbo_@ID@ : forall j, lift (cden [] [] j BB1_@ID@) = lift (Dc j 0).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_@ID@ = (@STI@, (@BLEFT@, S0, @BFARE@))).
  { unfold cden, BB1_@ID@, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
@IXBO@    rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
    cbn [app]. rewrite ?app_nil_r. reflexivity. }
  assert (HC : Dc j 0 = (@STI@, (@BWANT@, S0, @BFARW@))).
  { unfold Dc_@ID@, Cin_@ID@, TB_@ID@, Uc_@ID@. rewrite epow2_@ID@.
    replace (0 + @D0@) with @D0@ by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  rewrite HD, HC. rewrite ?lbl_@ID@. rewrite ?lift_app_blank. reflexivity.
Qed.

(** The closing sweep starts from the level-0 count, whose tail is by then
    [j] units longer than the top level's -- so unlike the per-level chains it
    is indexed by the OUTER index. *)
Lemma gcl_@ID@ : forall j, Dc 0 (j + 0) = cden [] [] j CL0_@ID@.
Proof.
  intro j.
  unfold Dc_@ID@, Cin_@ID@, TB_@ID@, Uc_@ID@, cden, CL0_@ID@, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
@IXCL@  rewrite ?rep_add. cbn [pow2 rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

(** ** The overflow branch

    [NestedLapCascade.cascade_overflow] with the level step above: boot in at
    level [j], [j] level steps down (exponentially many counts, none of them
    named), the sweep out.  The conclusion is verbatim the [LapStep]
    obligation, so this drops into a board wherever [lapo_] goes. *)
Lemma lapo_@ID@ : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j Ev.
  apply (cascade_overflow tm Cc Dc hstep_@ID@ p j 0).
  - exists (@CAB@ * j + @CBB@), (cden [] [] j BB1_@ID@).
    split; [lia|]. split; [| exact (gbo_@ID@ j)].
    rewrite (gso_@ID@ p j Ev).
    exact (srun_sound tm true true chb_@ID@ B0_@ID@ BB1_@ID@ @CAB@ @CBB@
             run_boot_@ID@ [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  - exists (@CACL@ * j + @CBCL@).
    rewrite gcl_@ID@, <- (geo_@ID@ p j Ev), <- gcx_@ID@.
    apply csteps_lift.
    exact (srun_sound tm true true chCL_@ID@ CL0_@ID@ CL1_@ID@ @CACL@ @CBCL@
             run_close_@ID@ [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.
'''

PROTO = PROTO_DOC + PROTO_CORE

# ------------------------------------------------- the octave-down variant ---
#
# Wave-24's 12 "main count at 2^(j-1)..2^j-1" non-gated rows: the WHOLE
# cascade sits one octave down.  At outer index S j' the boot lands on the
# top level's FIRST count A(j'), one A->B hop enters the standard descent,
# and after level 0 the machine runs ONE MORE ASCENDING COUNT at octave
# j+1 (the same inner family, constant tail) before the successor -- so the
# close is two affine chains around a [fill_hop], and the p = 1 overflow
# (outer index 0) has no cascade at all: a concrete lap, the offset route's
# exact j = 0 device.  No new library Coq: [fill_hop] and [cascade_vis]
# already carry everything.

# The closing count need not start AT the octave.  On part of this bucket the
# chain into it lands on its SECOND value, 2^(j+1)+1 = [xI (pow2 j)], and the
# emitter's whole answer to that is this lemma pair: the entered value's own
# word, and its fill's.  [fill_hop] needs nothing -- it is arbitrary-[v0]
# already -- and the way OUT is untouched, because both values share a fill.
EXI_SEC = r'''(** The closing count ENTERS ONE VALUE IN, at [xI (pow2 n)] = 2^(n+1)+1
    rather than at [pow2 (S n)]: its word is the octave's with the odd digit
    peeled off the front and one fewer unit copy behind it.  Its FILL is the
    same all-ones value, so only the way IN moves. *)
Lemma exi_@ID@ : forall n,
  @ENCI@ (xI (pow2 n)) = @USI@ ++ rep @UDI@ n ++ @SODI@.
Proof. intro n. rewrite <- epow2_@ID@. reflexivity. Qed.

Lemma exif_@ID@ : forall n,
  @ENCI@ (fill (xI (pow2 n))) = rep @USI@ (S n) ++ @SOSI@.
Proof. intro n. exact (efill_@ID@ (S n)). Qed.

'''

LOW_CLOSE = r'''(** *** the close, octave-down: after level 0 the machine runs ONE MORE
    ASCENDING COUNT at octave j+1 -- the same inner family over the constant
    tail [BT], its exponentially many laps living in [fill_hop] -- framed by
    two affine chains. *)
@EXISEC@Definition BT_@ID@ : list Sym := @BIGTAIL@.
Local Notation BT := BT_@ID@.

Definition CLA0_@ID@ : sconf := @CLA0@.
Definition CLA1_@ID@ : sconf := @CLA1@.
Definition chCLA_@ID@ : list lstep := @CHCLA@.

Lemma run_closeA_@ID@ :
  srun tm true true chCLA_@ID@ CLA0_@ID@ = Some (CLA1_@ID@, @CACA@, @CBCA@).
Proof. vm_compute. reflexivity. Qed.

Definition CLB0_@ID@ : sconf := @CLB0@.
Definition CLB1_@ID@ : sconf := @CLB1@.
Definition chCLB_@ID@ : list lstep := @CHCLB@.

Lemma run_closeB_@ID@ :
  srun tm true true chCLB_@ID@ CLB0_@ID@ = Some (CLB1_@ID@, @CACB@, @CBCB@).
Proof. vm_compute. reflexivity. Qed.

'''

LOW_GBO = r'''(** The boot chain lands on the TOP level's FIRST count -- A at one level
    BELOW the outer index, tail one unit past the top's -- up to @BPAD@/@BFAR@
    trailing blanks. *)
Lemma gboa_@ID@ : forall j, lift (cden [] [] j BB1_@ID@) = lift (Cin (TA 1) (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_@ID@ = (@STI@, (@BLEFT@, S0, @BFARE@))).
  { unfold cden, BB1_@ID@, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
@IXBO@    rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
    cbn [app]. rewrite ?app_nil_r. reflexivity. }
  assert (HC : Cin (TA 1) (pow2 j) = (@STI@, (@BWANT@, S0, @BFARW@))).
  { unfold Cin_@ID@, TA_@ID@, Uc_@ID@. rewrite epow2_@ID@.
    replace (1 + @D0@) with @D0P1@ by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  rewrite HD, HC. rewrite ?lbl_@ID@. rewrite ?lift_app_blank. reflexivity.
Qed.

'''

LOW_GCL = r'''(** The level-0 count's tail is [j + 1] units past the top's; the closing
    count starts at [@BIGV@] over [BT]. *)
Lemma gcla_@ID@ : forall j, Dc 0 (j + 1) = cden [] [] (S j) CLA0_@ID@.
Proof.
  intro j.
  unfold Dc_@ID@, Cin_@ID@, TB_@ID@, Uc_@ID@, cden, CLA0_@ID@, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite (epow2_@ID@ 0).
@IXCLA@  rewrite ?rep_add. cbn [pow2 rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma gclab_@ID@ : forall j,
  lift (cden [] [] (S j) CLA1_@ID@) = lift (Cin BT (@BIGV@)).
Proof.
  intro j.
  assert (HD : cden [] [] (S j) CLA1_@ID@ = (@STI@, (@CLABL@, S0, @CLABF@))).
  { unfold cden, CLA1_@ID@, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
@IXCLAB@    rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
    cbn [app]. rewrite ?app_nil_r. reflexivity. }
  assert (HC : Cin BT (@BIGV@) = (@STI@, (@CLABW@, S0, @CLABG@))).
  { unfold Cin_@ID@, BT_@ID@. rewrite @BIGVE@.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  rewrite HD, HC. rewrite ?lbl_@ID@. rewrite ?lift_app_blank. reflexivity.
Qed.

Lemma gclb_@ID@ : forall j,
  Cin BT (fill (@BIGV@)) = cden [] [] (S (S j)) CLB0_@ID@.
Proof.
  intro j.
  unfold Cin_@ID@, BT_@ID@, cden, CLB0_@ID@, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite @BIGVF@.
@IXCLB@  rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

(** The closing count lands one index up from [geo_]'s [B1] frame; both
    normalise to the same explicit successor word. *)
Lemma gclbx_@ID@ : forall j,
  lift (cden [] [] (S (S j)) CLB1_@ID@) = lift (cden [] [] (S j) B1_@ID@).
Proof.
  intro j.
  assert (HD : cden [] [] (S (S j)) CLB1_@ID@ = (@ST0@, (@CBXL@, S0, @CBXF@))).
  { unfold cden, CLB1_@ID@, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
@IXCBX@    rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
    cbn [app]. rewrite ?app_nil_r. reflexivity. }
  assert (HE : cden [] [] (S j) B1_@ID@ = (@ST0@, (@CBXB@, S0, @CBXG@))).
  { unfold cden, B1_@ID@, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
@IXCBE@    rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
    cbn [app]. rewrite ?app_nil_r. reflexivity. }
  rewrite HD, HE. rewrite ?lbl_@ID@. rewrite ?lift_app_blank. reflexivity.
Qed.

'''

LOW_LAPO = r'''(** ** The overflow branch, reindexed

    The top level sits ONE OCTAVE DOWN, so the generic route runs at
    [j = S j']: boot to A(j'), one A->B hop ([fill_hop] hides that count),
    [j'] level steps down, the closing count, out.  [j = 0] is a concrete
    lap -- the p = 1 overflow has no cascade at all. *)

Lemma gbor_@ID@ : forall p j, cview p = (S (S j), None) ->
  exists n c, 0 < n /\ csteps tm n (Cc p) = Some c /\ lift c = lift (Dc j 1).
Proof.
  intros p j Ev.
  assert (HAB : exists n, stepn tm n (lift (Cin (TA 1) (fill (pow2 j))))
                = Some (lift (Dc j 1))).
  { exists (@CAAB@ * j + @CBAB@). unfold Dc_@ID@.
    rewrite (gABs_@ID@ j 0), <- (gABd_@ID@ j 0).
    apply csteps_lift.
    exact (srun_sound tm @ELAB@ true chAB_@ID@ AB0_@ID@ AB1_@ID@ @CAAB@ @CBAB@
             run_AB_@ID@ (XAB_@ID@ 0) [] j
             ltac:(@ELABT@) ltac:(reflexivity)). }
  destruct (fill_hop tm Cin lapin_@ID@ (TA 1) (pow2 j) _ HAB) as (n2 & H2).
  rewrite <- (gboa_@ID@ j) in H2.
  destruct (stepn_csteps_at tm n2 (cden [] [] j BB1_@ID@) _ H2)
    as (cc & Hcc & Hl).
  exists (@CAB@ * j + @CBB@ + n2), cc.
  split; [lia|]. split; [| exact Hl].
  rewrite csteps_add, (gso_@ID@ p j Ev).
  rewrite (srun_sound tm true true chb_@ID@ B0_@ID@ BB1_@ID@ @CAB@ @CBB@
             run_boot_@ID@ [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  exact Hcc.
Qed.

(** j = 0: the p = 1 overflow, concrete. *)
Lemma lapz_@ID@ : exists n c', csteps tm n (Cc 1) = Some c'
  /\ lift c' = lift (Cc 2) /\ 0 < n.
Proof.
  exists @N0@.
  assert (H : match csteps tm @N0@ (Cc 1) with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm @N0@ (Cc 1)) as [c|] eqn:E0; [|discriminate].
  exists c. split; [reflexivity|]. split; [apply ceqb_lift; exact H | lia].
Qed.

Lemma lapo_@ID@ : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j Ev.
  destruct j as [|j'].
  - rewrite (cview_none_shape p 0 Ev). exact lapz_@ID@.
  - apply (cascade_overflow tm Cc Dc hstep_@ID@ p j' 1).
    + exact (gbor_@ID@ p j' Ev).
    + assert (HB : exists n,
        stepn tm n (lift (Cin BT (fill (@BIGVP@))))
        = Some (lift (Cc (Pos.succ p)))).
      { exists (@CACB@ * S (S j') + @CBCB@).
        rewrite (gclb_@ID@ j'), <- (geo_@ID@ p (S j') Ev), <- (gclbx_@ID@ j').
        apply csteps_lift.
        exact (srun_sound tm true true chCLB_@ID@ CLB0_@ID@ CLB1_@ID@
                 @CACB@ @CBCB@ run_closeB_@ID@ [] [] (S (S j'))
                 ltac:(reflexivity) ltac:(reflexivity)). }
      destruct (fill_hop tm Cin lapin_@ID@ BT (@BIGVP@) _ HB)
        as (n2 & H2).
      exists (@CACA@ * S j' + @CBCA@ + n2).
      rewrite (gcla_@ID@ j'), stepn_add.
      rewrite (csteps_lift _ _ _ _
        (srun_sound tm true true chCLA_@ID@ CLA0_@ID@ CLA1_@ID@ @CACA@ @CBCA@
           run_closeA_@ID@ [] [] (S j')
           ltac:(reflexivity) ltac:(reflexivity))).
      rewrite (gclab_@ID@ j'). exact H2.
Qed.
'''


def _low_core():
    """PROTO_CORE with the gated close/gbo/gcl/lapo sections swapped for the
    octave-down ones and [gso_] restated at the reindexed anchor.  Assembled
    by section markers so the gated text stays single-sourced."""
    c = PROTO_CORE
    i_close = c.index('(** *** the closing sweep')
    i_glue = c.index('(** ** The per-level glue')
    i_gbo = c.index('(** The boot lands on the level-j')
    i_gcl = c.index('(** The closing sweep starts from')
    i_lapo = c.index('(** ** The overflow branch')
    mid2 = c[i_glue:i_gbo]
    old_gso = ('Lemma gso_@ID@ : forall p j, cview p = (S j, None) ->'
               ' Cc p = cden [] [] j B0_@ID@.')
    new_gso = ('Lemma gso_@ID@ : forall p j, cview p = (S (S j), None) ->\n'
               '  Cc p = cden [] [] j B0_@ID@.')
    if old_gso not in mid2:
        raise RuntimeError('low core: gso statement not found')
    mid2 = mid2.replace(old_gso, new_gso)
    old_none = 'destruct (@ENCMOD@.@NONE@ p j Ev) as (H1 & _).'
    if old_none not in mid2:
        raise RuntimeError('low core: gso NONE destruct not found')
    mid2 = mid2.replace(old_none,
                        'destruct (@ENCMOD@.@NONE@ p (S j) Ev) as (H1 & _).')
    return (c[:i_close] + LOW_CLOSE + mid2 + LOW_GBO + LOW_GCL + LOW_LAPO)

# ----------------------------------------------------------------- the board ---
#
# Everything a BOARD adds around the overflow branch: the interior lap at the
# outer anchor (emit_lapcert's own templates, verbatim), the full lap, the
# bootstrap, the visits and the closer.  The whole board runs in [lift] space
# -- the cascade's overflow closes only up to [lift], so the closer is
# [LapCertGlueLift.glue_neverqh_lift] on every one of these.

BOARD_TAIL = r'''
(** ** The INTERIOR branch, at the outer anchor *)

@INTERIOR@

@GLUEI@

@LAPIL@(** ** The lap *)

Lemma lap_@ID@ : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
@LAPICASE@
  - destruct (cview_pos p j E) as (j' & ->).
    exact (lapo_@ID@ p j' E).
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

    Only the boot and the closing sweep fire at EVERY outer index -- at
    j = 0 the cascade has no descent, so a witness inside a per-level chain
    would not be universal.  A state missing from the boot chain is found in
    the SWEEP, reached through the whole cascade ([cascade_vis]: boot to
    level j, [cascade_down] to level 0, then a prefix of the sweep). *)

Lemma viso_@ID@ : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_@ID@ = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_@ID@ p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_@ID@ p j E)].
Qed.

Lemma visc_@ID@ : forall (l : list lstep) (q : St),
  srun_st tm true true l CL0_@ID@ = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros l q Hst p j Ev.
  apply (cascade_vis tm Cc Dc hstep_@ID@ q p j 0).
  - exists (@CAB@ * j + @CBB@), (cden [] [] j BB1_@ID@).
    split; [| exact (gbo_@ID@ j)].
    rewrite (gso_@ID@ p j Ev).
    exact (srun_sound tm true true chb_@ID@ B0_@ID@ BB1_@ID@ @CAB@ @CBB@
             run_boot_@ID@ [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  - rewrite gcl_@ID@.
    destruct (vis_of_run tm (fun _ => cden [] [] j CL0_@ID@) true true l
                CL0_@ID@ 1%positive j [] [] q Hst
                ltac:(reflexivity) ltac:(reflexivity) eq_refl)
      as (k & c & Hk & Hq).
    exists k, (lift c).
    split; [apply csteps_lift; exact Hk | rewrite lift_state; exact Hq].
Qed.

Lemma vis_@ID@ : forall p q,
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros p q.
  destruct q.
@VISITS@
Qed.

@FINAL@
'''

VIS_BOOT = '''  - (* %s *)
    apply (vis_via_ovf_lift tm Cc lapil_@ID@ %s).
    intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
    apply (viso_@ID@ %s %s ltac:(vm_compute; reflexivity)
                 p1 j1 E1).'''

# the octave-down bullet: the reindexed [viso_] covers j1 = S j1'; the p = 1
# anchor gets its concrete [visz_] witness (the offset route's device)
VIS_BOOT_LOW = '''  - (* %s *)
    apply (vis_via_ovf_lift tm Cc lapil_@ID@ %s).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      apply (vis_lift_of_csteps tm Cc). exact visz_%s_@ID@.
    + apply (vis_lift_of_csteps tm Cc).
      apply (viso_@ID@ %s %s ltac:(vm_compute; reflexivity)
                   p1 j1' E1).'''

VISZ_LOW = r'''(** State @STQ@'s visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_@STQ@_@ID@ : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = @STQ@.
Proof. exists @KQ@. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.'''

BOARD_TAIL_LOW = r'''
(** ** The INTERIOR branch, at the outer anchor *)

@INTERIOR@

@GLUEI@

@LAPIL@(** ** The lap *)

Lemma lap_@ID@ : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
@LAPICASE@
  - destruct (cview_pos p j E) as (j' & ->).
    exact (lapo_@ID@ p j' E).
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

    Every state fires inside the BOOT chain, which runs at the REINDEXED
    anchor -- so the generic witness covers j = S j', and the p = 1 anchor
    (whose overflow has no cascade) gets concrete [visz_] witnesses. *)

Lemma viso_@ID@ : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_@ID@ = Some q ->
  forall p j, cview p = (S (S j), None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_@ID@ p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_@ID@ p j E)].
Qed.

@VISZSEC@

Lemma vis_@ID@ : forall p q,
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros p q.
  destruct q.
@VISITS@
Qed.

@FINAL@
'''

VIS_CLOSE = '''  - (* %s: fires only in the closing sweep *)
    apply (vis_via_ovf_lift tm Cc lapil_@ID@ %s).
    intros p1 j1 E1.
    apply (visc_@ID@ %s %s ltac:(vm_compute; reflexivity)
                 p1 j1 E1).'''

LAPIL_EXACT = r'''(** The interior closes exactly; the cascade's plumbing runs in [lift]
    space, so restate it there. *)
Lemma lapil_@ID@ : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (lapi_@ID@ p j q0 E) as (n & Hn & Hr).
  exists n, (Cc (Pos.succ p)). auto.
Qed.

'''

LAPIL_LIFT = r'''(** [lapi_@ID@] is already in [lift] space; alias it for the plumbing. *)
Lemma lapil_@ID@ : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof. exact lapi_@ID@. Qed.

'''

LAPICASE_EXACT = '''  - destruct (lapi_@ID@ p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].'''

LAPICASE_LIFT = '''  - destruct (lapi_@ID@ p j q0 E) as (n & c' & Hn & Hrun & Hlift).
    exists n, c'. split; [exact Hrun | split; [exact Hlift | exact Hn]].'''


def _sconf(c):
    return E.cconf(c)


def reps(spec, d, K):
    """Every hole of [PROTO], from one gated [cascade_endpoints] record."""
    A = d['anchor']
    law = d['law']
    ID = E.mach_id(spec)
    din = E.ENCDATA[law['inner']]
    dout = E.ENCDATA[A['enc']]
    T = d['trans']
    ba, ab, cl = T['BA'], T['AB'], T['CLOSE']
    d0 = law['M'] - law['j']
    unit = law['unit']

    def side_b(t, which):
        return str(t[which][1][3])

    # the boot's landing, with its trailing blanks kept EXPLICIT so [lbl_]
    # can strip them: fusing them into a literal list first would leave no
    # `_ ++ [S0]` for the rewrite to see.
    bwant = (tuple(din['soD']) + tuple(law['extraB'])
             + tuple(unit) * (law['M'] - law['j']))
    bcore, bpad, bpadw = _pads(d['BB1'][1][4], bwant)
    bfcore, bfar, bfarw = _pads(tuple(d['BB1'][3][0]) + tuple(d['BB1'][3][4]),
                                tuple(law['far_in']))
    # the closing sweep's landing, same treatment: it stops on the outer
    # successor's anchor up to trailing blanks, and the syntactic bridge back
    # to [B1] is what [geo_] then consumes.
    ovwant = tuple(dout['soD']) + tuple(A['tail'])
    lpre, lu, la, lb, lpost = cl['land'][1]
    if (tuple(lpre), tuple(lu), la, lb) != ((), tuple(dout['uD']), 1, 1):
        raise NC.NestError('cascade CLOSE lands off the successor shape %r'
                           % (cl['land'][1],))
    ccore, cpad, cpadb = _pads(lpost, ovwant)
    cfcore, cfarp, cfarb = _pads(tuple(cl['land'][3][0])
                                 + tuple(cl['land'][3][4]), tuple(A['far']))
    crep = 'rep %s (j + 1)' % clist(dout['uD'])
    cleft = _nest(ccore, cpad, crep)
    clbase = _nest(ccore, cpadb, crep)
    cfare = _nest(cfcore, cfarp)
    cfarb = _nest(cfcore, cfarb)
    brep = 'rep %s j' % clist(din['uD'])
    bleft = _nest(bcore, bpad, brep)
    bwantc = _nest(bcore, bpadw, brep)
    bfare = _nest(bfcore, bfar)
    bfarw = _nest(bfcore, bfarw)

    r = {
        '@ID@': ID, '@SPEC@': spec,
        '@DSPEC@': E.mirror_spec(spec) if A['mirrored'] else spec,
        '@TABLE@': coq_table(E.mirror_spec(spec) if A['mirrored'] else spec),
        '@ST0@': ST[A['st0']], '@ENC@': dout.get('fn', A['enc']),
        '@TAIL@': clist(A['tail']), '@FAR@': clist(A['far']),
        '@STI@': ST[law['st_in']], '@ENCI@': din.get('fn', law['inner']),
        '@FARI@': clist(law['far_in']),
        '@UDI@': clist(din['uD']), '@USI@': clist(din['uS']),
        '@SODI@': clist(din['soD']), '@SOSI@': clist(din['soS']),
        '@ENCMODI@': din['mod'], '@SOMEI@': din['some'],
        '@NONEI@': din['none'],
        '@ENCMOD@': dout['mod'], '@NONE@': dout['none'],
        '@UNIT@': clist(unit), '@D0@': str(d0),
        '@HEADA@': clist(law['extraA']), '@HEADB@': clist(law['extraB']),
        '@AI0@': _sconf(d['AI0']), '@AI1@': _sconf(d['AI1']),
        '@CHN@': E.cchain(d['chn']),
        '@CAN@': str(d['cn'][0]), '@CBN@': str(d['cn'][1]),
        '@B0@': _sconf(d['B0']), '@B1@': _sconf(d['B1']),
        '@BB1@': _sconf(d['BB1']), '@CHB@': E.cchain(d['chb']),
        '@CAB@': str(d['cb'][0]), '@CBB@': str(d['cb'][1]),
        '@BA0@': _sconf(ba['src']), '@BA1@': _sconf(ba['land']),
        '@CHBA@': E.cchain(ba['chain']),
        '@CABA@': str(ba['cost'][0]), '@CBBA@': str(ba['cost'][1]),
        '@AB0@': _sconf(ab['src']), '@AB1@': _sconf(ab['land']),
        '@CHAB@': E.cchain(ab['chain']),
        '@CAAB@': str(ab['cost'][0]), '@CBAB@': str(ab['cost'][1]),
        '@CL0@': _sconf(cl['src']), '@CL1@': _sconf(cl['land']),
        '@CHCL@': E.cchain(cl['chain']),
        '@CLEFT@': cleft, '@CFARE@': cfare, '@CLBASE@': clbase,
        '@CFARB@': cfarb,
        '@CPAD@': str(cpad), '@CFARP@': str(cfarp),
        '@CACL@': str(cl['cost'][0]), '@CBCL@': str(cl['cost'][1]),
        '@ELBA@': 'true' if ba['el'] else 'false',
        '@ELAB@': 'true' if ab['el'] else 'false',
        '@ELBAT@': 'reflexivity' if ba['el'] else 'discriminate',
        '@ELABT@': 'reflexivity' if ab['el'] else 'discriminate',
        '@BBA0@': side_b(ba, 'src'), '@BBA1@': str(ba['land'][1][3]),
        '@BAB0@': side_b(ab, 'src'), '@BAB1@': str(ab['land'][1][3]),
        '@BBB1@': str(d['BB1'][1][3]), '@BCL0@': side_b(cl, 'src'),
        '@OBSP@': ('1' if dout['obS'] >= 1 else '0'),
        '@CNTP@': ('(S j)' if dout['obS'] >= 1 else 'j'),
        '@BPAD@': str(bpad), '@BFAR@': str(bfar),
        '@BLEFT@': bleft, '@BFARE@': bfare, '@BWANT@': bwantc,
        '@BFARW@': bfarw,
        '@NLEV@': 'j+1', '@NVAL@': d['nval'],
        '@EXTRAMOD@': ('' if din['mod'] == dout['mod']
                       else ' ' + din['mod']),
    }
    # the opaque regions, as functions of the level's tail length
    r['@XBA@'] = _xterm(ba, law, 'BA')
    r['@XAB@'] = _xterm(ab, law, 'AB')
    # the index arithmetic each glue lemma needs.  Every one of these is a
    # [lia] identity; what they do is put the growing rep's extra units where
    # the OTHER side of the equation has them -- at the front when the tail
    # head sits before them, at the back when it does not.
    def cnt(v, b):
        return ('  replace (1 * %s + %d) with %s by lia.\n'
                % (v, b, v if b == 0 else '(%s + %d)' % (v, b)))

    def far(v):
        return '  replace (0 * %s + 0) with 0 by lia.\n' % v

    def front(term, k):
        return '  replace (%s) with (%d + m) by lia.\n' % (term, k)

    bb = lambda t, w: t[w][1][3] if w != 'land' else t['land'][1][3]
    r['@IXBAS@'] = (cnt('l', ba['src'][1][3]) + far('l')
                    + '  replace (S l) with (l + 1) by lia.\n'
                    + front('m + %d' % d0, d0))
    r['@IXBAD@'] = (cnt('l', ba['land'][1][3]) + far('l')
                    + front('S m + %d' % d0, d0 + 1))
    r['@IXABS@'] = (cnt('l', ab['src'][1][3]) + far('l')
                    + front('S m + %d' % d0, d0 + 1))
    r['@IXABD@'] = (cnt('l', ab['land'][1][3]) + far('l')
                    + front('S m + %d' % d0, d0 + 1))
    r['@IXBO@'] = ('  ' + cnt('j', d['BB1'][1][3]).strip() + '\n'
                   + '  ' + far('j').strip() + '\n')
    r['@FARN@'] = _farchg(d['ifar'], law['far_in'])
    r['@FARBA@'] = _farchg(NC._slack(tuple(ba['land'][3][0])
                                     + tuple(ba['land'][3][4]),
                                     tuple(law['far_in']), 'BA far'),
                           law['far_in'])
    r['@FARAB@'] = _farchg(NC._slack(tuple(ab['land'][3][0])
                                     + tuple(ab['land'][3][4]),
                                     tuple(law['far_in']), 'AB far'),
                           law['far_in'])
    r['@IXCL@'] = ('  rewrite (epow2_%s 0).\n' % ID
                   + cnt('j', cl['src'][1][3]) + far('j')
                   + '  replace (j + 0 + %d) with (j + %d) by lia.\n'
                   % (d0, d0))
    return r


def reps_low(spec, d, K):
    """[reps]'s octave-down twin: the shared holes, the reindexed boot's
    landing bridge (to the TOP level's FIRST count), and the two-chain close
    around the octave-(j+1) count.  Shapes the framing search cannot express
    in this template raise rather than mis-render."""
    A = d['anchor']
    law = d['law']
    ID = E.mach_id(spec)
    din = E.ENCDATA[law['inner']]
    dout = E.ENCDATA[A['enc']]
    T = d['trans']
    ba, ab = T['BA'], T['AB']
    ca, cb = T['CLOSEA'], T['CLOSEB']
    d0 = law['M'] - law['j']
    unit = law['unit']
    bt = tuple(law['big_tail'])
    soD, soS = tuple(din['soD']), tuple(din['soS'])

    if dout['obS'] != 0:
        raise NC.NestError('cascade low: only obS=0 outer alphabets wired')
    for t, nm in ((ca, 'CLOSEA'), (cb, 'CLOSEB')):
        if not t['el']:
            raise NC.NestError('cascade low: %s is not el' % nm)

    # the boot lands on A(top): soD ++ extraA ++ unit^(dm+1)
    bwant = soD + tuple(law['extraA']) + tuple(unit) * (d0 + 1)
    bcore, bpad, bpadw = _pads(d['BB1'][1][4], bwant)
    bfcore, bfar, bfarw = _pads(tuple(d['BB1'][3][0]) + tuple(d['BB1'][3][4]),
                                tuple(law['far_in']))
    brep = 'rep %s j' % clist(din['uD'])

    # CLOSEA: level-0 fill -> the closing count's start
    apre, au, aa, ab_, apost = ca['src'][1]
    if (tuple(apre), tuple(au), aa, ab_, tuple(apost)) != \
            (soD + tuple(law['extraB']), tuple(unit), 1, d0, ()):
        raise NC.NestError('cascade low: CLOSEA src off shape %r'
                           % (ca['src'][1],))
    # [big_in] = 1: the count is entered one value in, at [xI (pow2 (S j))],
    # so the landing carries the odd digit in its PREFIX and one fewer unit
    # copy behind it.  Its fill is the octave's, so CLOSEB is untouched.
    bi = law.get('big_in', 0)
    uSi = tuple(din['uS'])
    lpre, lu, la, lb, lpost = ca['land'][1]
    if (tuple(lpre), tuple(lu), la, lb) != \
            (((), tuple(din['uD']), 1, 1) if not bi
             else (uSi, tuple(din['uD']), 1, 0)):
        raise NC.NestError('cascade low: CLOSEA lands off shape %r'
                           % (ca['land'][1],))
    acore, apadl, apadw = _pads(lpost, soD + bt)
    afcore, afarl, afarw = _pads(tuple(ca['land'][3][0])
                                 + tuple(ca['land'][3][4]),
                                 tuple(law['far_in']))
    arep = ('rep %s (S (S j))' % clist(din['uD']) if not bi
            else '%s ++ rep %s (S j)' % (clist(uSi), clist(din['uD'])))

    # CLOSEB: the closing count's fill -> the outer successor
    zpre, zu, za, zb, zpost = cb['src'][1]
    if (tuple(zpre), tuple(zu), za, zb, tuple(zpost)) != \
            ((), tuple(din['uS']), 1, 0, soS + bt):
        raise NC.NestError('cascade low: CLOSEB src off shape %r'
                           % (cb['src'][1],))
    xpre, xu, xa, xb, xpost = cb['land'][1]
    if (tuple(xpre), tuple(xu), xa, xb) != ((), tuple(dout['uD']), 1, 0):
        raise NC.NestError('cascade low: CLOSEB lands off shape %r'
                           % (cb['land'][1],))
    ovwant = tuple(dout['soD']) + tuple(A['tail'])
    xcore, xpadl, xpadb = _pads(xpost, ovwant)
    xfcore, xfarl, xfarb = _pads(tuple(cb['land'][3][0])
                                 + tuple(cb['land'][3][4]), tuple(A['far']))
    xrep = 'rep %s (S (S j))' % clist(dout['uD'])

    def cnt(v, b):
        return ('  replace (1 * %s + %d) with %s by lia.\n'
                % (v, b, v if b == 0 else '(%s + %d)' % (v, b)))

    def far(v):
        return '  replace (0 * %s + 0) with 0 by lia.\n' % v

    r = {
        '@ID@': ID, '@SPEC@': spec,
        '@DSPEC@': E.mirror_spec(spec) if A['mirrored'] else spec,
        '@TABLE@': coq_table(E.mirror_spec(spec) if A['mirrored'] else spec),
        '@ST0@': ST[A['st0']], '@ENC@': dout.get('fn', A['enc']),
        '@TAIL@': clist(A['tail']), '@FAR@': clist(A['far']),
        '@STI@': ST[law['st_in']], '@ENCI@': din.get('fn', law['inner']),
        '@FARI@': clist(law['far_in']),
        '@UDI@': clist(din['uD']), '@USI@': clist(din['uS']),
        '@SODI@': clist(din['soD']), '@SOSI@': clist(din['soS']),
        '@ENCMODI@': din['mod'], '@SOMEI@': din['some'],
        '@NONEI@': din['none'],
        '@ENCMOD@': dout['mod'], '@NONE@': dout['none'],
        '@UNIT@': clist(unit), '@D0@': str(d0), '@D0P1@': str(d0 + 1),
        '@HEADA@': clist(law['extraA']), '@HEADB@': clist(law['extraB']),
        '@AI0@': _sconf(d['AI0']), '@AI1@': _sconf(d['AI1']),
        '@CHN@': E.cchain(d['chn']),
        '@CAN@': str(d['cn'][0]), '@CBN@': str(d['cn'][1]),
        '@B0@': _sconf(d['B0']), '@B1@': _sconf(d['B1']),
        '@BB1@': _sconf(d['BB1']), '@CHB@': E.cchain(d['chb']),
        '@CAB@': str(d['cb'][0]), '@CBB@': str(d['cb'][1]),
        '@BA0@': _sconf(ba['src']), '@BA1@': _sconf(ba['land']),
        '@CHBA@': E.cchain(ba['chain']),
        '@CABA@': str(ba['cost'][0]), '@CBBA@': str(ba['cost'][1]),
        '@AB0@': _sconf(ab['src']), '@AB1@': _sconf(ab['land']),
        '@CHAB@': E.cchain(ab['chain']),
        '@CAAB@': str(ab['cost'][0]), '@CBAB@': str(ab['cost'][1]),
        '@ELBA@': 'true' if ba['el'] else 'false',
        '@ELAB@': 'true' if ab['el'] else 'false',
        '@ELBAT@': 'reflexivity' if ba['el'] else 'discriminate',
        '@ELABT@': 'reflexivity' if ab['el'] else 'discriminate',
        '@OBSP@': '0', '@CNTP@': 'j',
        '@BPAD@': str(bpad), '@BFAR@': str(bfar),
        '@BLEFT@': _nest(bcore, bpad, brep),
        '@BFARE@': _nest(bfcore, bfar),
        '@BWANT@': _nest(bcore, bpadw, brep),
        '@BFARW@': _nest(bfcore, bfarw),
        '@NLEV@': 'j', '@NVAL@': d['nval'],
        '@EXTRAMOD@': ('' if din['mod'] == dout['mod']
                       else ' ' + din['mod']),
        '@BIGTAIL@': clist(bt),
        '@CLA0@': _sconf(ca['src']), '@CLA1@': _sconf(ca['land']),
        '@CHCLA@': E.cchain(ca['chain']),
        '@CACA@': str(ca['cost'][0]), '@CBCA@': str(ca['cost'][1]),
        '@CLB0@': _sconf(cb['src']), '@CLB1@': _sconf(cb['land']),
        '@CHCLB@': E.cchain(cb['chain']),
        '@CACB@': str(cb['cost'][0]), '@CBCB@': str(cb['cost'][1]),
        '@CLABL@': _nest(acore, apadl, arep),
        '@CLABW@': _nest(acore, apadw, arep),
        '@CLABF@': _nest(afcore, afarl), '@CLABG@': _nest(afcore, afarw),
        '@CBXL@': _nest(xcore, xpadl, xrep),
        '@CBXB@': _nest(xcore, xpadb, xrep),
        '@CBXF@': _nest(xfcore, xfarl), '@CBXG@': _nest(xfcore, xfarb),
        '@N0@': str(d['n0']),
        '@BIGV@': 'pow2 (S (S j))' if not bi else 'xI (pow2 (S j))',
        '@BIGVP@': "pow2 (S (S j'))" if not bi else "xI (pow2 (S j'))",
        '@BIGVE@': 'epow2_%s' % ID if not bi else 'exi_%s' % ID,
        '@BIGVF@': 'efill_%s' % ID if not bi else 'exif_%s' % ID,
        '@EXISEC@': '' if not bi else EXI_SEC,
    }
    r['@XBA@'] = _xterm(ba, law, 'BA')
    r['@XAB@'] = _xterm(ab, law, 'AB')

    def front(term, k):
        return '  replace (%s) with (%d + m) by lia.\n' % (term, k)

    r['@IXBAS@'] = (cnt('l', ba['src'][1][3]) + far('l')
                    + '  replace (S l) with (l + 1) by lia.\n'
                    + front('m + %d' % d0, d0))
    r['@IXBAD@'] = (cnt('l', ba['land'][1][3]) + far('l')
                    + front('S m + %d' % d0, d0 + 1))
    r['@IXABS@'] = (cnt('l', ab['src'][1][3]) + far('l')
                    + front('S m + %d' % d0, d0 + 1))
    r['@IXABD@'] = (cnt('l', ab['land'][1][3]) + far('l')
                    + front('S m + %d' % d0, d0 + 1))
    r['@IXBO@'] = ('  ' + cnt('j', d['BB1'][1][3]).strip() + '\n'
                   + '  ' + far('j').strip() + '\n')
    r['@FARN@'] = _farchg(d['ifar'], law['far_in'])
    r['@FARBA@'] = _farchg(NC._slack(tuple(ba['land'][3][0])
                                     + tuple(ba['land'][3][4]),
                                     tuple(law['far_in']), 'BA far'),
                           law['far_in'])
    r['@FARAB@'] = _farchg(NC._slack(tuple(ab['land'][3][0])
                                     + tuple(ab['land'][3][4]),
                                     tuple(law['far_in']), 'AB far'),
                           law['far_in'])
    # the close's index arithmetic: CLOSEA runs at S j (level-0 tail is
    # j+1 units past the top's), CLOSEB at S (S j) (the closing count)
    r['@IXCLA@'] = ('  replace (1 * S j + %d) with (j + 1 + %d) by lia.\n'
                    % (d0, d0)
                    + far('S j'))
    r['@IXCLAB@'] = ('    replace (1 * S j + %d) with (%s) by lia.\n'
                     % (1 - bi, 'S (S j)' if not bi else 'S j')
                     + '  ' + far('S j'))
    r['@IXCLB@'] = ('  replace (1 * S (S j) + 0) with (S (S j)) by lia.\n'
                    + far('S (S j)'))
    r['@IXCBX@'] = ('    replace (1 * S (S j) + 0) with (S (S j)) by lia.\n'
                    + '  ' + far('S (S j)'))
    r['@IXCBE@'] = ('    replace (1 * S j + 1) with (S (S j)) by lia.\n'
                    + '  ' + far('S j'))
    return r


def _pads(got, want):
    """The common core of a landing and the anchor it is meant to be, plus the
    trailing blanks each carries past it.

    A chain accepted up to [lift] can stop EITHER side of the anchor's
    syntactic form: past it, or one cell short when the anchor's own tail ends
    in a blank that [lift] cannot see.  Both happen on this bucket, so the
    bridge is stated over the core with a pad on each side rather than on the
    landing alone."""
    got, want = tuple(got), tuple(want)
    n = min(len(got), len(want))
    core = got[:n]
    if want[:n] != core or any(got[n:]) or any(want[n:]):
        raise NC.NestError('landing off shape: %r vs %r' % (got, want))
    return core, len(got) - n, len(want) - n


def _nest(core, npad, head=''):
    """[core] with [npad] trailing blanks, parenthesised so [lbl_] can see
    them: fusing them into a literal first leaves no `_ ++ [S0]` to rewrite."""
    body = (head + ' ++ ' if head else '') + clist(core)
    return '(' * npad + body + ''.join(') ++ [S0]' for _ in range(npad))


def _farchg(n, far_in):
    """A landing may stop [n] blanks past the anchor's FAR side.  [lift] cannot
    see them, but [lift_app_blank] rewrites `r ++ [S0]` and after the
    normalisation above the side is one fused literal, so re-split it first --
    the same [change] the flat nested glue uses for its inner-lap far pad."""
    if not n:
        return ''
    fused = clist(tuple(far_in) + (0,) * n)
    nest = ('(' * n + clist(tuple(far_in))
            + ''.join(') ++ [S0]' for _ in range(n)))
    return '  change (%s) with (%s).\n' % (fused, nest)


def _xterm(t, law, kind):
    """The chain's opaque region as a Coq term in [m].

    Read off the framing rather than assumed: [Xs] holds the region measured
    at each sampled level, and the law is that it grows by one unit per level
    down.  [m] is the emitter's tail index, which is [j - l] at the level a
    B->A step LEAVES and one less at the level an A->B step runs in."""
    W, j = law['unit'], law['j']
    n = sorted(t['Xs'])[0]
    X0 = t['Xs'][n]
    m0 = (j - n) if kind == 'BA' else (j - n - 1)
    k = len(X0) // len(W)
    head = X0[:len(X0) - k * len(W)]
    if X0[len(head):] != W * k:
        raise NC.NestError('cascade %s: the opaque region %r is not '
                           'head ++ rep unit k' % (kind, X0))
    off = k - m0
    if off < 0:
        raise NC.NestError('cascade %s: the opaque region shrinks with the '
                           'level (%d)' % (kind, off))
    body = 'rep Uc m' if off == 0 else 'rep Uc (%d + m)' % off
    return _cat([clist(head), body])


def proto(spec, K=7, out=None):
    d = CP.endpoints(spec, K, quiet=True)
    txt = _fill(PROTO, reps(spec, d, K))
    if out:
        with open(out, 'w') as f:
            f.write(txt)
    return txt


# ------------------------------------------------------------------ boards ---

BOARD_PREFIX = 'CASB'


def _far_slack_i(side, far):
    """The interior lap's landing FAR side vs the anchor's: the blanks it
    carries past it, rendered fused and re-split (emit_lapcert's far_slack)."""
    if side[1]:
        raise NC.NestError('interior far slack: unit run on the far side')
    got, wnt = tuple(side[0]) + tuple(side[4]), tuple(far)
    n = len(got) - len(wnt)
    if n < 1 or got != wnt + (0,) * n:
        raise NC.NestError('interior far slack %r vs %r' % (got, wnt))
    return (clist(got), '(' * n + clist(wnt)
            + ''.join(') ++ [S0]' for _ in range(n)))


def derive_board(spec, K=7):
    """Everything a FULL cascade board needs, gated: the wave-24 overflow
    record plus the interior chain at the outer anchor, the bootstrap and one
    visit witness per state.  Raises [NestError]/[DeriveError] naming the
    first piece that does not derive."""
    d = CP.endpoints(spec, K, quiet=True)
    A = d['anchor']
    oct_ = d['law'].get('oct', 0)
    tab, st0 = A['tab'], A['st0']
    tail, far, enc = A['tail'], A['far'], A['enc']
    encf = E.ENC[enc]
    dspec = E.mirror_spec(spec) if A['mirrored'] else spec
    p0 = None
    for (edge, tl, pp, en, fr) in E.anchors(dspec):
        if (E.LAB.index(edge), tuple(tl), en, tuple(fr)) == \
                (st0, tuple(tail), enc, tuple(far)):
            p0 = pp
            break
    if p0 is None:
        raise NC.NestError('anchor family lost its p0')

    A0, A1, _, _ = E.confs(enc, st0, tail, far)
    chi = E.LC.derive_chain(tab, False, True, A0, A1)
    islack = False
    if chi is None:
        chi = E.LC.derive_chain(tab, False, True, A0, A1, lift=True)
        if chi is None:
            raise NC.NestError('no interior chain')
        islack = True
    if islack and oct_ == -1:
        raise NC.NestError('cascade low: only exact interiors wired')
    ri = E.LC.srun(tab, False, True, chi, A0)
    if ri is None or ri[2] == 0:
        raise NC.NestError('interior lap of zero length at j=0')
    if islack:
        A1 = ri[0]
    cost = lambda j, c=(ri[1], ri[2]): c[0] * j + c[1]        # noqa: E731
    ok, ival = E.validate_int(tab, st0, encf, tail, far, cost)
    if not ok:
        raise NC.NestError('interior validation: ' + ival)

    boot = E.boot_probe(tab, st0, encf, tail, far, p0)
    if boot is None:
        raise NC.NestError('no bootstrap to p0=%d' % p0)

    # one witness per state: the boot chain covers most; the closing sweep is
    # the only other piece of the overflow available at EVERY outer index
    # (octave down: the boot chain alone, plus the concrete p = 1 witnesses).
    vis = {}
    for q in range(4):
        pre = E.LC.reach_state(tab, True, True, d['B0'], d['chb'], q)
        if pre is not None:
            vis[q] = ('boot', pre)
            continue
        if oct_ == 0:
            pre = E.LC.reach_state(tab, True, True,
                                   d['trans']['CLOSE']['src'],
                                   d['trans']['CLOSE']['chain'], q)
            if pre is not None:
                vis[q] = ('close', pre)
                continue
        raise NC.NestError('no visit witness for state %s' % E.LAB[q])
    if oct_ == -1 and sorted(d['visz']) != [0, 1, 2, 3]:
        raise NC.NestError('cascade low: p=1 visit witnesses incomplete')

    return dict(spec=spec, dspec=dspec, mirrored=A['mirrored'], d=d, K=K,
                oct=oct_, p0=p0, boot=boot, chi=chi, ci=(ri[1], ri[2]),
                A0=A0, A1=A1, islack=islack, vis=vis, ival=ival)


def render_board(D):
    """The full board source.  Rendered against the (possibly mirrored)
    derivation spec, like emit_lapcert; [mirrorize] then rewrites it into the
    transfer form for the real machine."""
    d, dspec = D['d'], D['dspec']
    low = D.get('oct', 0) == -1
    A2 = dict(d['anchor'], mirrored=False)
    r = (reps_low if low else reps)(dspec, dict(d, anchor=A2), D['K'])
    ID = r['@ID@']
    dout = E.ENCDATA[d['anchor']['enc']]
    r.update({
        '@SOME@': dout['some'],
        '@US@': clist(dout['uS']), '@UD@': clist(dout['uD']),
        '@A0@': E.cconf(D['A0']), '@A1@': E.cconf(D['A1']),
        '@CHI@': E.cchain(D['chi']),
        '@CAI@': str(D['ci'][0]), '@CBI@': str(D['ci'][1]),
        '@P0@': str(D['p0']), '@BOOT@': str(D['boot']),
        '@NI@': '%d*j+%d' % D['ci'],
        '@ICLO@': 'up to [lift]' if D['islack'] else 'exactly',
        '@IVAL@': D['ival'],
        '@INTERIOR@': E.INT_ONE,
        '@GLUEI@': E.GLUE_ONE_LIFT if D['islack'] else E.GLUE_ONE,
        '@LAPIL@': LAPIL_LIFT if D['islack'] else LAPIL_EXACT,
        '@LAPICASE@': LAPICASE_LIFT if D['islack'] else LAPICASE_EXACT,
        '@FINAL@': E.NQH_CLOSE_LIFT,
    })
    if D['islack']:
        farb, farnest = _far_slack_i(D['A1'][3], d['anchor']['far'])
        r['@FARB@'], r['@FARNEST@'] = farb, farnest
    vis = []
    for q in range(4):
        route, pre = D['vis'][q]
        if low:
            vis.append(VIS_BOOT_LOW % (ST[q], ST[q], ST[q],
                                       E.cchain(pre), ST[q]))
        else:
            tpl = VIS_BOOT if route == 'boot' else VIS_CLOSE
            vis.append(tpl % (ST[q], ST[q], E.cchain(pre), ST[q]))
    r['@VISITS@'] = '\n'.join(vis)
    if low:
        r['@VISZSEC@'] = '\n\n'.join(
            _fill(VISZ_LOW, {'@STQ@': ST[q], '@KQ@': str(d['visz'][q])})
            for q in range(4))
        src = BOARD_DOC_LOW + _low_core() + BOARD_TAIL_LOW
    else:
        src = BOARD_DOC + PROTO_CORE + BOARD_TAIL
    for _ in range(3):              # the injected blocks carry holes themselves
        for k, v in r.items():
            src = src.replace(k, v)
    if D['mirrored']:
        src = E.mirrorize(src, D['spec'], dspec)
    return src


def process_board(spec, do_emit=True, force=False, K=7):
    """emit_lapcert.process's shape, for the cascade route: derive, render,
    compile, report.  Returns the result dict, or ok=False with the reason."""
    try:
        D = derive_board(spec, K)
        src = render_board(D)
    except Exception as e:                                     # noqa: BLE001
        return dict(spec=spec, ok=False, why='cascade: %s' % e)
    if not do_emit:
        return dict(spec=spec, ok=True, enc=d_enc(D), ni='%d*j+%d' % D['ci'],
                    no='cascade')
    path = os.path.join(E.OUTDIR, '%s_%s.v'
                        % (BOARD_PREFIX, E.mach_id(spec)))
    if os.path.exists(path) and not force:
        return dict(spec=spec, ok=True, enc=d_enc(D), file=path, skipped=True,
                    ni='%d*j+%d' % D['ci'], no='cascade')
    open(path, 'w').write(src)
    ok, log = E.coqc(os.path.relpath(path, REPO))
    if not ok:
        os.remove(path)
        lg = [l for l in log.strip().splitlines() if l.strip()]
        return dict(spec=spec, ok=False,
                    why='cascade coqc: ' + (lg[-1] if lg else '?'))
    return dict(spec=spec, ok=True, enc=d_enc(D), file=path,
                ni='%d*j+%d' % D['ci'], no='cascade')


def d_enc(D):
    return D['d']['anchor']['enc'] + ('/mirror' if D['mirrored'] else '')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--proto')
    ap.add_argument('--board')
    ap.add_argument('--boards', help='spec-list file: emit + coqc each')
    ap.add_argument('-K', type=int, default=7)
    ap.add_argument('-o')
    ap.add_argument('--force', action='store_true')
    a = ap.parse_args()
    if a.proto:
        txt = proto(a.proto, a.K, a.o)
        if not a.o:
            sys.stdout.write(txt)
        return
    if a.board:
        r = process_board(a.board, True, a.force, a.K)
        print(r)
        return
    if a.boards:
        specs = [l.strip() for l in open(a.boards) if l.strip()]
        nok = 0
        for i, spec in enumerate(specs):
            r = process_board(spec, True, a.force, a.K)
            nok += bool(r['ok'])
            print('%3d/%d %-40s %s'
                  % (i + 1, len(specs), spec,
                     ('OK %s %s' % (r['enc'], r.get('file', '')))
                     if r['ok'] else r['why'][:120]), flush=True)
        print('%d / %d boarded' % (nok, len(specs)))
        return
    ap.error('one of --proto / --board / --boards is required')


if __name__ == '__main__':
    main()
