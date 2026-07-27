(** * WrapBounce: the two [1RB---] wrap holdouts, boarded by a SHARED core.

    The last two members of the frozen holdout list are

      W15 = 1RB---_1RC0RB_0LC0RD_1LD1LB
      W07 = 1RB---_1LC0LB_0RC0LD_1RD1RB

    Both quasihalt for a trivial reason -- no transition targets [StA], so
    [StA] is visited once and is quiet from index 0 -- and both already
    carried [NonHalt /\ QuietAfter tm StA 0 /\ QuasiHaltsSt] from
    [Machines/Bulk/Wrap_01.v].  That is NOT enough to board: [boarded] wants
    [exists B, QHBound B tm], i.e. EVERY quiet state bounded, and knowing
    [StA] is quiet says nothing about [StB]/[StC]/[StD].  The open content is
    therefore a LIVENESS statement on the 3-state core -- B, C and D are each
    visited infinitely often -- which is exactly [LapGlueQH.glue_qh]'s
    hypothesis set.  (This is also why the never-QH checkers correctly
    rejected these two: pointed at the 4-state machine from the blank tape,
    [StA] genuinely is quiet.)

    ** One core, two machines

    [mirror_tm W07 = 1LB---_1RC0RB_0LC0RD_1LD1LB] differs from [W15] ONLY in
    [StA]'s direction, so the two share the {B,C,D} table VERBATIM.  Every
    lemma below is proved once in [Section Core] against six transition
    hypotheses; the two machines differ only in their bootstrap step count
    (7 for W15, 6 for the mirror of W07), and W07 comes back through
    [Mirror].  Nothing in the core lemmas mentions [StA]'s row, which is the
    whole reason the sharing works.

    ** The counter

    The recurrent shape is the "wall at the left, ones to the right" config

      E(n) = (StB, ([], S0, rep [S1] n))

    reached at n = 3, 7, 15, 31, 63, ... -- one lap DOUBLES the block,
    E(n) -> E(2n+1), in exactly n^2 + 6n - 2 steps.  Writing n = 2m+3, the
    lap is a flat composition of seven frame-polymorphic units:

      RATCHET  (StB, (L, S0, S1::S1::r))    -3-> (StB, (S1::L, S0, S1::r))
      TURN1    (StB, (S1::L, S0, [S1]))     -5-> (StB, (L, S1, [S1;S1;S1]))
      SWEEPR   (StB, (L, S1, rep [S1] b))   -(b+1)-> (StB, (rep [S0] (S b) ++ L, S0, []))
      TURN2    (StB, (L, S0, []))           -3-> (StD, (S0::L, S0, []))
      SWEEPL   (StD, (rep [S0] m ++ L, S0, r)) -m-> (StD, (L, S0, rep [S1] m ++ r))
      TURNL    (StD, (S1::S1::L, S0, r))    -2-> (StB, (L, S1, S1::S1::r))
      TURNL1   (StD, ([S1], S0, r))         -2-> (StB, ([], S0, S1::S1::r))

      E(n) --RATCHET^(n-1)--> (StB, (1^(n-1), S0, [S1]))
           --TURN1-->         (StB, (1^(n-2), S1, 1^3))
           --BOUNCE^m-->      (StB, ([S1],    S1, 1^(4m+3)))
           --CLOSE-->         E(2n+1)

      BOUNCE = SWEEPR . TURN2 . SWEEPL . TURNL   (a -= 2, b += 4)
      CLOSE  = SWEEPR . TURN2 . SWEEPL . TURNL1  (a = 1, lands on E(b+4))

    The head never leaves the units: [tools/counters/lapwrap.py] rebuilds
    each lap out of these seven alone and diffs the composite against the raw
    stepper for n = 3 .. 255 -- unit coverage is 100%, with no boundary
    gadget left over, and both the step counts and the exact configurations
    agree.

    Axiom footprint: [functional_extensionality_dep] only (via [CTape.lift]
    and the two [mirror_tm] table identities). *)

From Coq Require Import Arith Lia Bool List PArith FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From BBB4.Counters Require Import WTape LapGlueQH CReach.
From BBB4.Census Require Import TNF_QH.
Import ListNotations.

Definition mk_wrapb (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).
Local Notation mk := mk_wrapb.

(** ** The anchor family

    [wcnt k] is the block length after [k] laps: 3, 7, 15, 31, ... *)

Fixpoint wcnt (k : nat) : nat :=
  match k with O => 3 | S k' => 2 * wcnt k' + 1 end.

Definition Cw (p : positive) : cconf :=
  (StB, ([], S0, rep [S1] (wcnt (Nat.pred (Pos.to_nat p))))).

Lemma wcnt_succ : forall p,
  wcnt (Nat.pred (Pos.to_nat (Pos.succ p))) = 2 * wcnt (Nat.pred (Pos.to_nat p)) + 1.
Proof.
  intro p. rewrite Pos2Nat.inj_succ. cbn [Nat.pred].
  pose proof (Pos2Nat.is_pos p) as Hp.
  destruct (Pos.to_nat p) as [|x] eqn:E; [lia|]. cbn [Nat.pred]. reflexivity.
Qed.

(** Every block length is odd and at least 3 -- the form the lap needs. *)
Lemma wcnt_form : forall k, exists m, wcnt k = 2 * m + 3.
Proof.
  induction k as [|k (m & IH)].
  - exists 0. reflexivity.
  - exists (2 * m + 2). cbn [wcnt]. rewrite IH. lia.
Qed.

(** A repeated cell absorbed at the far end of its own repetition -- the
    only list identity the lap needs, in the direction the units want it. *)
Lemma rep_snoc_cons : forall (x : Sym) k X, rep [x] k ++ x :: X = x :: rep [x] k ++ X.
Proof. intros. symmetry. apply rep_slide. Qed.

(** ** The core

    Six transition equations; [StA]'s row is never mentioned. *)

Section Core.

Variable tm : TM.

Hypothesis HB0 : tm StB S0 = Some (mkTrans S1 DR StC).
Hypothesis HB1 : tm StB S1 = Some (mkTrans S0 DR StB).
Hypothesis HC0 : tm StC S0 = Some (mkTrans S0 DL StC).
Hypothesis HC1 : tm StC S1 = Some (mkTrans S0 DR StD).
Hypothesis HD0 : tm StD S0 = Some (mkTrans S1 DL StD).
Hypothesis HD1 : tm StD S1 = Some (mkTrans S1 DL StB).

(** Peel EXACTLY one step.  [cbn [csteps]] is wrong here: on a symbolic
    count [S b] it keeps unfolding the recursive call, so the induction
    hypotheses of [u_sweepr]/[u_sweepl] no longer match. *)
Lemma cstepsS_ : forall n c,
  csteps tm (S n) c =
  match cstep tm c with Some c' => csteps tm n c' | None => None end.
Proof. reflexivity. Qed.

(** One computable step, driven by the transition equation for it. *)
Ltac stp H :=
  rewrite cstepsS_; cbn [cstep]; rewrite H;
  cbn [t_next t_dir t_write ctape_move chd ctl].

(** *** The seven units *)

Lemma u_ratchet : forall L r,
  csteps tm 3 (StB, (L, S0, S1 :: S1 :: r)) = Some (StB, (S1 :: L, S0, S1 :: r)).
Proof. intros. stp HB0. stp HC1. stp HD1. reflexivity. Qed.

Lemma u_turn1 : forall L,
  csteps tm 5 (StB, (S1 :: L, S0, [S1])) = Some (StB, (L, S1, [S1; S1; S1])).
Proof. intros. stp HB0. stp HC1. stp HD0. stp HD0. stp HD1. reflexivity. Qed.

Lemma u_sweepr : forall b L,
  csteps tm (S b) (StB, (L, S1, rep [S1] b))
  = Some (StB, (rep [S0] (S b) ++ L, S0, [])).
Proof.
  induction b as [|b IH]; intro L.
  - stp HB1. reflexivity.
  - change (rep [S1] (S b)) with (S1 :: rep [S1] b).
    stp HB1. rewrite IH, (rep_snoc_cons S0 (S b) L). reflexivity.
Qed.

Lemma u_turn2 : forall L,
  csteps tm 3 (StB, (L, S0, [])) = Some (StD, (S0 :: L, S0, [])).
Proof. intros. stp HB0. stp HC0. stp HC1. reflexivity. Qed.

Lemma u_sweepl : forall m L r,
  csteps tm m (StD, (rep [S0] m ++ L, S0, r))
  = Some (StD, (L, S0, rep [S1] m ++ r)).
Proof.
  induction m as [|m IH]; intros L r.
  - reflexivity.
  - change (rep [S0] (S m) ++ L) with (S0 :: (rep [S0] m ++ L)).
    stp HD0. rewrite IH, (rep_snoc_cons S1 m r). reflexivity.
Qed.

Lemma u_turnl : forall L r,
  csteps tm 2 (StD, (S1 :: S1 :: L, S0, r)) = Some (StB, (L, S1, S1 :: S1 :: r)).
Proof. intros. stp HD0. stp HD1. reflexivity. Qed.

Lemma u_turnl1 : forall r,
  csteps tm 2 (StD, ([S1], S0, r)) = Some (StB, ([], S0, S1 :: S1 :: r)).
Proof. intros. stp HD0. stp HD1. reflexivity. Qed.

(** *** The ratchet chain: cross the whole block, one cell per 3 steps *)

Lemma ratchet_k : forall k L r,
  csteps tm (3 * k) (StB, (L, S0, rep [S1] k ++ S1 :: r))
  = Some (StB, (rep [S1] k ++ L, S0, S1 :: r)).
Proof.
  induction k as [|k IH]; intros L r.
  - reflexivity.
  - replace (3 * S k) with (3 + 3 * k) by lia.
    rewrite csteps_add.
    (* expose the S1 :: S1 :: _ window RATCHET needs, by sliding the
       trailing S1 of the block back through the repetition *)
    change (rep [S1] (S k) ++ S1 :: r) with (S1 :: (rep [S1] k ++ S1 :: r)).
    rewrite (rep_snoc_cons S1 k r), u_ratchet.
    rewrite <- (rep_snoc_cons S1 k r), IH, (rep_snoc_cons S1 k L).
    reflexivity.
Qed.

(** *** The bounce: one out-and-back, [a -= 2] and [b += 4] *)

Lemma bounce_step : forall a b,
  creach tm (StB, (rep [S1] (2 + a), S1, rep [S1] b))
            (StB, (rep [S1] a, S1, rep [S1] (4 + b))).
Proof.
  intros a b.
  eapply creach_trans;
    [apply (creach_csteps _ _ _ _ (u_sweepr b (rep [S1] (2 + a))))|].
  eapply creach_trans;
    [apply (creach_csteps _ _ _ _ (u_turn2 (rep [S0] (S b) ++ rep [S1] (2 + a))))|].
  eapply creach_trans.
  { apply (creach_csteps _ (S (S b))).
    change (S0 :: rep [S0] (S b) ++ rep [S1] (2 + a))
      with (rep [S0] (S (S b)) ++ rep [S1] (2 + a)).
    apply u_sweepl. }
  apply (creach_csteps _ 2).
  change (rep [S1] (2 + a)) with (S1 :: S1 :: rep [S1] a).
  rewrite u_turnl, app_nil_r. reflexivity.
Qed.

Lemma bounce_close : forall b,
  creach tm (StB, ([S1], S1, rep [S1] b))
            (StB, ([], S0, rep [S1] (4 + b))).
Proof.
  intro b.
  eapply creach_trans; [apply (creach_csteps _ _ _ _ (u_sweepr b [S1]))|].
  eapply creach_trans;
    [apply (creach_csteps _ _ _ _ (u_turn2 (rep [S0] (S b) ++ [S1])))|].
  eapply creach_trans.
  { apply (creach_csteps _ (S (S b))).
    change (S0 :: rep [S0] (S b) ++ [S1]) with (rep [S0] (S (S b)) ++ [S1]).
    apply u_sweepl. }
  apply (creach_csteps _ 2).
  rewrite u_turnl1, app_nil_r. reflexivity.
Qed.

Lemma bounce_chain : forall j b,
  creach tm (StB, (rep [S1] (2 * j + 1), S1, rep [S1] b))
            (StB, ([S1], S1, rep [S1] (b + 4 * j))).
Proof.
  induction j as [|j IH]; intro b.
  - replace (2 * 0 + 1) with 1 by lia. replace (b + 4 * 0) with b by lia.
    cbn [rep app]. apply creach_refl.
  - eapply creach_trans.
    { replace (2 * S j + 1) with (2 + (2 * j + 1)) by lia.
      apply bounce_step. }
    eapply creach_trans; [apply IH|].
    replace (4 + b + 4 * j) with (b + 4 * S j) by lia.
    apply creach_refl.
Qed.

(** *** One lap of the counter, E(n) -> E(2n+1) for n = 2m+3 *)

Lemma lap_core : forall m, exists n,
  csteps tm n (StB, ([], S0, rep [S1] (2 * m + 3)))
  = Some (StB, ([], S0, rep [S1] (2 * (2 * m + 3) + 1))) /\ 0 < n.
Proof.
  intro m.
  eapply creach_pos with
    (n := 3 * (2 * m + 2)) (c1 := (StB, (rep [S1] (2 * m + 2), S0, [S1]))).
  - replace (2 * m + 3) with ((2 * m + 2) + 1) by lia.
    rewrite rep_add. change (rep [S1] 1) with [S1].
    rewrite ratchet_k, app_nil_r. reflexivity.
  - lia.
  - (* TURN1, then m bounces, then the close *)
    eapply creach_trans.
    { apply (creach_csteps _ 5).
      replace (2 * m + 2) with (1 + (2 * m + 1)) by lia.
      rewrite rep_add. change (rep [S1] 1) with [S1]. cbn [app].
      apply u_turn1. }
    eapply creach_trans.
    { change [S1; S1; S1] with (rep [S1] 3). apply bounce_chain. }
    eapply creach_trans; [apply bounce_close|].
    replace (4 + (3 + 4 * m)) with (2 * (2 * m + 3) + 1) by lia.
    apply creach_refl.
Qed.

(** *** The three [glue_qh] premises that are not syntactic *)

Lemma lap_w : forall p, (1 <= p)%positive -> exists n c',
  csteps tm n (Cw p) = Some c' /\ lift c' = lift (Cw (Pos.succ p)) /\ 0 < n.
Proof.
  intros p _. unfold Cw. rewrite wcnt_succ.
  destruct (wcnt_form (Nat.pred (Pos.to_nat p))) as (m & Hm). rewrite Hm.
  destruct (lap_core m) as (n & Hrun & Hn).
  exists n, (StB, ([], S0, rep [S1] (2 * (2 * m + 3) + 1))).
  split; [exact Hrun | split; [reflexivity | exact Hn]].
Qed.

Lemma vis_w : forall p q, (1 <= p)%positive -> q <> StA ->
  exists k c, csteps tm k (Cw p) = Some c /\ fst c = q.
Proof.
  intros p q _ Hq. unfold Cw.
  destruct (wcnt_form (Nat.pred (Pos.to_nat p))) as (m & Hm). rewrite Hm.
  replace (2 * m + 3) with (2 + (2 * m + 1)) by lia.
  rewrite rep_add. change (rep [S1] 2) with [S1; S1]. cbn [app].
  destruct q.
  - exfalso; exact (Hq eq_refl).
  - exists 0. eexists. split; reflexivity.
  - exists 1. eexists. split; [stp HB0; reflexivity | reflexivity].
  - exists 2. eexists. split; [stp HB0; stp HC1; reflexivity | reflexivity].
Qed.

(** *** The core theorem

    [Hboot] stays a hypothesis: it is the ONE thing the two machines do
    differently (7 steps vs 6). *)

Hypothesis Hboot : exists t0, stepn tm t0 InitES = Some (lift (Cw 1)).
Hypothesis Huntarget : forall q b tr, tm q b = Some tr -> t_next tr <> StA.

Theorem core_iqh : NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.
Proof.
  destruct (glue_qh tm Cw 1 Hboot lap_w vis_w Huntarget) as (Hn & Hb & Hq).
  split; [exact Hn | split; [| exact Hq]].
  apply (qhbound_mono 1 2000); [lia | exact Hb].
Qed.

End Core.

(** ** The census tier predicate *)

Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.

(** ** W15 = 1RB---_1RC0RB_0LC0RD_1LD1LB, boarded directly *)

Definition tm_1RB____1RC0RB_0LC0RD_1LD1LB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => None
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S0 DR StB
  | StC, S0 => mk S0 DL StC | StC, S1 => mk S0 DR StD
  | StD, S0 => mk S1 DL StD | StD, S1 => mk S1 DL StB end.

Lemma boot_w15 : exists t0,
  stepn tm_1RB____1RC0RB_0LC0RD_1LD1LB t0 InitES = Some (lift (Cw 1)).
Proof.
  exists 7.
  assert (H : match csteps tm_1RB____1RC0RB_0LC0RD_1LD1LB 7 c0 with
              | Some c => ceqb c (Cw 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm_1RB____1RC0RB_0LC0RD_1LD1LB 7 c0) as [c|] eqn:E;
    [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

Theorem iqh_1RB____1RC0RB_0LC0RD_1LD1LB : iqh tm_1RB____1RC0RB_0LC0RD_1LD1LB.
Proof.
  unfold iqh. apply (core_iqh tm_1RB____1RC0RB_0LC0RD_1LD1LB); try reflexivity.
  - exact boot_w15.
  - intros q b tr Ht; destruct q, b; cbn in Ht;
      try discriminate; injection Ht as <-; discriminate.
Qed.

Theorem nonhalt_1RB____1RC0RB_0LC0RD_1LD1LB :
  NonHalt tm_1RB____1RC0RB_0LC0RD_1LD1LB.
Proof. apply (proj1 iqh_1RB____1RC0RB_0LC0RD_1LD1LB). Qed.

(** ** W07 = 1RB---_1LC0LB_0RC0LD_1RD1RB, boarded through its mirror

    [mirror_tm W07 = 1LB---_1RC0RB_0LC0RD_1LD1LB] -- the SAME {B,C,D} table
    as W15, differing only in [StA]'s direction, and reaching the same
    anchor [Cw 1] one step sooner. *)

Definition tm_1RB____1LC0LB_0RC0LD_1RD1RB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => None
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DL StB
  | StC, S0 => mk S0 DR StC | StC, S1 => mk S0 DL StD
  | StD, S0 => mk S1 DR StD | StD, S1 => mk S1 DR StB end.

Definition tmm_1RB____1LC0LB_0RC0LD_1RD1RB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => None
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S0 DR StB
  | StC, S0 => mk S0 DL StC | StC, S1 => mk S0 DR StD
  | StD, S0 => mk S1 DL StD | StD, S1 => mk S1 DL StB end.

Lemma mirror_ok_w07 :
  mirror_tm tm_1RB____1LC0LB_0RC0LD_1RD1RB = tmm_1RB____1LC0LB_0RC0LD_1RD1RB.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Lemma boot_w07m : exists t0,
  stepn tmm_1RB____1LC0LB_0RC0LD_1RD1RB t0 InitES = Some (lift (Cw 1)).
Proof.
  exists 6.
  assert (H : match csteps tmm_1RB____1LC0LB_0RC0LD_1RD1RB 6 c0 with
              | Some c => ceqb c (Cw 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tmm_1RB____1LC0LB_0RC0LD_1RD1RB 6 c0) as [c|] eqn:E;
    [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

Theorem iqhm_1RB____1LC0LB_0RC0LD_1RD1RB : iqh tmm_1RB____1LC0LB_0RC0LD_1RD1RB.
Proof.
  unfold iqh. apply (core_iqh tmm_1RB____1LC0LB_0RC0LD_1RD1RB); try reflexivity.
  - exact boot_w07m.
  - intros q b tr Ht; destruct q, b; cbn in Ht;
      try discriminate; injection Ht as <-; discriminate.
Qed.

Theorem iqh_1RB____1LC0LB_0RC0LD_1RD1RB : iqh tm_1RB____1LC0LB_0RC0LD_1RD1RB.
Proof.
  destruct iqhm_1RB____1LC0LB_0RC0LD_1RD1RB as (Hn & Hb & Hq).
  rewrite <- mirror_ok_w07 in Hn, Hb, Hq.
  split; [exact (mirror_nonhalt _ Hn)
         | split; [exact (qhbound_mirror _ _ Hb)
                  | exact (mirror_qh _ Hq)]].
Qed.

Theorem nonhalt_1RB____1LC0LB_0RC0LD_1RD1RB :
  NonHalt tm_1RB____1LC0LB_0RC0LD_1RD1RB.
Proof. apply (proj1 iqh_1RB____1LC0LB_0RC0LD_1RD1RB). Qed.
