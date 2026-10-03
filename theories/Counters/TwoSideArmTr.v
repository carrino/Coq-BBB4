(** * Counters.TwoSideArmTr: arm families with BOTH tails opaque
    (SCOPING_INSTR 7.4.LE9).

    [NestCountTr.armfam_r] / [armfam_l] state an arm family with one opaque
    tail; the far side is a literal.  A counter held on BOTH sides of the
    head (LE7's zig-zag mirrors) is crossed one copy at a time, and while
    one copy is crossed the other is an opaque tail on the far side.  These
    are the same lemmas with the far side [literal ++ X] for any [X] the
    arm's flag allows ([armfam2_lr] / [armfam2_rl]: a pass that carries
    the block across the head), plus the fire witnesses in the same shape.

    Nothing landed is modified.  Axiom footprint: [functional_extensionality_dep],
    via [CTape.lift]. *)
From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape.
From BBB4.Checkers Require Import LapDecider LadderKernel LadderCheck LadderNest LadderCheckNestTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import NestCountTr.
Import ListNotations.

Section TwoSide.
Variable tm : TM.

(** a block on the right, the left an opaque tail *)
Lemma armfam2_r : forall el er N0 st (AR : nat -> LRule)
    q1 L1 h1 P1 w1 W1 q2 L2 h2 P2 w2 W2,
  0 < st ->
  (forall r, r < N0 + st -> ReachL tm el er (lr_lhs (AR r)) (lr_rhs (AR r))) ->
  (forall r, r < N0 + st ->
     lr_lhs (AR r) = mkC q1 (sflat L1) h1 (blk (P1 ++ rep w1 r) w1 (astride N0 st r) W1)) ->
  (forall r, r < N0 + st ->
     lr_rhs (AR r) = mkC q2 (sflat L2) h2 (blk (P2 ++ rep w2 r) w2 (astride N0 st r) W2)) ->
  forall k XL XR, (el = true -> XL = []) -> (er = true -> XR = []) ->
  Reach1 tm (q1, (L1 ++ XL, h1, P1 ++ rep w1 k ++ W1 ++ XR))
            (q2, (L2 ++ XL, h2, P2 ++ rep w2 k ++ W2 ++ XR)).
Proof.
  intros el er N0 st AR q1 L1 h1 P1 w1 W1 q2 L2 h2 P2 w2 W2 Hst HS HL HR k XL XR HXL HXR.
  set (r := aoff N0 st k).
  assert (Hr : r < N0 + st) by (apply arm_index_lt; exact Hst).
  assert (Hk : r + astride N0 st r * acnt N0 st k = k) by (apply arm_index; exact Hst).
  pose proof (reachL_reach1 tm el er _ _ XL XR (acnt N0 st k) (HS r Hr) HXL HXR) as H.
  rewrite (HL r Hr), (HR r Hr) in H. unfold cden in H; cbn [c_st c_l c_h c_r] in H.
  rewrite !sden_flat, !sden_blk_rep, Hk in H. exact H.
Qed.

(** a block on the left, the right an opaque tail *)
Lemma armfam2_l : forall el er N0 st (AR : nat -> LRule)
    q1 R1 h1 P1 w1 W1 q2 R2 h2 P2 w2 W2,
  0 < st ->
  (forall r, r < N0 + st -> ReachL tm el er (lr_lhs (AR r)) (lr_rhs (AR r))) ->
  (forall r, r < N0 + st ->
     lr_lhs (AR r) = mkC q1 (blk (P1 ++ rep w1 r) w1 (astride N0 st r) W1) h1 (sflat R1)) ->
  (forall r, r < N0 + st ->
     lr_rhs (AR r) = mkC q2 (blk (P2 ++ rep w2 r) w2 (astride N0 st r) W2) h2 (sflat R2)) ->
  forall k XL XR, (el = true -> XL = []) -> (er = true -> XR = []) ->
  Reach1 tm (q1, (P1 ++ rep w1 k ++ W1 ++ XL, h1, R1 ++ XR))
            (q2, (P2 ++ rep w2 k ++ W2 ++ XL, h2, R2 ++ XR)).
Proof.
  intros el er N0 st AR q1 R1 h1 P1 w1 W1 q2 R2 h2 P2 w2 W2 Hst HS HL HR k XL XR HXL HXR.
  set (r := aoff N0 st k).
  assert (Hr : r < N0 + st) by (apply arm_index_lt; exact Hst).
  assert (Hk : r + astride N0 st r * acnt N0 st k = k) by (apply arm_index; exact Hst).
  pose proof (reachL_reach1 tm el er _ _ XL XR (acnt N0 st k) (HS r Hr) HXL HXR) as H.
  rewrite (HL r Hr), (HR r Hr) in H. unfold cden in H; cbn [c_st c_l c_h c_r] in H.
  rewrite !sden_flat, !sden_blk_rep, Hk in H. exact H.
Qed.

(** the block crosses the head: on the left before, on the right after *)
Lemma armfam2_lr : forall el er N0 st (AR : nat -> LRule)
    q1 R1 h1 P1 w1 W1 q2 L2 h2 P2 w2 W2,
  0 < st ->
  (forall r, r < N0 + st -> ReachL tm el er (lr_lhs (AR r)) (lr_rhs (AR r))) ->
  (forall r, r < N0 + st ->
     lr_lhs (AR r) = mkC q1 (blk (P1 ++ rep w1 r) w1 (astride N0 st r) W1) h1 (sflat R1)) ->
  (forall r, r < N0 + st ->
     lr_rhs (AR r) = mkC q2 (sflat L2) h2 (blk (P2 ++ rep w2 r) w2 (astride N0 st r) W2)) ->
  forall k XL XR, (el = true -> XL = []) -> (er = true -> XR = []) ->
  Reach1 tm (q1, (P1 ++ rep w1 k ++ W1 ++ XL, h1, R1 ++ XR))
            (q2, (L2 ++ XL, h2, P2 ++ rep w2 k ++ W2 ++ XR)).
Proof.
  intros el er N0 st AR q1 R1 h1 P1 w1 W1 q2 L2 h2 P2 w2 W2 Hst HS HL HR k XL XR HXL HXR.
  set (r := aoff N0 st k).
  assert (Hr : r < N0 + st) by (apply arm_index_lt; exact Hst).
  assert (Hk : r + astride N0 st r * acnt N0 st k = k) by (apply arm_index; exact Hst).
  pose proof (reachL_reach1 tm el er _ _ XL XR (acnt N0 st k) (HS r Hr) HXL HXR) as H.
  rewrite (HL r Hr), (HR r Hr) in H. unfold cden in H; cbn [c_st c_l c_h c_r] in H.
  rewrite !sden_flat, !sden_blk_rep, Hk in H. exact H.
Qed.

(** the block crosses the head: on the right before, on the left after *)
Lemma armfam2_rl : forall el er N0 st (AR : nat -> LRule)
    q1 L1 h1 P1 w1 W1 q2 R2 h2 P2 w2 W2,
  0 < st ->
  (forall r, r < N0 + st -> ReachL tm el er (lr_lhs (AR r)) (lr_rhs (AR r))) ->
  (forall r, r < N0 + st ->
     lr_lhs (AR r) = mkC q1 (sflat L1) h1 (blk (P1 ++ rep w1 r) w1 (astride N0 st r) W1)) ->
  (forall r, r < N0 + st ->
     lr_rhs (AR r) = mkC q2 (blk (P2 ++ rep w2 r) w2 (astride N0 st r) W2) h2 (sflat R2)) ->
  forall k XL XR, (el = true -> XL = []) -> (er = true -> XR = []) ->
  Reach1 tm (q1, (L1 ++ XL, h1, P1 ++ rep w1 k ++ W1 ++ XR))
            (q2, (P2 ++ rep w2 k ++ W2 ++ XL, h2, R2 ++ XR)).
Proof.
  intros el er N0 st AR q1 L1 h1 P1 w1 W1 q2 R2 h2 P2 w2 W2 Hst HS HL HR k XL XR HXL HXR.
  set (r := aoff N0 st k).
  assert (Hr : r < N0 + st) by (apply arm_index_lt; exact Hst).
  assert (Hk : r + astride N0 st r * acnt N0 st k = k) by (apply arm_index; exact Hst).
  pose proof (reachL_reach1 tm el er _ _ XL XR (acnt N0 st k) (HS r Hr) HXL HXR) as H.
  rewrite (HL r Hr), (HR r Hr) in H. unfold cden in H; cbn [c_st c_l c_h c_r] in H.
  rewrite !sden_flat, !sden_blk_rep, Hk in H. exact H.
Qed.

(** no block at all *)
Lemma arm2_flat : forall el er A q1 L1 h1 R1 q2 L2 h2 R2,
  ReachL tm el er (lr_lhs A) (lr_rhs A) ->
  lr_lhs A = mkC q1 (sflat L1) h1 (sflat R1) ->
  lr_rhs A = mkC q2 (sflat L2) h2 (sflat R2) ->
  forall XL XR, (el = true -> XL = []) -> (er = true -> XR = []) ->
  Reach1 tm (q1, (L1 ++ XL, h1, R1 ++ XR)) (q2, (L2 ++ XL, h2, R2 ++ XR)).
Proof.
  intros el er A q1 L1 h1 R1 q2 L2 h2 R2 HS HL HR XL XR HXL HXR.
  pose proof (reachL_reach1 tm el er _ _ XL XR 0 HS HXL HXR) as H.
  rewrite HL, HR in H. unfold cden in H; cbn [c_st c_l c_h c_r] in H.
  rewrite !sden_flat in H. exact H.
Qed.

(** fire witnesses in the same shapes *)
Lemma fire2_r : forall el er rs N0 st (sg : nat -> list nseg) (vl : nat -> list lstep)
    (lhs : nat -> sconf) q1 L1 h1 P1 w1 W1 t,
  0 < st ->
  Forall (RuleSound tm false false) rs ->
  (forall r, r < N0 + st -> nfire tm el er rs (sg r) (vl r) (lhs r) = Some t) ->
  (forall r, r < N0 + st ->
     lhs r = mkC q1 (sflat L1) h1 (blk (P1 ++ rep w1 r) w1 (astride N0 st r) W1)) ->
  forall k XL XR, (el = true -> XL = []) -> (er = true -> XR = []) ->
  Fires tm (q1, (L1 ++ XL, h1, P1 ++ rep w1 k ++ W1 ++ XR)) t.
Proof.
  intros el er rs N0 st sg vl lhs q1 L1 h1 P1 w1 W1 t Hst Hrs HF HL k XL XR HXL HXR.
  set (r := aoff N0 st k).
  assert (Hr : r < N0 + st) by (apply arm_index_lt; exact Hst).
  assert (Hk : r + astride N0 st r * acnt N0 st k = k) by (apply arm_index; exact Hst).
  destruct (nfire_sound tm el er rs (sg r) (vl r) (lhs r) t Hrs (HF r Hr)
              XL XR (acnt N0 st k) HXL HXR) as (m & c' & Hc & Ht).
  rewrite (HL r Hr) in Hc. unfold cden in Hc; cbn [c_st c_l c_h c_r] in Hc.
  rewrite !sden_flat, !sden_blk_rep, Hk in Hc.
  exists m, c'. split; assumption.
Qed.

Lemma fire2_l : forall el er rs N0 st (sg : nat -> list nseg) (vl : nat -> list lstep)
    (lhs : nat -> sconf) q1 R1 h1 P1 w1 W1 t,
  0 < st ->
  Forall (RuleSound tm false false) rs ->
  (forall r, r < N0 + st -> nfire tm el er rs (sg r) (vl r) (lhs r) = Some t) ->
  (forall r, r < N0 + st ->
     lhs r = mkC q1 (blk (P1 ++ rep w1 r) w1 (astride N0 st r) W1) h1 (sflat R1)) ->
  forall k XL XR, (el = true -> XL = []) -> (er = true -> XR = []) ->
  Fires tm (q1, (P1 ++ rep w1 k ++ W1 ++ XL, h1, R1 ++ XR)) t.
Proof.
  intros el er rs N0 st sg vl lhs q1 R1 h1 P1 w1 W1 t Hst Hrs HF HL k XL XR HXL HXR.
  set (r := aoff N0 st k).
  assert (Hr : r < N0 + st) by (apply arm_index_lt; exact Hst).
  assert (Hk : r + astride N0 st r * acnt N0 st k = k) by (apply arm_index; exact Hst).
  destruct (nfire_sound tm el er rs (sg r) (vl r) (lhs r) t Hrs (HF r Hr)
              XL XR (acnt N0 st k) HXL HXR) as (m & c' & Hc & Ht).
  rewrite (HL r Hr) in Hc. unfold cden in Hc; cbn [c_st c_l c_h c_r] in Hc.
  rewrite !sden_flat, !sden_blk_rep, Hk in Hc.
  exists m, c'. split; assumption.
Qed.

Lemma fire2_flat : forall el er rs sg vl (lhs : sconf) q1 L1 h1 R1 t,
  Forall (RuleSound tm false false) rs ->
  nfire tm el er rs sg vl lhs = Some t ->
  lhs = mkC q1 (sflat L1) h1 (sflat R1) ->
  forall XL XR, (el = true -> XL = []) -> (er = true -> XR = []) ->
  Fires tm (q1, (L1 ++ XL, h1, R1 ++ XR)) t.
Proof.
  intros el er rs sg vl lhs q1 L1 h1 R1 t Hrs HF HL XL XR HXL HXR.
  destruct (nfire_sound tm el er rs sg vl lhs t Hrs HF XL XR 0 HXL HXR) as (m & c' & Hc & Ht).
  rewrite HL in Hc. unfold cden in Hc; cbn [c_st c_l c_h c_r] in Hc.
  rewrite !sden_flat in Hc. exists m, c'. split; assumption.
Qed.

End TwoSide.
