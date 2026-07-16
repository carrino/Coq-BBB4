(** * Exp_2: the exp_counter machine #2, 1RB0LA_1LC0RB_1RD1LD_1LA1RC.

    First machine of the BBB harness's [exp_counter] family
    (certificate results/counter2.cert: side R, edge state D, moff 1,
    bootstrap v0 = 1).  The anchor is a two-cell pair with the value
    v kept on BOTH sides:

      C(v) = (StD, (1 :: Tp (v+1), 1, Wp v)),

    the W side (right) v in odd-cell binary (MonoCounter.Wp), the
    marker side (left) v+1 as stride-3 markers (ExpCounter.Tp).  One
    lap C(v) -> C(v+1) is a binary +1 on both sides: a 2-step cycle
    crosses the W carry run, a 4-step unit flips the clear bit (or
    writes it into blank territory), a 1-step walk-back zeroes the
    trail; then a 5-step bounce cycle crosses the set markers, an
    8-step stop sets the clear (or fresh, off the tape edge) marker,
    a 1-step run zeroes the bounce trail and a 3-step unit rebuilds
    the anchor pair.  With moff 1 exactly one side carries per lap
    (trailing_ones(v) vs trailing_ones(v+1)); the proof cases over
    both carry views independently.  Laps end exactly at C(v+1).
    Validated differentially for v = 1..300
    (tools/counters/lap2.py). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter ExpCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB0LA_1LC0RB_1RD1LD_1LA1RC *)
Definition tm_2 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StA
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DR StB
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S1 DL StD
  | StD, S0 => mk S1 DL StA | StD, S1 => mk S1 DR StC
  end.

Definition Cc (p : positive) : cconf :=
  (StD, (S1 :: Tp (Pos.succ p), S1, Wp p)).

(** ** The unit runs *)

(** UWout: the W-side carry crossing (2 steps/set bit). *)
Lemma UWout : wsteps true true tm_2 2 (StD, ([], S1, [S0; S1]))
              = Some (StD, ([S1; S1], S1, [])).
Proof. reflexivity. Qed.

(** UWf: flip the clear W bit, restore the filler. *)
Lemma UWf : wsteps true true tm_2 4 (StD, ([], S1, [S0; S0]))
            = Some (StA, ([], S1, [S0; S1])).
Proof. reflexivity. Qed.

(** UWfE: the W overflow -- a fresh MSB beyond the right edge. *)
Lemma UWfE : wsteps true false tm_2 4 (StD, ([], S1, []))
             = Some (StA, ([], S1, [S0; S1])).
Proof. reflexivity. Qed.

(** UWb: the walk-back zeroing the W trail (1 step/cell). *)
Lemma UWb : wsteps true true tm_2 1 (StA, ([S1], S1, []))
            = Some (StA, ([], S1, [S0])).
Proof. reflexivity. Qed.

(** UMs: the marker-side bounce stride over a set marker. *)
Lemma UMs : wsteps true true tm_2 5 (StA, ([S0; S0; S1], S1, []))
            = Some (StA, ([], S1, [S1; S1; S1])).
Proof. reflexivity. Qed.

(** UMi: interior marker stop -- set the clear marker. *)
Lemma UMi : wsteps true true tm_2 8 (StA, ([S0; S0; S0], S1, []))
            = Some (StB, ([S0; S0; S1], S1, [])).
Proof. reflexivity. Qed.

(** UMo: overflow stop -- a fresh marker beyond the left edge. *)
Lemma UMo : wsteps false true tm_2 8 (StA, ([], S1, []))
            = Some (StB, ([S0; S0; S1], S1, [])).
Proof. reflexivity. Qed.

(** UBr: the B-run zeroing the bounce trail (1 step/cell). *)
Lemma UBr : wsteps true true tm_2 1 (StB, ([], S1, [S1]))
            = Some (StB, ([S0], S1, [])).
Proof. reflexivity. Qed.

(** UEnd: rebuild the anchor pair. *)
Lemma UEnd : wsteps true true tm_2 3 (StB, ([], S1, [S0]))
             = Some (StD, ([S1], S1, [])).
Proof. reflexivity. Qed.

(** Visit witnesses: C after 1 step, B two steps past the walk-back. *)
Lemma UVC : wsteps true true tm_2 1 (StD, ([], S1, [S0]))
            = Some (StC, ([S1], S0, [])).
Proof. reflexivity. Qed.

Lemma UVB : wsteps true true tm_2 2 (StA, ([S0], S1, []))
            = Some (StB, ([S1], S0, [])).
Proof. reflexivity. Qed.

(** ** Transported phases *)

Lemma phUWout : forall k L R,
  csteps tm_2 (2 * k) (StD, (L, S1, rep [S0; S1] k ++ R))
  = Some (StD, (rep [S1; S1] k ++ L, S1, R)).
Proof. intros. exact (cycR _ _ _ _ _ _ UWout k L R). Qed.

Lemma phUWf : forall L R,
  csteps tm_2 4 (StD, (L, S1, S0 :: S0 :: R))
  = Some (StA, (L, S1, S0 :: S1 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UWf). Qed.

Lemma phUWfE : forall L,
  csteps tm_2 4 (StD, (L, S1, []))
  = Some (StA, (L, S1, [S0; S1])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L UWfE). Qed.

Lemma phUWb : forall k L R,
  csteps tm_2 k (StA, (rep [S1] k ++ L, S1, R))
  = Some (StA, (L, S1, rep [S0] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ UWb k L R) as H.
  rewrite Nat.mul_1_l in H; cbn [app] in H.
  exact H.
Qed.

Lemma phUMs : forall k L R,
  csteps tm_2 (5 * k) (StA, (rep [S0; S0; S1] k ++ L, S1, R))
  = Some (StA, (L, S1, rep [S1; S1; S1] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ UMs k L R) as H; cbn [app] in H.
  exact H.
Qed.

Lemma phUMi : forall L R,
  csteps tm_2 8 (StA, (S0 :: S0 :: S0 :: L, S1, R))
  = Some (StB, (S0 :: S0 :: S1 :: L, S1, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UMi). Qed.

Lemma phUMo : forall R,
  csteps tm_2 8 (StA, ([], S1, R))
  = Some (StB, ([S0; S0; S1], S1, R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R UMo). Qed.

Lemma phUBr : forall k L R,
  csteps tm_2 k (StB, (L, S1, rep [S1] k ++ R))
  = Some (StB, (rep [S0] k ++ L, S1, R)).
Proof.
  intros.
  pose proof (cycR _ _ _ _ _ _ UBr k L R) as H.
  rewrite Nat.mul_1_l in H.
  exact H.
Qed.

Lemma phUEnd : forall L R,
  csteps tm_2 3 (StB, (L, S1, S0 :: R))
  = Some (StD, (S1 :: L, S1, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UEnd). Qed.

Lemma phUVC : forall L R,
  csteps tm_2 1 (StD, (L, S1, S0 :: R))
  = Some (StC, (S1 :: L, S0, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UVC). Qed.

Lemma phUVB : forall L R,
  csteps tm_2 2 (StA, (S0 :: L, S1, R))
  = Some (StB, (S1 :: L, S0, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UVB). Qed.

(** ** The lap *)

Lemma lap_2 : forall p,
  exists n c', csteps tm_2 n (Cc p) = Some c' /\
               lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p.
  destruct (cview p) as [j o] eqn:Ep.
  destruct (cview (Pos.succ p)) as [jm om] eqn:Es.
  unfold Cc.
  destruct o as [q|]; destruct om as [qm|].
  - (* W interior, marker interior *)
    destruct (cview_some_W p j q Ep) as (HWp & HWs).
    destruct (cview_some_T (Pos.succ p) jm qm Es) as (HTp & HTs).
    do 2 eexists. split; [|split].
    + rewrite HWp, HTp.
      eapply csteps_chain. { apply phUWout. }
      eapply csteps_chain. { apply phUWf. }
      rewrite ones_fold_S.
      eapply csteps_chain. { apply phUWb. }
      eapply csteps_chain. { apply phUMs. }
      eapply csteps_chain. { apply phUMi. }
      rewrite rep_tpl.
      eapply csteps_chain. { apply phUBr. }
      change (rep [S0] (S (2 * j)) ++ S0 :: S1 :: Wp q)
        with (S0 :: rep [S0] (2 * j) ++ S0 :: S1 :: Wp q).
      apply phUEnd.
    + rewrite HWs, HTs, rep_dbl.
      reflexivity.
    + lia.
  - (* W interior, marker overflow *)
    destruct (cview_some_W p j q Ep) as (HWp & HWs).
    destruct (cview_none_T (Pos.succ p) jm Es) as (HTp & HTs).
    do 2 eexists. split; [|split].
    + rewrite HWp, HTp, <- (app_nil_r (rep [S0; S0; S1] jm)).
      eapply csteps_chain. { apply phUWout. }
      eapply csteps_chain. { apply phUWf. }
      rewrite ones_fold_S.
      eapply csteps_chain. { apply phUWb. }
      eapply csteps_chain. { apply phUMs. }
      eapply csteps_chain. { apply phUMo. }
      rewrite rep_tpl.
      eapply csteps_chain. { apply phUBr. }
      change (rep [S0] (S (2 * j)) ++ S0 :: S1 :: Wp q)
        with (S0 :: rep [S0] (2 * j) ++ S0 :: S1 :: Wp q).
      apply phUEnd.
    + rewrite HWs, HTs, rep_dbl.
      reflexivity.
    + lia.
  - (* W overflow, marker interior *)
    destruct (cview_none_W p j Ep) as (HWp & HWs).
    destruct (cview_some_T (Pos.succ p) jm qm Es) as (HTp & HTs).
    do 2 eexists. split; [|split].
    + rewrite HWp, HTp, <- (app_nil_r (rep [S0; S1] j)).
      eapply csteps_chain. { apply phUWout. }
      eapply csteps_chain. { apply phUWfE. }
      rewrite ones_fold_S.
      eapply csteps_chain. { apply phUWb. }
      eapply csteps_chain. { apply phUMs. }
      eapply csteps_chain. { apply phUMi. }
      rewrite rep_tpl.
      eapply csteps_chain. { apply phUBr. }
      change (rep [S0] (S (2 * j)) ++ [S0; S1])
        with (S0 :: rep [S0] (2 * j) ++ [S0; S1]).
      apply phUEnd.
    + rewrite HWs, HTs, rep_dbl.
      reflexivity.
    + lia.
  - (* W overflow, marker overflow (vacuous but closes) *)
    destruct (cview_none_W p j Ep) as (HWp & HWs).
    destruct (cview_none_T (Pos.succ p) jm Es) as (HTp & HTs).
    do 2 eexists. split; [|split].
    + rewrite HWp, HTp, <- (app_nil_r (rep [S0; S1] j)),
        <- (app_nil_r (rep [S0; S0; S1] jm)).
      eapply csteps_chain. { apply phUWout. }
      eapply csteps_chain. { apply phUWfE. }
      rewrite ones_fold_S.
      eapply csteps_chain. { apply phUWb. }
      eapply csteps_chain. { apply phUMs. }
      eapply csteps_chain. { apply phUMo. }
      rewrite rep_tpl.
      eapply csteps_chain. { apply phUBr. }
      change (rep [S0] (S (2 * j)) ++ [S0; S1])
        with (S0 :: rep [S0] (2 * j) ++ [S0; S1]).
      apply phUEnd.
    + rewrite HWs, HTs, rep_dbl.
      reflexivity.
    + lia.
Qed.

(** ** Bootstrap, visits, and the theorem *)

Lemma boot_2 : exists t0, stepn tm_2 t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 34.
  assert (H : match csteps tm_2 34 c0 with
              | Some c => ceqb c (Cc 1)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_2 34 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

Lemma vis_2 : forall p q,
  exists k c, csteps tm_2 k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q.
  unfold Cc.
  destruct q.
  - (* StA: the W flip's exit state *)
    destruct (cview p) as [j o] eqn:Ep.
    destruct o as [q0|].
    + destruct (cview_some_W p j q0 Ep) as (HWp & _).
      do 2 eexists. split.
      * rewrite HWp.
        eapply csteps_chain. { apply phUWout. }
        apply phUWf.
      * reflexivity.
    + destruct (cview_none_W p j Ep) as (HWp & _).
      do 2 eexists. split.
      * rewrite HWp, <- (app_nil_r (rep [S0; S1] j)).
        eapply csteps_chain. { apply phUWout. }
        apply phUWfE.
      * reflexivity.
  - (* StB: two steps past the walk-back *)
    destruct (Tp_head (Pos.succ p)) as (w & Hw).
    destruct (cview p) as [j o] eqn:Ep.
    destruct o as [q0|].
    + destruct (cview_some_W p j q0 Ep) as (HWp & _).
      do 2 eexists. split.
      * rewrite HWp, Hw.
        eapply csteps_chain. { apply phUWout. }
        eapply csteps_chain. { apply phUWf. }
        rewrite ones_fold_S.
        eapply csteps_chain. { apply phUWb. }
        apply phUVB.
      * reflexivity.
    + destruct (cview_none_W p j Ep) as (HWp & _).
      do 2 eexists. split.
      * rewrite HWp, Hw, <- (app_nil_r (rep [S0; S1] j)).
        eapply csteps_chain. { apply phUWout. }
        eapply csteps_chain. { apply phUWfE. }
        rewrite ones_fold_S.
        eapply csteps_chain. { apply phUWb. }
        apply phUVB.
      * reflexivity.
  - (* StC after 1 step *)
    destruct (Wp_head p) as (w & Hw).
    exists 1. eexists. split.
    + rewrite Hw. apply phUVC.
    + reflexivity.
  - exists 0. eexists. split; reflexivity.
Qed.

(** #2 never quasihalts: bbchallenge 1RB0LA_1LC0RB_1RD1LD_1LA1RC. *)
Theorem nqh_1RB0LA_1LC0RB_1RD1LD_1LA1RC : NeverQuasiHaltsSt tm_2.
Proof.
  apply (glue_neverqh tm_2 Cc 1).
  - exact boot_2.
  - intros p _. apply lap_2.
  - intros p q _. apply vis_2.
Qed.

Theorem tm_2_nonhalt : NonHalt tm_2.
Proof. apply never_qh_nonhalt, nqh_1RB0LA_1LC0RB_1RD1LD_1LA1RC. Qed.
