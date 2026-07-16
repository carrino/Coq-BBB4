(** * Exp_4: the exp_counter machine #4, 1RB0LA_1LC1RC_1RD1LB_1LA0RD.

    Second machine of the BBB harness's [exp_counter] family
    (certificate results/counter4.cert: side L, edge state C, moff 0,
    bootstrap v0 = 1).  Mirror geometry of #2: the W side is on the
    LEFT (MonoCounter.Wp) and the marker side on the RIGHT, encoding
    v itself (moff 0), in marker-first groups (ExpCounter.Gp) behind
    the 2-cell anchor stub:

      C(v) = (StC, (Wp v, 1, 1 :: 0 :: 0 :: Gp v)).

    With moff 0 both sides carry the same run j = trailing_ones(v),
    so one carry view drives the whole lap: a 2-step cycle crosses
    the W run leftward, a 4-step flip, a 1-step D-run zeroes the
    trail rightward, a 4-step junction enters the marker groups, a
    5-step bounce cycle crosses the set markers, a 2-step stop sets
    the clear marker (the overflow spelling crosses the last marker
    into blank territory first), a 1-step walk-back zeroes the
    bounce trail and a 3-step unit rebuilds the anchor.  Laps end
    exactly at C(v+1).  Validated differentially for v = 1..300
    (tools/counters/lap4.py). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter ExpCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB0LA_1LC1RC_1RD1LB_1LA0RD *)
Definition tm_4 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StA
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StC
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S1 DL StB
  | StD, S0 => mk S1 DL StA | StD, S1 => mk S0 DR StD
  end.

Definition Cc (p : positive) : cconf :=
  (StC, (Wp p, S1, S1 :: S0 :: S0 :: Gp p)).

(** ** The unit runs *)

(** UWout: the W-side carry crossing, leftward (2 steps/set bit). *)
Lemma UWout : wsteps true true tm_4 2 (StC, ([S0; S1], S1, []))
              = Some (StC, ([], S1, [S1; S1])).
Proof. reflexivity. Qed.

(** UWf: flip the clear W bit, restore the filler. *)
Lemma UWf : wsteps true true tm_4 4 (StC, ([S0; S0], S1, []))
            = Some (StD, ([S0; S1], S1, [])).
Proof. reflexivity. Qed.

(** UWfE: the W overflow -- a fresh MSB beyond the left edge. *)
Lemma UWfE : wsteps false true tm_4 4 (StC, ([], S1, []))
             = Some (StD, ([S0; S1], S1, [])).
Proof. reflexivity. Qed.

(** UWb: the D-run zeroing the W trail rightward (1 step/cell). *)
Lemma UWb : wsteps true true tm_4 1 (StD, ([], S1, [S1]))
            = Some (StD, ([S0], S1, [])).
Proof. reflexivity. Qed.

(** UJ: the junction from the anchor stub into the marker groups. *)
Lemma UJ : wsteps true true tm_4 4 (StD, ([], S1, [S0; S0]))
           = Some (StC, ([S1; S1], S0, [])).
Proof. reflexivity. Qed.

(** UMs: the marker-side bounce stride over a set marker. *)
Lemma UMs : wsteps true true tm_4 5 (StC, ([], S0, [S1; S0; S0]))
            = Some (StC, ([S1; S1; S1], S0, [])).
Proof. reflexivity. Qed.

(** UMi: interior marker stop -- set the clear marker. *)
Lemma UMi : wsteps true true tm_4 2 (StC, ([], S0, [S0]))
            = Some (StA, ([], S1, [S1])).
Proof. reflexivity. Qed.

(** UMsE: the overflow stride across the last marker (right edge). *)
Lemma UMsE : wsteps true false tm_4 5 (StC, ([], S0, [S1]))
             = Some (StC, ([S1; S1; S1], S0, [])).
Proof. reflexivity. Qed.

(** UMo: overflow stop -- a fresh marker in blank territory. *)
Lemma UMo : wsteps true false tm_4 2 (StC, ([], S0, []))
            = Some (StA, ([], S1, [S1])).
Proof. reflexivity. Qed.

(** UAw: the A-walk zeroing the bounce trail (1 step/cell). *)
Lemma UAw : wsteps true true tm_4 1 (StA, ([S1], S1, []))
            = Some (StA, ([], S1, [S0])).
Proof. reflexivity. Qed.

(** UEnd: rebuild the anchor pair. *)
Lemma UEnd : wsteps true true tm_4 3 (StA, ([S0], S1, []))
             = Some (StC, ([], S1, [S1])).
Proof. reflexivity. Qed.

(** Visit witnesses: B after 1 step, A two steps into the junction. *)
Lemma UVB : wsteps true true tm_4 1 (StC, ([S0], S1, []))
            = Some (StB, ([], S0, [S1])).
Proof. reflexivity. Qed.

Lemma UVA : wsteps true true tm_4 2 (StD, ([], S1, [S0; S0]))
            = Some (StA, ([], S0, [S1; S0])).
Proof. reflexivity. Qed.

(** ** Transported phases *)

Lemma phUWout : forall k L R,
  csteps tm_4 (2 * k) (StC, (rep [S0; S1] k ++ L, S1, R))
  = Some (StC, (L, S1, rep [S1; S1] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ UWout k L R) as H; cbn [app] in H.
  exact H.
Qed.

Lemma phUWf : forall L R,
  csteps tm_4 4 (StC, (S0 :: S0 :: L, S1, R))
  = Some (StD, (S0 :: S1 :: L, S1, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UWf). Qed.

Lemma phUWfE : forall R,
  csteps tm_4 4 (StC, ([], S1, R))
  = Some (StD, ([S0; S1], S1, R)).
Proof. intros. exact (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R UWfE). Qed.

Lemma phUWb : forall k L R,
  csteps tm_4 k (StD, (L, S1, rep [S1] k ++ R))
  = Some (StD, (rep [S0] k ++ L, S1, R)).
Proof.
  intros.
  pose proof (cycR _ _ _ _ _ _ UWb k L R) as H.
  rewrite Nat.mul_1_l in H.
  exact H.
Qed.

Lemma phUJ : forall L R,
  csteps tm_4 4 (StD, (L, S1, S0 :: S0 :: R))
  = Some (StC, (S1 :: S1 :: L, S0, R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UJ). Qed.

Lemma phUMs : forall k L R,
  csteps tm_4 (5 * k) (StC, (L, S0, rep [S1; S0; S0] k ++ R))
  = Some (StC, (rep [S1; S1; S1] k ++ L, S0, R)).
Proof. intros. exact (cycR _ _ _ _ _ _ UMs k L R). Qed.

Lemma phUMi : forall L R,
  csteps tm_4 2 (StC, (L, S0, S0 :: R))
  = Some (StA, (L, S1, S1 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UMi). Qed.

Lemma phUMsE : forall L,
  csteps tm_4 5 (StC, (L, S0, [S1]))
  = Some (StC, (S1 :: S1 :: S1 :: L, S0, [])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L UMsE). Qed.

Lemma phUMo : forall L,
  csteps tm_4 2 (StC, (L, S0, []))
  = Some (StA, (L, S1, [S1])).
Proof. intros. exact (wsteps_frame_r _ _ _ _ _ _ _ _ _ _ L UMo). Qed.

Lemma phUAw : forall k L R,
  csteps tm_4 k (StA, (rep [S1] k ++ L, S1, R))
  = Some (StA, (L, S1, rep [S0] k ++ R)).
Proof.
  intros.
  pose proof (cycL _ _ _ _ _ _ _ UAw k L R) as H.
  rewrite Nat.mul_1_l in H; cbn [app] in H.
  exact H.
Qed.

Lemma phUEnd : forall L R,
  csteps tm_4 3 (StA, (S0 :: L, S1, R))
  = Some (StC, (L, S1, S1 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UEnd). Qed.

Lemma phUVB : forall L R,
  csteps tm_4 1 (StC, (S0 :: L, S1, R))
  = Some (StB, (L, S0, S1 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UVB). Qed.

Lemma phUVA : forall L R,
  csteps tm_4 2 (StD, (L, S1, S0 :: S0 :: R))
  = Some (StA, (L, S0, S1 :: S0 :: R)).
Proof. intros. exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R UVA). Qed.

(** ** The lap *)

Lemma lap_4 : forall p,
  exists n c', csteps tm_4 n (Cc p) = Some c' /\
               lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p.
  destruct (cview p) as [j o] eqn:Ep.
  unfold Cc.
  destruct o as [q|].
  - (* interior carry on both sides *)
    destruct (cview_some_W p j q Ep) as (HWp & HWs).
    destruct (cview_some_G p j q Ep) as (HGp & HGs).
    do 2 eexists. split; [|split].
    + rewrite HWp, HGp.
      eapply csteps_chain. { apply phUWout. }
      eapply csteps_chain. { apply phUWf. }
      rewrite ones_fold_S.
      eapply csteps_chain. { apply phUWb. }
      eapply csteps_chain. { apply phUJ. }
      eapply csteps_chain. { apply phUMs. }
      eapply csteps_chain. { apply phUMi. }
      rewrite rep_tpl, rep1_fold, rep1_fold.
      eapply csteps_chain. { apply phUAw. }
      change (rep [S0] (S (2 * j)) ++ S0 :: S1 :: Wp q)
        with (S0 :: rep [S0] (2 * j) ++ S0 :: S1 :: Wp q).
      apply phUEnd.
    + rewrite HWs, HGs, rep_dbl.
      reflexivity.
    + lia.
  - (* overflow on both sides: p = 2^j - 1 *)
    destruct j as [|j'].
    { exfalso.
      destruct p; simpl in Ep;
        [destruct (cview p); discriminate | discriminate | discriminate]. }
    destruct (cview_none_W p (S j') Ep) as (HWp & HWs).
    destruct (cview_none_G p j' Ep) as (HGp & HGs).
    do 2 eexists. split; [|split].
    + rewrite HWp, <- (app_nil_r (rep [S0; S1] (S j'))), HGp.
      eapply csteps_chain. { apply phUWout. }
      eapply csteps_chain. { apply phUWfE. }
      rewrite ones_fold_S.
      eapply csteps_chain. { apply phUWb. }
      eapply csteps_chain. { apply phUJ. }
      eapply csteps_chain. { apply phUMs. }
      eapply csteps_chain. { apply phUMsE. }
      eapply csteps_chain. { apply phUMo. }
      change (S1 :: S1 :: S1 :: rep [S1; S1; S1] j' ++
                S1 :: S1 :: rep [S0] (S (2 * S j')) ++ [S0; S1])
        with (rep [S1; S1; S1] (S j') ++
                S1 :: S1 :: rep [S0] (S (2 * S j')) ++ [S0; S1]).
      rewrite rep_tpl, rep1_fold, rep1_fold.
      eapply csteps_chain. { apply phUAw. }
      change (rep [S0] (S (2 * S j')) ++ [S0; S1])
        with (S0 :: rep [S0] (2 * S j') ++ [S0; S1]).
      apply phUEnd.
    + rewrite HWs, HGs, rep_dbl.
      reflexivity.
    + lia.
Qed.

(** ** Bootstrap, visits, and the theorem *)

Lemma boot_4 : exists t0, stepn tm_4 t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 18.
  assert (H : match csteps tm_4 18 c0 with
              | Some c => ceqb c (Cc 1)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_4 18 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

Lemma vis_4 : forall p q,
  exists k c, csteps tm_4 k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q.
  unfold Cc.
  destruct q.
  - (* StA: two steps into the junction *)
    destruct (cview p) as [j o] eqn:Ep.
    destruct o as [q0|].
    + destruct (cview_some_W p j q0 Ep) as (HWp & _).
      do 2 eexists. split.
      * rewrite HWp.
        eapply csteps_chain. { apply phUWout. }
        eapply csteps_chain. { apply phUWf. }
        rewrite ones_fold_S.
        eapply csteps_chain. { apply phUWb. }
        apply phUVA.
      * reflexivity.
    + destruct (cview_none_W p j Ep) as (HWp & _).
      do 2 eexists. split.
      * rewrite HWp, <- (app_nil_r (rep [S0; S1] j)).
        eapply csteps_chain. { apply phUWout. }
        eapply csteps_chain. { apply phUWfE. }
        rewrite ones_fold_S.
        eapply csteps_chain. { apply phUWb. }
        apply phUVA.
      * reflexivity.
  - (* StB after 1 step *)
    destruct (Wp_head p) as (w & Hw).
    exists 1. eexists. split.
    + rewrite Hw. apply phUVB.
    + reflexivity.
  - exists 0. eexists. split; reflexivity.
  - (* StD: the W flip's exit state *)
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
Qed.

(** #4 never quasihalts: bbchallenge 1RB0LA_1LC1RC_1RD1LB_1LA0RD. *)
Theorem nqh_1RB0LA_1LC1RC_1RD1LB_1LA0RD : NeverQuasiHaltsSt tm_4.
Proof.
  apply (glue_neverqh tm_4 Cc 1).
  - exact boot_4.
  - intros p _. apply lap_4.
  - intros p q _. apply vis_4.
Qed.

Theorem tm_4_nonhalt : NonHalt tm_4.
Proof. apply never_qh_nonhalt, nqh_1RB0LA_1LC1RC_1RD1LB_1LA0RD. Qed.
