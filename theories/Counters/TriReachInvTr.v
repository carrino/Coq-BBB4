(** * TriGlue liveness restricted to a preserved family invariant.

    The invariant is checked on each concrete leaf map. This lets a
    certificate exclude unreachable parameter values while keeping the
    landed TriGlue transition checker and ValueLap liveness bridge. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import TriGlueTr ValueLapTr LapCertGlueLift TriReachTr.
Import ListNotations.

Lemma tri_leaf_invariant : forall tm fams leaves (I : nat * list nat -> Prop),
 fams_ok tm fams leaves = true ->
 (forall lf, In lf leaves -> forall z,
    I (tl_f lf, map (aeval z) (rsub (tl_reg lf))) ->
    I (tl_g lf, map (aeval z) (tl_tgt lf))) ->
 forall a, Good fams a -> I a -> I (tnxt fams leaves a).
Proof.
 intros tm fams leaves I Hf Hleaf [fi vals] HG HI.
 destruct (walk_leaf tm fams leaves Hf _ HG)
  as (F & lf & l & R & z & HF & Hw & Hlf & Hfi & HR & Hok & Hv & Hlen).
 unfold tnxt. rewrite HF, Hw, Hlf. apply Hleaf.
 - eapply nth_error_In. exact Hlf.
 - cbn [fst snd] in Hfi,Hv. rewrite Hfi,HR,<-Hv. exact HI.
Qed.

Theorem tri_reach_glue_invariant : forall tm fams leaves (I : nat * list nat -> Prop),
 fams_ok tm fams leaves = true -> forall a0,
 Good fams a0 -> I a0 ->
 (forall a, Good fams a -> I a -> I (tnxt fams leaves a)) ->
 (exists t0, stepn tm t0 InitES = Some (lift (tanc fams a0))) ->
 (forall a, Good fams a -> I a -> forall t,
    tri_reaches_fire tm t (tanc fams a)) ->
 NeverQuasiHaltsTr tm.
Proof.
 intros tm fams leaves I Hf a0 H0 HI0 Hstep Hb Hfire.
 assert (Hg : forall n, Good fams (Nat.iter n (tnxt fams leaves) a0)).
 { induction n as [|n IH]; [exact H0|].
   cbn [Nat.iter nat_rect].
   exact (proj2 (step_ok tm fams leaves Hf _ IH)). }
 assert (HI : forall n, I (Nat.iter n (tnxt fams leaves) a0)).
 { induction n as [|n IH]; [exact HI0|].
   cbn [Nat.iter nat_rect]. apply Hstep; [apply Hg|exact IH]. }
 apply (value_lap_neverqhtr tm unit (fun x => x)
   (fun n _ => tanc fams (Nat.iter n (tnxt fams leaves) a0)) tt).
 - exact Hb.
 - intros n []. cbn [Nat.iter nat_rect].
   exact (proj1 (step_ok tm fams leaves Hf _ (Hg n))).
 - intros n [] t.
   destruct (Hfire _ (Hg n) (HI n) t) as (k & e & Hk & Ht).
   destruct (stepn_csteps_at tm k _ e Hk) as (c & Hc & Hl).
   exists k,c. split; [exact Hc|].
   rewrite <- cinstr_lift, Hl. exact Ht.
Qed.
