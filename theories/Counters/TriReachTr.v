(** * Closing TriGlue families with a separate eventual-fire argument.

    The landed family checker still verifies every machine step.  Clients
    may supply a non-affine liveness proof without changing its tape or
    dispatch language. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import TriGlueTr ValueLapTr LapCertGlueLift.
Import ListNotations.

Definition tri_reaches_fire (tm : TM) (t : Instr) (c : cconf) : Prop :=
  exists k e, stepn tm k (lift c) = Some e /\ instr_of e = t.

Lemma tri_fire_back : forall tm t c d n e,
  csteps tm n c = Some e -> lift e = lift d ->
  tri_reaches_fire tm t d -> tri_reaches_fire tm t c.
Proof.
  intros tm t c d n e H He (k & f & Hk & Ht).
  exists (n+k), f. split; [|exact Ht].
  rewrite stepn_add, (csteps_lift _ _ _ _ H), He. exact Hk.
Qed.

Lemma tri_leaf_back : forall tm fams f l g,
  leaf_ok tm fams f l = true -> nth_error fams (tl_g l) = Some g ->
  forall z t,
  tri_reaches_fire tm t (tinst g (map (aeval z) (tl_tgt l))) ->
  tri_reaches_fire tm t (tinst f (map (aeval z) (rsub (tl_reg l)))).
Proof.
  intros tm fams f l g H Hg z t Ht.
  destruct (leaf_lap tm fams f l g H Hg z) as (n & c & Hn & Hl & _).
  eapply tri_fire_back; eauto.
Qed.

Lemma tri_leaf_now : forall tm fams f l,
  leaf_ok tm fams f l = true -> forall t,
  In t (leaf_fired tm l) -> forall z,
  tri_reaches_fire tm t (tinst f (map (aeval z) (rsub (tl_reg l)))).
Proof.
  intros tm fams f l H t Ht z.
  destruct (leaf_fires tm fams f l t H Ht z) as (k & c & Hk & Hc).
  exists k, (lift c). split; [apply csteps_lift;exact Hk|].
  rewrite cinstr_lift. exact Hc.
Qed.

Theorem tri_reach_glue : forall tm fams leaves,
  fams_ok tm fams leaves = true -> forall a0,
  Good fams a0 ->
  (exists t0, stepn tm t0 InitES = Some (lift (tanc fams a0))) ->
  (forall a, Good fams a -> forall t,
     tri_reaches_fire tm t (tanc fams a)) ->
  NeverQuasiHaltsTr tm.
Proof.
  intros tm fams leaves Hf a0 H0 Hb Hfire.
  assert (Hg : forall n, Good fams (Nat.iter n (tnxt fams leaves) a0)).
  { induction n as [|n IH]; [exact H0|].
    cbn [Nat.iter nat_rect].
    exact (proj2 (step_ok tm fams leaves Hf _ IH)). }
  apply (value_lap_neverqhtr tm unit (fun x => x)
    (fun n _ => tanc fams (Nat.iter n (tnxt fams leaves) a0)) tt).
  - exact Hb.
  - intros n []. cbn [Nat.iter nat_rect].
    exact (proj1 (step_ok tm fams leaves Hf _ (Hg n))).
  - intros n [] t.
    destruct (Hfire _ (Hg n) t) as (k & e & Hk & Ht).
    destruct (stepn_csteps_at tm k _ e Hk) as (c & Hc & Hl).
    exists k,c. split; [exact Hc|].
    rewrite <- cinstr_lift, Hl. exact Ht.
Qed.
