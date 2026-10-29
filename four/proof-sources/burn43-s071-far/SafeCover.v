(** Positive-cost, safe macro segments cover every actual microstep.
    Boundary tapes may differ by implicit blank padding. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement CTape.
From BBB24Burn43S071FAR Require Import Programs.
From BBB24Burn43S071FAR Require Import BlockMicro.
Import ListNotations.

Lemma c53_all_blank_complete : forall l,
  (forall n, nthb l n = S0) -> all_blank l = true.
Proof.
  induction l as [|h t IH]; intro H; [reflexivity|].
  assert (Eh : h = S0) by exact (H 0).
  subst h; cbn [all_blank sym_eqb].
  apply IH; intro n; exact (H (S n)).
Qed.

Lemma c53_all_blank_ext : forall a b,
  (forall n, nthb a n = nthb b n) -> all_blank a = all_blank b.
Proof.
  intros a b H.
  assert (AB : all_blank a = true -> all_blank b = true).
  { intro E; apply c53_all_blank_complete; intro n.
    rewrite <- H; now apply all_blank_nthb. }
  assert (BA : all_blank b = true -> all_blank a = true).
  { intro E; apply c53_all_blank_complete; intro n.
    rewrite H; now apply all_blank_nthb. }
  destruct (all_blank a), (all_blank b); auto; specialize (AB eq_refl) || specialize (BA eq_refl); discriminate.
Qed.

Lemma c53_safe_lift : forall c d,
  lift c = lift d -> c52_safe c -> c52_safe d.
Proof.
  intros [q [[l h] r]] [q' [[l' h'] r']] E H.
  pose proof (f_equal (@fst St Tape) E) as Eq.
  pose proof (f_equal (fun e => t_head (snd e)) E) as Eh.
  pose proof (f_equal (fun e => t_right (snd e)) E) as Er.
  change (q = q') in Eq; change (h = h') in Eh.
  change (lift_side r = lift_side r') in Er.
  subst q' h'; destruct q, h; cbn [c52_safe] in *; auto.
  rewrite <- (c53_all_blank_ext r r'); [exact H|].
  intro n; exact (f_equal (fun f => f n) Er).
Qed.

Lemma c53_front_empty_pad : forall q l,
  lift (s71_front q l []) = lift (s71_front q l [S0;S0]).
Proof.
  intros.
  change ((q,mkTape (lift_side l) S0 (lift_side [])) =
          (q,mkTape (lift_side l) S0 (lift_side [S0]))).
  rewrite (lpad_eqb_lift [] [S0] eq_refl); reflexivity.
Qed.

Lemma c53_back_empty_pad : forall q r,
  lift (s71_back q [] r) = lift (s71_back q [S0;S0] r).
Proof.
  intros.
  change ((q,mkTape (lift_side []) S0 (lift_side r)) =
          (q,mkTape (lift_side [S0]) S0 (lift_side r))).
  rewrite (lpad_eqb_lift [] [S0] eq_refl); reflexivity.
Qed.

Lemma c53_initial_padded : lift (s71_front StA [S0;S0] []) = InitES.
Proof.
  change ((StA,mkTape (lift_side [S0;S0]) S0 (lift_side [])) = InitES).
  rewrite (lpad_eqb_lift [S0;S0] [] eq_refl), lift_side_nil; reflexivity.
Qed.

Definition c53_safe_before (tm : TM) (k : nat) (c : cconf) : Prop :=
  forall n, n < k -> forall d,
    csteps tm n c = Some d -> c52_safe d.

Definition c53_progress (tm : TM) (Good : cconf -> Prop) : Prop :=
  forall c, Good c -> exists k ci ce cn,
    0 < k /\ lift ci = lift c /\ csteps tm k ci = Some ce /\
    lift ce = lift cn /\ Good cn /\ c53_safe_before tm k ci.

Theorem c53_cover : forall tm Good,
  c53_progress tm Good -> forall n c d,
  Good c -> stepn tm n (lift c) = Some (lift d) -> c52_safe d.
Proof.
  intros tm Good P n; induction n using lt_wf_ind; intros c d G E.
  destruct (P c G) as (k & ci & ce & cn & Hk & Ei & Ek & En & Gn & Safe).
  rewrite <- Ei in E.
  destruct (lt_dec n k) as [Hnk|Hnk].
  - destruct (csteps_prefix tm n k ci ce (Nat.lt_le_incl _ _ Hnk) Ek)
      as (mid & Em & _).
    pose proof (csteps_lift tm n ci mid Em) as El.
    rewrite El in E.
    assert (Eeq : lift mid = lift d) by congruence.
    eapply c53_safe_lift; [exact Eeq|].
    eapply Safe; eauto.
  - assert (Eq : n = k + (n-k)) by lia.
    rewrite Eq, stepn_add, (csteps_lift tm k ci ce Ek), En in E.
    eapply (H (n-k)); [lia|exact Gn|exact E].
Qed.

Theorem c53_blank_run_safe : forall tm Good entry,
  c53_progress tm Good -> Good entry -> lift entry = InitES ->
  forall n d, csteps tm n c0 = Some d -> c52_safe d.
Proof.
  intros tm Good entry P G Ei n d E.
  eapply (c53_cover tm Good P n entry d); [exact G|].
  rewrite Ei, <- lift_c0; now apply csteps_lift.
Qed.

Theorem c53_blank_no_spinout : forall tm Good entry,
  c53_progress tm Good -> Good entry -> lift entry = InitES ->
  forall n l, csteps tm n c0 <> Some (StB,(l,S0,[])).
Proof.
  intros tm Good entry P G Ei n l E.
  pose proof (c53_blank_run_safe tm Good entry P G Ei n _ E) as H.
  cbn [c52_safe all_blank] in H; discriminate.
Qed.

Print Assumptions c53_safe_lift.
Print Assumptions c53_cover.
Print Assumptions c53_blank_no_spinout.
