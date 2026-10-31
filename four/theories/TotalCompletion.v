(** Fully defined tables suffice for the non-halting part of BBB.
    Halting tables remain a separate obligation for the unrestricted bound. *)
From Coq Require Import NArith Lia Setoid.
From BBB24 Require Import Statement StatementTr Spec Bounds Census.

Definition Total (tm : TM) := forall q s, exists tr, tm q s = Some tr.
Definition totalize (tm : TM) : TM := fun q s =>
  match tm q s with
  | Some tr => Some tr
  | None => Some (mkTrans S0 DL StA)
  end.

Lemma totalize_total : forall tm, Total (totalize tm).
Proof. intros tm q s. unfold totalize. destruct (tm q s); eexists; reflexivity. Qed.

Lemma totalize_extends : forall tm, TM_le tm (totalize tm).
Proof.
  intros tm q s. unfold totalize. destruct (tm q s) eqn:E;
    [right | left]; reflexivity.
Qed.

Theorem totalize_run : forall tm, NonHalt tm -> forall n,
  stepn (totalize tm) n InitES = stepn tm n InitES.
Proof. intros tm Hnh. apply extend_run; [exact Hnh | apply totalize_extends]. Qed.

Lemma same_run_bounds : forall tm tm',
  (forall n, stepn tm n InitES = stepn tm' n InitES) ->
  forall bs bi, Bounds bs bi tm <-> Bounds bs bi tm'.
Proof.
  intros tm tm' H bs bi.
  unfold Bounds, QHBound, QHBoundTr, QuietAfter, QuietAfterTr, VisitsAt, FiresAt.
  setoid_rewrite H. reflexivity.
Qed.

Theorem totalize_scores : forall tm, NonHalt tm -> forall B,
  (AttainsSt (totalize tm) B <-> AttainsSt tm B) /\
  (AttainsTr (totalize tm) B <-> AttainsTr tm B).
Proof.
  intros tm Hnh B. unfold AttainsSt, AttainsTr, QuietAfter, QuietAfterTr, VisitsAt, FiresAt.
  setoid_rewrite (totalize_run tm Hnh). split; reflexivity.
Qed.

Theorem nonhalting_bounds_from_total : forall bs bi,
  (forall tm, Total tm -> Bounds bs bi tm) ->
  forall tm, NonHalt tm -> Bounds bs bi tm.
Proof.
  intros bs bi H tm Hnh.
  apply (proj1 (same_run_bounds (totalize tm) tm (totalize_run tm Hnh) bs bi)).
  apply H, totalize_total.
Qed.

(** This split is constructive: inspect the run at the proposed halting bound.
    No excluded middle, halting oracle, or assumed busy-beaver value is used. *)
Theorem global_bounds_from_total_and_halts : forall bs bi k,
  k <= N.to_nat bs -> k <= N.to_nat bi ->
  (forall tm, Total tm -> Bounds bs bi tm) ->
  (forall tm, Halts tm -> stepn tm k InitES = None) ->
  forall tm, Bounds bs bi tm.
Proof.
  intros bs bi k Hs Hi Htotal Hhalt tm.
  destruct (stepn tm k InitES) as [c|] eqn:E.
  - apply (nonhalting_bounds_from_total bs bi Htotal tm).
    intros n Hn. pose proof (Hhalt tm (ex_intro _ n Hn)) as H. congruence.
  - eapply halt_bounds; eauto.
Qed.

Print Assumptions totalize_scores.
Print Assumptions global_bounds_from_total_and_halts.
