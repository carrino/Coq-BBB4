(** Total observation horizons, as distinct from extra waiting times.
    This is the minimal horizon at or after the known BBB cutoff for the
    uniform per-target observation rule. It is not a lower bound on the
    runtime of every possible algorithm deciding quasihalting. *)
From Coq Require Import Arith Lia.
Require Import SmallBB.Spec.
From BBBWait Require Import Spec SpecTr.

Definition BBBQHDecide_is ns ms D :=
  exists B w, BBBWait_is ns ms B w /\ D = B+w.
Definition BBBQHDecideTr_is ns ms D :=
  exists B w, BBBWaitTr_is ns ms B w /\ D = B+w.

Theorem wait_to_decide : forall ns ms B w,
  BBBWait_is ns ms B w -> BBBQHDecide_is ns ms (B+w).
Proof. intros ns ms B w H; exists B,w; auto. Qed.

Theorem wait_tr_to_decide : forall ns ms B w,
  BBBWaitTr_is ns ms B w -> BBBQHDecideTr_is ns ms (B+w).
Proof. intros ns ms B w H; exists B,w; auto. Qed.

Theorem BBBQHDecide_unique : forall ns ms D D',
  BBBQHDecide_is ns ms D -> BBBQHDecide_is ns ms D' -> D=D'.
Proof.
  intros ns ms D D' (B & w & H & HD) (B' & w' & H' & HD').
  assert (HB : B=B').
  { eapply SmallBB.Spec.BBBSt_unique; [exact (proj1 H)|exact (proj1 H')]. }
  subst B'.
  assert (Hw : w=w') by (eapply BBBWait_unique; eauto).
  lia.
Qed.

Theorem BBBQHDecideTr_unique : forall ns ms D D',
  BBBQHDecideTr_is ns ms D -> BBBQHDecideTr_is ns ms D' -> D=D'.
Proof.
  intros ns ms D D' (B & w & H & HD) (B' & w' & H' & HD').
  assert (HB : B=B').
  { eapply SmallBB.Spec.BBBTr_unique; [exact (proj1 H)|exact (proj1 H')]. }
  subst B'.
  assert (Hw : w=w') by (eapply BBBWaitTr_unique; eauto).
  lia.
Qed.

Theorem BBBQHDecide_minimal : forall ns ms D,
  BBBQHDecide_is ns ms D -> forall B D',
  SmallBB.Spec.BBBSt_is ns ms B -> B <= D' ->
  WaitBound ns ms B (D'-B) -> D <= D'.
Proof.
  intros ns ms D (B & w & H & HD) B' D' Hbbb HBD Hwait.
  assert (HB : B=B').
  { eapply SmallBB.Spec.BBBSt_unique; [exact (proj1 H)|exact Hbbb]. }
  subst B'.
  destruct H as [_ [_ Hminimal]].
  specialize (Hminimal (D'-B) Hwait); lia.
Qed.

Theorem BBBQHDecideTr_minimal : forall ns ms D,
  BBBQHDecideTr_is ns ms D -> forall B D',
  SmallBB.Spec.BBBTr_is ns ms B -> B <= D' ->
  WaitBoundTr ns ms B (D'-B) -> D <= D'.
Proof.
  intros ns ms D (B & w & H & HD) B' D' Hbbb HBD Hwait.
  assert (HB : B=B').
  { eapply SmallBB.Spec.BBBTr_unique; [exact (proj1 H)|exact Hbbb]. }
  subst B'.
  destruct H as [_ [_ Hminimal]].
  specialize (Hminimal (D'-B) Hwait); lia.
Qed.

