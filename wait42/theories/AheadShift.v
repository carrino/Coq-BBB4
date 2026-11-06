(** Directions with no return to cells already crossed. *)
From Coq Require Import Arith Lia.
From BBB4 Require Import BBB4_Statement.
From BBBWait42 Require Import Sweep.

Definition forwardblank (d : Dir) (tp : Tape) : Prop :=
  forall n, ahead d tp n = S0.

Lemma forwardblank_move : forall d tp w,
  forwardblank d tp -> forwardblank d (tape_move d w tp).
Proof.
  intros d tp w H n. rewrite ahead_move. apply H.
Qed.

Lemma blank_radius_ahead : forall tp B d k,
  blank_radius tp B -> ahead d tp (S B+k) = S0.
Proof.
  intros tp B d k H.
  destruct (H (B+k) ltac:(lia)) as [Hl Hr].
  destruct d; assumption.
Qed.

Section PhaseScan.
Variable tm : TM.
Variable P : St -> Prop.
Variable d : Dir.
Hypothesis internal_direction : forall s h tr,
  P s -> tm s h = Some tr -> P (t_next tr) -> t_dir tr = d.

Lemma phase_prefix_ahead : forall n c c',
  stepn tm n c = Some c' ->
  (forall j cj, j <= n -> stepn tm j c = Some cj -> P (fst cj)) ->
  forall k, ahead d (snd c') k = ahead d (snd c) (n+k).
Proof.
  induction n as [|n IH]; intros [s tp] c' Hrun HP k.
  - cbn [stepn] in Hrun. injection Hrun as <-. reflexivity.
  - cbn [stepn step] in Hrun.
    destruct (tm s (t_head tp)) as [tr|] eqn:Et; [|discriminate].
    set (c1 := (t_next tr,tape_move (t_dir tr) (t_write tr) tp)).
    assert (H0 : P s).
    { exact (HP 0 (s,tp) ltac:(lia) eq_refl). }
    assert (H1 : P (t_next tr)).
    { apply (HP 1 c1); [lia|]. cbn [stepn step]. rewrite Et. reflexivity. }
    assert (Hd : t_dir tr = d) by (exact (internal_direction s (t_head tp) tr H0 Et H1)).
    assert (HPtail : forall j cj, j <= n -> stepn tm j c1 = Some cj -> P (fst cj)).
    { intros j cj Hj Htail. apply (HP (S j) cj); [lia|].
      cbn [stepn step]. rewrite Et. exact Htail. }
    rewrite (IH c1 c' Hrun HPtail k).
    unfold c1. cbn [snd]. rewrite Hd, ahead_move. reflexivity.
Qed.

Theorem phase_prefix_forwardblank : forall B c c',
  blank_radius (snd c) B ->
  stepn tm (S B) c = Some c' ->
  (forall j cj, j <= S B -> stepn tm j c = Some cj -> P (fst cj)) ->
  forwardblank d (snd c').
Proof.
  intros B c c' Hblank Hrun HP k.
  rewrite (phase_prefix_ahead (S B) c c' Hrun HP k).
  apply blank_radius_ahead; exact Hblank.
Qed.
End PhaseScan.

Print Assumptions phase_prefix_forwardblank.
