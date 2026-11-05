(** The right-moving blank loop 0RA--- witnesses a beep at the one-state
    cutoff itself. Both waiting minima are zero. *)
From Coq Require Import Lia.
From SmallBB Require Import Statement StatementTr Size.

Definition zero_wait_machine : TM := fun q s => match q, s with
  | StA, S0 => Some (mkTrans S0 DR StA)
  | _, _ => None
  end.

Lemma zero_wait_admissible : Admissible 1 2 zero_wait_machine.
Proof.
  split.
  - intros [] [] tr H; cbn in H; try discriminate.
    injection H as <-; unfold output_ok; cbn; lia.
  - intros [] [] H; cbn in H; try lia; reflexivity.
Qed.

Lemma zero_wait_instruction_beep : FiresAt zero_wait_machine (StA,S0) 1.
Proof. eexists; split; reflexivity. Qed.

Lemma zero_wait_state_beep : VisitsAt zero_wait_machine StA 1.
Proof. apply (fires_visits zero_wait_machine StA S0 1); exact zero_wait_instruction_beep. Qed.
