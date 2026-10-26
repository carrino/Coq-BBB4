(** All seven symmetry representatives have unconditional instruction bounds.
    The six-case assembly isolates the final binary counter proof. *)
From Coq Require Import List.
From SmallBB Require Import Bounds Remaining23Symmetry RepA RepB
  Binary23Counter RepA_Binary Symbolic23Case.

Theorem remaining23_six :
  QHBoundTr 67 remaining23_rep1 ->
  Forall (QHBoundTr 67) remaining23_representatives.
Proof.
  intro H1. unfold remaining23_representatives.
  constructor; [exact (proj2 (proj2 repA0_bounds))|].
  constructor; [exact H1|].
  constructor; [exact binary23_rep2_bound|].
  constructor; [exact repb_instruction_bound0|].
  constructor; [exact repb_instruction_bound1|].
  constructor; [exact (proj2 (proj2 symbolic23_bound))|].
  constructor; [exact (proj2 (proj2 repA6_bounds))|].
  constructor.
Qed.

Theorem remaining23_all :
  Forall (QHBoundTr 67) remaining23_representatives.
Proof. exact (remaining23_six binary23_rep1_bound). Qed.

Print Assumptions remaining23_all.
