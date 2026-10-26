(** Exact state and instruction values for two states and three symbols. *)
From SmallBB Require Import Spec Value23Conditional Remaining23Solved.

Theorem BBB23_value : BBB23_statement.
Proof. exact (BBB23_value_if_remaining remaining23_all). Qed.

Print Assumptions BBB23_value.
