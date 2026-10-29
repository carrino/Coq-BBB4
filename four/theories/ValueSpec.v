(** The state-based equality claim for unrestricted two-state, four-symbol
    machines. This file states the claim; it does not prove the upper bound.
    The machine model and score convention are in Statement.v and Spec.v. *)
From BBB24 Require Import Statement Spec.

Definition BBB24_state_is (B : nat) : Prop :=
  BBB24_state_lower_bound B /\ (forall tm : TM, QHBound B tm).

Definition BBB24_state_statement : Prop := BBB24_state_is score.
