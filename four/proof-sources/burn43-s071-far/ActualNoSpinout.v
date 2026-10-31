(** Actual S071 state closeout, using the finite checked FAR certificate. *)
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn43S071FAR Require Import Programs Progress.
From BBB24Burn43S071FAR Require Import NoSpinout.
From BBB24Burn43S071FAR Require Import Data ActualClosed.
From BBB24Burn43S071FAR Require Import MacroBridge.

Theorem c54_s071_no_spinout:c49_no_spinout.
Proof. exact(@c54_no_spinout certificate actual_closed). Qed.

Theorem c54_s071_state_zero:QHBound 0 s71_tm.
Proof. apply c49_zero_from_no_spinout;exact c54_s071_no_spinout. Qed.

Print Assumptions c54_s071_no_spinout.
Print Assumptions c54_s071_state_zero.
