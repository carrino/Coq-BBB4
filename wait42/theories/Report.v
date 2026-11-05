(** This report states lower bounds, never an unproved exact value. *)
From Coq Require Import NArith.
From BBB4 Require Import BBB4_Spec.
From BBBWait42 Require Import Spec Recurrence Witness Examples WitnessRecord LowerBounds.

Check record_wait_lower_bound.
Check record_decision_value_lower_bound.
Check instruction_wait_lower_bound.
Check instruction_decision_value_lower_bound.
Print BBBWait42_is.
Print BBBWaitTr42_is.
Print BBBQHDecide42_is.
Print BBBQHDecideTr42_is.
Eval compute in wait_start.
Eval compute in record_wait.
Eval compute in record_horizon.
Eval compute in instruction_wait.
Eval compute in (wait_start + instruction_wait)%N.
Print Assumptions record_wait_lower_bound.
Print Assumptions record_decision_value_lower_bound.
Print Assumptions instruction_wait_lower_bound.
Print Assumptions instruction_decision_value_lower_bound.
