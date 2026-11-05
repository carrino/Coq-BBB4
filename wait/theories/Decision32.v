(** Total observation horizons for three-state binary machines. *)
From BBBWait Require Export DecisionSpec.
From BBBWait Require Import Value32.

Theorem BBB_qh_decide32_value : BBBQHDecide_is 3 2 93.
Proof. exact (wait_to_decide 3 2 55 38 BBB_wait32_value). Qed.
Theorem BBB_qh_decide_tr32_value : BBBQHDecideTr_is 3 2 228.
Proof. exact (wait_tr_to_decide 3 2 55 173 BBB_wait_tr32_value). Qed.

Print Assumptions BBB_qh_decide32_value.
Print Assumptions BBB_qh_decide_tr32_value.
