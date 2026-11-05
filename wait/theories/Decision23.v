(** Total observation horizons for two-state ternary machines. *)
From BBBWait Require Export DecisionSpec.
From BBBWait Require Import Value23.

Theorem BBB_qh_decide23_value : BBBQHDecide_is 2 3 91.
Proof. exact (wait_to_decide 2 3 59 32 BBB_wait23_value). Qed.
Theorem BBB_qh_decide_tr23_value : BBBQHDecideTr_is 2 3 760.
Proof. exact (wait_tr_to_decide 2 3 67 693 BBB_wait_tr23_value). Qed.

Print Assumptions BBB_qh_decide23_value.
Print Assumptions BBB_qh_decide_tr23_value.
