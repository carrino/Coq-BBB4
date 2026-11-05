(** Total observation horizons for one- and two-state binary machines. *)
From BBBWait Require Export DecisionSpec WitnessZero.
From BBBWait Require Import Values ValuesTr.

Theorem BBB_qh_decide12_value : BBBQHDecide_is 1 2 1.
Proof. exact (wait_to_decide 1 2 1 0 BBB_wait12_value). Qed.
Theorem BBB_qh_decide22_value : BBBQHDecide_is 2 2 9.
Proof. exact (wait_to_decide 2 2 6 3 BBB_wait22_value). Qed.
Theorem BBB_qh_decide_tr12_value : BBBQHDecideTr_is 1 2 1.
Proof. exact (wait_tr_to_decide 1 2 1 0 BBB_wait12_tr_value). Qed.
Theorem BBB_qh_decide_tr22_value : BBBQHDecideTr_is 2 2 17.
Proof. exact (wait_tr_to_decide 2 2 8 9 BBB_wait22_tr_value). Qed.

Print Assumptions BBB_qh_decide12_value.
Print Assumptions BBB_qh_decide22_value.
Print Assumptions BBB_qh_decide_tr12_value.
Print Assumptions BBB_qh_decide_tr22_value.
