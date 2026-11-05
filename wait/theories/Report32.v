(** Statements are printed after the full recursive audit, not just a scan. *)
From BBBWait Require Import Spec SpecTr Value32 Recurrence RecurrenceTr Decision32.

Check BBB_wait32_value : BBBWait_is 3 2 55 38.
Check BBB_wait_tr32_value : BBBWaitTr_is 3 2 55 173.
Print BBBWait_is.
Print BBBWaitTr_is.
Print WaitBound.
Print WaitBoundTr.
Check wait_decides_quasihalting.
Check wait_tr_decides_quasihalting.
Print Assumptions BBB_wait32_value.
Print Assumptions BBB_wait_tr32_value.
Check BBB_qh_decide32_value : BBBQHDecide_is 3 2 93.
Check BBB_qh_decide_tr32_value : BBBQHDecideTr_is 3 2 228.
Print Assumptions BBB_qh_decide32_value.
Print Assumptions BBB_qh_decide_tr32_value.
