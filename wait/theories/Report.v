(** Report the exact claims only after the recursive audit succeeds. *)
From BBBWait Require Import Spec SpecTr Values ValuesTr Recurrence RecurrenceTr Decision.

Check BBB_wait12_value : BBBWait_is 1 2 1 0.
Check BBB_wait22_value : BBBWait_is 2 2 6 3.
Check BBB_wait12_tr_value : BBBWaitTr_is 1 2 1 0.
Check BBB_wait22_tr_value : BBBWaitTr_is 2 2 8 9.
Print BBBWaitTr_is.
Print WaitBoundTr.
Print BBBWait_is.
Print WaitBound.
Print FutureBeep.
Print BeepWindow.
Check wait_silence_decision.
Check late_beep_not_eventually_quiet.
Check wait_decides_quasihalting.
Print Assumptions BBB_wait12_value.
Print Assumptions BBB_wait22_value.
Print Assumptions wait_decides_quasihalting.
Check wait_tr_decides_quasihalting.
Print Assumptions BBB_wait12_tr_value.
Print Assumptions BBB_wait22_tr_value.
Print Assumptions wait_tr_decides_quasihalting.
Check BBB_qh_decide12_value : BBBQHDecide_is 1 2 1.
Check BBB_qh_decide22_value : BBBQHDecide_is 2 2 9.
Check BBB_qh_decide_tr12_value : BBBQHDecideTr_is 1 2 1.
Check BBB_qh_decide_tr22_value : BBBQHDecideTr_is 2 2 17.
Print BBBQHDecide_is.
Print BBBQHDecideTr_is.
