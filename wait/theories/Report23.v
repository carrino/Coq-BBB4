(** Printed only after the recursive audit. *)
From BBBWait Require Import Spec SpecTr Value23 Decision23 Recurrence RecurrenceTr.

Check BBB_wait23_value : BBBWait_is 2 3 59 32.
Check BBB_wait_tr23_value : BBBWaitTr_is 2 3 67 693.
Check BBB_qh_decide23_value : BBBQHDecide_is 2 3 91.
Check BBB_qh_decide_tr23_value : BBBQHDecideTr_is 2 3 760.
Print BBBQHDecide_is.
Print BBBQHDecideTr_is.
Check wait_decides_quasihalting.
Check wait_tr_decides_quasihalting.
Print Assumptions BBB_wait23_value.
Print Assumptions BBB_wait_tr23_value.
Print Assumptions BBB_qh_decide23_value.
Print Assumptions BBB_qh_decide_tr23_value.
