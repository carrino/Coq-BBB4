(** Report the exact claims only after the recursive audit succeeds. *)
From BBBWait Require Import Spec Values Recurrence.

Check BBB_wait12_value : BBBWait_is 1 2 1 0.
Check BBB_wait22_value : BBBWait_is 2 2 6 3.
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
