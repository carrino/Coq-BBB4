(** Printed only after proof-timing completes its recursive audit. *)
From BBBWait42 Require Import Spec Sweep SweepResiduals InvariantTimedRank ThreeStateCounter.
Check SweepResiduals.exact_case_count.
Check SweepResiduals.all_completions.
Check ThreeStateCounter.counter_cutoff_window.
Check ThreeStateCounter.counter_window_all_completions.
Print Assumptions SweepResiduals.all_completions.
Print Assumptions ThreeStateCounter.counter_cutoff_window.
