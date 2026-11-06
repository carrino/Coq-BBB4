(** Printed only after proof-timing completes its recursive audit. *)
From BBBWait42 Require Import Spec Sweep SweepResiduals InvariantTimedRank ThreeStateCounter SweepGeneralResiduals.
From BBBWait42.ControlRankReplay Require Import All Tight.
Check SweepResiduals.exact_case_count.
Check SweepResiduals.all_completions.
Check ThreeStateCounter.counter_cutoff_window.
Check ThreeStateCounter.counter_window_all_completions.
Check SweepGeneralResiduals.exact_case_count.
Check SweepGeneralResiduals.all_completions.
Check All.exact_case_count.
Check Tight.all_completions.
Print Assumptions SweepResiduals.all_completions.
Print Assumptions ThreeStateCounter.counter_cutoff_window.
Print Assumptions SweepGeneralResiduals.all_completions.
Print Assumptions Tight.all_completions.
