(** Printed only after proof-timing completes its recursive audit. *)
From BBBWait42 Require Import Spec Sweep SweepResiduals InvariantTimedRank ThreeStateCounter SweepGeneralResiduals.
From BBBWait42.ControlRankReplay Require Import All Tight.
From BBBWait42 Require Import PhaseRankTests.
From BBBWait42.PhaseRankReplay Require Import Union.
Check SweepResiduals.exact_case_count.
Check SweepResiduals.all_completions.
Check ThreeStateCounter.counter_cutoff_window.
Check ThreeStateCounter.counter_window_all_completions.
Check SweepGeneralResiduals.exact_case_count.
Check SweepGeneralResiduals.all_completions.
Check ControlRankReplay.All.exact_case_count.
Check ControlRankReplay.Tight.all_completions.
Check PhaseRankReplay.Union.exact_case_count.
Check PhaseRankReplay.Union.all_completions.
Check PhaseRankTests.scanner_completion.
Print Assumptions SweepResiduals.all_completions.
Print Assumptions ThreeStateCounter.counter_cutoff_window.
Print Assumptions SweepGeneralResiduals.all_completions.
Print Assumptions ControlRankReplay.Tight.all_completions.
Print Assumptions PhaseRankReplay.Union.all_completions.
Print Assumptions PhaseRankTests.scanner_completion.
