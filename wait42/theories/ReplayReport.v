(** This report is printed by proof-replay after recursive checking. *)
From BBBWait42 Require Import Spec ReplayPilot ReplayCoverage ResidualReplay ResidualReplayMore.
Check replay_pilot_residual_sizes.
Check replay_pilot_removed_count.
Check replay_pilot_still_unfinished.
Check replay_pilot_conditional_coverage.
Check replay_pilot_coverage_at_width.
Check ResidualReplay.residual_217415_completion.
Check ResidualReplayMore.residual_184475_completion.
Print Assumptions replay_pilot_residual_sizes.
Print Assumptions replay_pilot_conditional_coverage.
Print Assumptions ResidualReplay.residual_217415_completion.
