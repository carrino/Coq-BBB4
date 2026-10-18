(** Kernel assumption audits for the schema and fallback trace projections. *)
From BBB4.CensusTr Require Import HintTagTr.
From BBB4HintTrace Require Import TraceRungsTr TraceWalkTr.

Print Assumptions tr_winner_count.
Print Assumptions tr_winner_codes.
Print Assumptions tr_winner_roundtrips.
Print Assumptions tr_winner_reject_sentinel.
Print Assumptions tr_winner_reject_bad_index.
Print Assumptions trace_anyb_spec.
Print Assumptions trace_qhbtr_spec.
Print Assumptions trace_decider_spec.
Print Assumptions trace_decider_projection.
Print Assumptions trace_upd_projection.
Print Assumptions trace_upds_projection.
Print Assumptions trace_q_suc_projection.
Print Assumptions trace_rounds_projection.
Print Assumptions trace_subtree_projection.
Print Assumptions trace_unit_acc_projection.
Print Assumptions trace_unit_projection.
