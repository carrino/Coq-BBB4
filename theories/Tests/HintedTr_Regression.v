(** Failure and fallback regressions for instruction-census advisory hints.
    These tests construct their own maps and do not depend on generated rows.
    Every checked branch uses the actual configured checker and actual TM. *)
From Coq Require Import Arith Bool List PArith.
From Coq Require Import FSets.FMapPositive.
From BBB4 Require Import BBB4_Statement BBBT4_Statement.
From BBB4.Census Require Import TNF_QH Decide.
From BBB4.CensusTr Require Import HintTagTr HintedTr RunTr_Compute.
Import ListNotations.

Definition hint_test_halt : TM := fun _ _ => None.
Definition hint_test_key := tm_enc hint_test_halt.

Definition hint_test_attempt :=
  try_hint_winner_tr B_search_tr 200000 512 ng_rungs_tr rank_rungs_tr
    qhb_rungs_tr qhb_lex_rungs_tr rw_qhb_rungs_tr rw_rungs_tr
    rw_fuel_tr rw_cut_tr.

Definition hint_test_apply (hm : TrHintMap) : QHDecider :=
  advisory_decider_tr B_search_tr 200000 512 ng_rungs_tr rank_rungs_tr
    qhb_rungs_tr qhb_lex_rungs_tr rw_qhb_rungs_tr rw_rungs_tr
    rw_fuel_tr rw_cut_tr (fun _ => true) decider_tr_fallback hm.

(** Logical empty fallback for EVERY machine, independently of its verdict. *)
Example hint_empty_fallback : forall tm,
  hint_test_apply (PositiveMap.empty _) tm = decider_tr_fallback tm.
Proof. intros tm. unfold hint_test_apply. apply advisory_decider_tr_empty. Qed.

(** An existing map with a DIFFERENT key must not dispatch a checker. *)
Definition hint_test_other_key : TrHintMap :=
  PositiveMap.add (Pos.succ hint_test_key) (WNGram 0) (PositiveMap.empty _).

Example hint_nonempty_map_miss :
  tr_hint_lookup hint_test_other_key hint_test_halt = None.
Proof. vm_compute. reflexivity. Qed.

Example hint_miss_returns_real_fallback :
  hint_test_apply hint_test_other_key hint_test_halt = R_Halt StA S0.
Proof. vm_compute. reflexivity. Qed.

(** Unknown wire tags cannot alias an adjacent family or be accepted. *)
Example hint_invalid_wire_is_miss :
  tr_hint_lookup (tr_hmap_of_codes [(hint_test_key, 38); (hint_test_key, 999)])
    hint_test_halt = None.
Proof. vm_compute. reflexivity. Qed.

Example hint_invalid_wire_fallback :
  hint_test_apply (tr_hmap_of_codes [(hint_test_key, 38)]) hint_test_halt =
  R_Halt StA S0.
Proof. vm_compute. reflexivity. Qed.

(** One out-of-range index for every family, through the typed map API. *)
Definition hint_test_bad_indices : list TrWinner :=
  [WNGram 4; WRank 4; WQHPlain TrShort 9; WQHLex TrFull 3;
   WQHRW TrShort 1; WRW 4].

Example hint_bad_indices_rejected :
  map (hint_test_attempt hint_test_halt) hint_test_bad_indices =
  repeat (@None TrHintDecision) 6.
Proof. vm_compute. reflexivity. Qed.

Example hint_bad_index_real_fallback :
  hint_test_apply (tr_hmap_of [(hint_test_key, WNGram 99)]) hint_test_halt =
  R_Halt StA S0.
Proof. native_compute. reflexivity. Qed.

(** All six families, both QH horizons. The rank hint selects t=64,
    ensuring an immediate halted csteps path; RW uses its real t=0 rung.
    Valid tags for a HALTING machine must fail their actual checkers. *)
Definition hint_test_failed_tags : list TrWinner :=
  [WNGram 0; WRank 1;
   WQHPlain TrShort 0; WQHPlain TrFull 0;
   WQHLex TrShort 0; WQHLex TrFull 0;
   WQHRW TrShort 0; WQHRW TrFull 0; WRW 0].

Example hint_valid_tags_fail_on_halting_machine :
  map (hint_test_attempt hint_test_halt) hint_test_failed_tags =
  repeat (@None TrHintDecision) 9.
Proof. vm_compute. reflexivity. Qed.

Example hint_failed_checks_return_real_fallback :
  map (fun tag => hint_test_apply (tr_hmap_of [(hint_test_key, tag)])
    hint_test_halt) hint_test_failed_tags = repeat (R_Halt StA S0) 9.
Proof. native_compute. reflexivity. Qed.

Print Assumptions hint_empty_fallback.
Print Assumptions hint_nonempty_map_miss.
Print Assumptions hint_invalid_wire_is_miss.
Print Assumptions hint_bad_indices_rejected.
Print Assumptions hint_valid_tags_fail_on_halting_machine.
Print Assumptions hint_failed_checks_return_real_fallback.
