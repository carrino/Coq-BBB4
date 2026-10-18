(** Generated-data wiring regression for the full advisory hint corpus.
    The established Unit10 entry must be present and its actual checker must
    succeed. This is separate from the map-independent failure tests so that
    partial pilot tables for other units can still exercise the core suite. *)
From BBB4 Require Import BBB4_Statement.

(* key=2986866472; tag=0; machine=0RB1RA_1RC1LC_1LD0RC_0LA1RC *)
Definition actual_unit10_hint_machine : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StA)
  | StB, S0 => Some (mkTrans S1 DR StC)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S0 DL StA)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

From Coq Require Import PArith.
From BBB4.CensusTr Require Import HintTagTr HintedTr RunTr_Hinted RunTr_Compute.

Example actual_unit10_hint_key :
  tr_hint_lookup hint_map_tr actual_unit10_hint_machine = Some (WNGram 0).
Proof. vm_compute. reflexivity. Qed.

Example actual_unit10_hint_accepted :
  try_hint_tr B_search_tr 200000 512 ng_rungs_tr rank_rungs_tr
    qhb_rungs_tr qhb_lex_rungs_tr rw_qhb_rungs_tr rw_rungs_tr
    rw_fuel_tr rw_cut_tr hint_map_tr actual_unit10_hint_machine =
    Some HintNeverTr.
Proof. native_compute. reflexivity. Qed.

Print Assumptions actual_unit10_hint_key.
Print Assumptions actual_unit10_hint_accepted.
