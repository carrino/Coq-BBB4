(** Configure advisory dispatch without importing RunTr_Compute.
    The computation entry point can instantiate this module without a cycle.
    Misses and failed checks call the unchanged fallback once. *)
From Coq Require Import Arith List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement.
From BBB4.Census Require Import TNF_QH.
From BBB4.CensusTr Require Import TNF_QHTr HintedTr HintsTr_Data.

(** Native evaluation memoizes this application as one shared lazy constant.
    Each worker builds its own map when the constant is first forced. *)
Definition hint_map_tr : TrHintMap := tr_hmap_of hint_rows_tr.

Section ConfigureHintTr.
Variables B ng_fuel ng_rounds : nat.
Variables ng_rungs rank_rungs qhb_rungs qhb_lex_rungs : list (nat * nat).
Variables rw_qhb_rungs rw_rungs : list (nat * nat * nat).
Variables rw_fuel rw_cut : nat.

Definition with_tr_hints (fallback : QHDecider) : QHDecider :=
  advisory_decider_tr B ng_fuel ng_rounds ng_rungs rank_rungs
    qhb_rungs qhb_lex_rungs rw_qhb_rungs rw_rungs rw_fuel rw_cut
    (fun _ => true) fallback hint_map_tr.

Theorem with_tr_hints_WF_larger : forall bound D fallback,
  B <= bound -> QHDeciderTr_WF bound D fallback ->
  QHDeciderTr_WF bound D (with_tr_hints fallback).
Proof.
  intros bound D fallback HB Hfallback. unfold with_tr_hints.
  apply advisory_decider_tr_WF_larger; assumption.
Qed.

(** Only the empty-data case has this equality. Do not generalize it to
    arbitrary generated rows: the soundness theorem is the integration API. *)
Lemma with_tr_hints_empty : forall fallback tm,
  hint_rows_tr = nil -> with_tr_hints fallback tm = fallback tm.
Proof.
  intros fallback tm Hempty. unfold with_tr_hints, hint_map_tr.
  rewrite Hempty. cbn [tr_hmap_of]. apply advisory_decider_tr_empty.
Qed.
End ConfigureHintTr.
