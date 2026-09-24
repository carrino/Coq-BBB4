(** * CloseoutFinalTr: the transition-level target, modulo the residue.

      [bbbt4_target : forall tm, QHBoundTr B_tr tm \/ Deferred D_remaining_tr tm]

    -- every (4,2) machine has every quiet instruction quiet before
    configuration index 32,779,478, or is in the orbit of one of the
    rows no closeout batch has boarded yet (CloseoutTr/RemainingTr.v).
    When that list is empty the second disjunct is uninhabited
    ([Deferred [] tm] has no base case) and the transition-level bound
    is unconditional.

    Chains [census_tr] (the 96-unit walk, CensusTr/Compute/, box only)
    with [closeout_tr_partial] (CloseoutTr.v, built by CI).  Compile it
    after `make census-tr-walk`:  `make closeout-tr-final`.  It is
    exempt from _CoqProject for the same reason the walk units are. *)
From BBB4 Require Import BBB4_Statement BBBT4_Statement.
From BBB4.Census Require Import TNF_QH.
From BBB4.CensusTr Require Import TNF_QHTr RunTr.
From BBB4.CensusTr.Compute Require Import Census_TheoremTr.
From BBB4.CloseoutTr Require Import CloseoutKitTr CloseoutTr.

Theorem bbbt4_target : forall tm,
  QHBoundTr B_tr tm \/ Deferred D_remaining_tr tm.
Proof.
  intro tm.
  destruct (census_tr tm) as [H | H]; [left; exact H |].
  exact (closeout_tr_partial tm H).
Qed.
