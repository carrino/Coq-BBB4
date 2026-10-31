(** All B contexts require markers. Selected A symbols retain them;
    unselected A contexts may erase and subsequently recreate them. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement CTape MarkerState.
From BBB24.Checkers Require Import NGramHist.
From BBB24Burn11ConditionalMarker Require Import ConditionalMarker.
Import ListNotations.
Definition mark := ms_mark 2%N.
Definition need := ms_mark 8%N.
Definition Aempty : hcconf := (StA,([],hblank,[])).
Definition Bempty : hcconf := (StB,([],hblank,[])).
Definition Acarry : hcconf := (StA,([],(S3,[]),[])).
Example unselected_A_needs_no_initial_marker : sm_initial mark need c0=true.
Proof. reflexivity. Qed.
Example selected_A_needs_initial_marker : sm_initial mark need(StA,([],S3,[]))=false.
Proof. reflexivity. Qed.
Example B_always_needs_marker : sm_need (ms_mark 0%N)(StB,([],S0,[]))=true.
Proof. reflexivity. Qed.
Example unselected_A_cannot_supply_marker : sm_edge mark need Aempty Bempty=false.
Proof. reflexivity. Qed.
Example selected_unmarked_A_carries_marker : sm_edge mark need Acarry Bempty=true.
Proof. reflexivity. Qed.
Example unselected_successor_may_drop_marker : sm_edge mark need Acarry Aempty=true.
Proof. reflexivity. Qed.
Example required_successor_needs_evidence : sm_edge mark need Aempty Acarry=false.
Proof. reflexivity. Qed.
