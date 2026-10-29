(** Boundary and transport guards for the contextual marker checker. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Pipeline MarkerState.
From BBB24.Checkers Require Import NGramHist.
From BBB24Burn9ContextMarker Require Import ContextMarker.
Import ListNotations.
Definition z:hsym := (S0,[]).
Definition m:hsym := (S1,[]).
Definition a:hcconf := (StA,([],z,[])).
Definition b:hcconf := (StB,([],z,[])).
Definition bm:hcconf := (StB,([],m,[])).
Definition bt:hcconf := (StB,([],z,[m])).
Example entry_without_visible_marker_rejected : cm_edge(ms_mark 2%N)a b=false.
Proof. reflexivity. Qed.
Example entry_with_visible_marker_accepted : cm_edge(ms_mark 2%N)a bt=true.
Proof. reflexivity. Qed.
Example carried_unseen_marker_accepted : cm_edge(ms_mark 2%N)b b=true.
Proof. reflexivity. Qed.
Example consumed_last_visible_marker_rejected : cm_edge(ms_mark 2%N)bm b=false.
Proof. reflexivity. Qed.
Example marker_may_disappear_on_return_to_A : cm_edge(ms_mark 2%N)bm a=true.
Proof. reflexivity. Qed.
Example next_head_marker_accepted : cm_edge(ms_mark 2%N)a bm=true.
Proof. reflexivity. Qed.
Example wrong_mask_rejected : cm_edge(ms_mark 4%N)a bt=false.
Proof. reflexivity. Qed.
Example blank_marker_rejected : cm_check(machine_of_codes[5;4;3;11;15;9;6;1])
 1%N 1 0 1 4 4 4096 131072 128=false.
Proof. reflexivity. Qed.
