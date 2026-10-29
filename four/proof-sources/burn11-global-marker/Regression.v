(** Retaining a marker through A needs an actual initial marker in A;
    unmarked heads carry distant markers, while marked heads require evidence
    that the successor still contains one. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement CTape MarkerState.
From BBB24.Checkers Require Import NGramHist.
From BBB24Burn9ContextMarker Require Import ContextMarker.
From BBB24Burn11GlobalMarker Require Import GlobalMarker.
Import ListNotations.
Definition mark := ms_mark 2%N.
Definition Aempty : hcconf := (StA,([],hblank,[])).
Definition Bempty : hcconf := (StB,([],hblank,[])).
Definition Amarked : hcconf := (StA,([],(S1,[]),[])).
Example A_requires_initial_marker : gm_initial mark c0=false.
Proof. reflexivity. Qed.
Example ordinary_A_invariant_is_weaker : cm_initial mark c0=true.
Proof. reflexivity. Qed.
Example unmarked_A_can_carry_distant_marker : gm_edge mark Aempty Bempty=true.
Proof. reflexivity. Qed.
Example old_entry_rule_forgets_A_marker : cm_edge mark Aempty Bempty=false.
Proof. reflexivity. Qed.
Example consuming_only_visible_marker_rejects : gm_edge mark Amarked Bempty=false.
Proof. reflexivity. Qed.
Example unmarked_A_can_carry_through_A : gm_edge mark Aempty Aempty=true.
Proof. reflexivity. Qed.
