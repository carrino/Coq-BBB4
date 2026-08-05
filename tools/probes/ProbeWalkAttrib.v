From Coq Require Import Arith List.
From BBB4 Require Import BBB4_Statement ProbeWalkCommon.
From BBB4.Census Require Import TNF_QH Decide.
Import ListNotations.
(* ladder disabled: undecided machines go to the back list *)
Definition decider_nolad : TM -> QHResult :=
  decide_easy Bc 130 512 200000 512 [] [] [] [] 0 pmap0 emap dmap0 hmap0.
Definition qsuc7n (q : SearchQueue) : SearchQueue :=
  SearchQueue_upds q decider_nolad 7.
Time Eval vm_compute in
  (let q := Nat.iter 4 qsuc7n q_probe in (length (fst q), length (snd q))).
