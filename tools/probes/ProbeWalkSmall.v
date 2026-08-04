From Coq Require Import Arith List.
From BBB4 Require Import ProbeWalkCommon.
From BBB4.Census Require Import TNF_QH.
Import ListNotations.
(* 2^7 = 128 pop-slots per iter; 4 iters = up to 512 pops *)
Definition qsuc7 (q : SearchQueue) : SearchQueue :=
  SearchQueue_upds q decider0 7.
Time Eval vm_compute in
  (let q := Nat.iter 4 qsuc7 q_probe in (length (fst q), length (snd q))).
