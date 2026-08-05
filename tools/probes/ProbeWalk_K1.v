From Coq Require Import Arith List.
From BBB4 Require Import ProbeWalkCommon.
Import ListNotations.
Time Eval vm_compute in
  (let q := Nat.iter 1 qsuc q_probe in (length (fst q), length (snd q))).
