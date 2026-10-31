From Coq Require Import List Bool.
From BBB24Burn43S071FAR Require Import Checker Data.
From BBB24Burn43S071FAR Require Import LocalTable.

Theorem actual_checked : check certificate Data.nodeindex c52_localfun = true.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions actual_checked.
