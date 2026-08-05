From Coq Require Import Arith Bool List ZArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH Decide.
Import ListNotations.
Definition T (w : Sym) (d : Dir) (n : St) := Some (mkTrans w d n).
Definition mk8 (a0 a1 b0 b1 c0' c1 d0 d1 : option Trans) : TM :=
  fun q s => match q, s with
  | StA, S0 => a0 | StA, S1 => a1 | StB, S0 => b0 | StB, S1 => b1
  | StC, S0 => c0' | StC, S1 => c1 | StD, S0 => d0 | StD, S1 => d1 end.
Definition spin0 : TM := mk8 (T S0 DR StA) None None None None None None None.
Definition run1 : TM := mk8 (T S1 DR StA) None None None None None None None.
Eval vm_compute in (lp_candidates spin0 130).
Eval vm_compute in (lp_candidates run1 130).
Time Eval vm_compute in (scan_loops 2000 spin0 130).
Time Eval vm_compute in (scan_loops 2000 run1 130).
