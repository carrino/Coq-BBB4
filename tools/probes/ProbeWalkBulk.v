From Coq Require Import Arith List.
From BBB4 Require Import BBB4_Statement ProbeWalkCommon.
From BBB4.Census Require Import TNF_QH.
Import ListNotations.
(* the bulk subtree GGH_0RB_1LC_0LB (cheap machines; old build: 8,192
   pop-slots in 0.50 s vm) *)
Definition tm_gb : TM :=
  TM_upd' (TM_upd' TM0 StA S0 (Some (mkTrans S0 DR StB)))
          StB S0 (Some (mkTrans S1 DL StC)).
Definition gb_0LB : TNF_Node :=
  mkNode (TM_upd' tm_gb StC S0 (Some (mkTrans S0 DL StB)))
         (ptr_after (Some StD) StB).
Time Eval vm_compute in
  (let q := Nat.iter 1 qsuc ([gb_0LB], []) in (length (fst q), length (snd q))).
