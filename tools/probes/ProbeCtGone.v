(* A/B: per-tier decider cost with scan_ct gone (current Decide.vo)
   -- same sampled machines as ProbeTierCost. *)
From Coq Require Import Arith List.
From BBB4 Require Import BBB4_Statement CTape ProbeWalkCommon ProbeTierCost.
From BBB4.Census Require Import TNF_QH Decide.
Import ListNotations.
Time Eval vm_compute in
  (List.length (filter decided (map decider0 grp_H))).
Time Eval vm_compute in
  (List.length (filter decided (map decider0 grp_C))).
Time Eval vm_compute in
  (List.length (filter decided (map decider0 grp_T))).
Time Eval vm_compute in
  (List.length (filter decided (map decider0 grp_N2))).
Time Eval vm_compute in
  (List.length (filter decided (map decider0 grp_N6))).
Time Eval vm_compute in
  (List.length (filter decided (map decider0 grp_RES))).
