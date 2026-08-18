(* M4 sizing, part D (2026-08-12): inside the failing attempts, split
   diverging close from converging-but-not-catching.

   Part C (ProbeRwDivPop) measured, per winning-rung group of 30, that
   the failing earlier attempts cost far more than the winning one --
   but its [csz] sums cover BOTH kinds of failing attempt:

     - a close that DIVERGES: pure close cost, then rw_tier returns
       false without calling the search or the checker.  This is what
       M4 would remove.
     - a close that CONVERGES but whose certificate does not catch:
       close + rw_procedure + the verified checker, all of it failing.
       M4 does NOT touch this -- the closure is well-behaved, it simply
       does not prove anything.

   Only the first is M4's prize, so the two have to be separated before
   the ceiling can be quoted.  Groups are reused from ProbeRwDivPop so
   the sample is identical.

   Untrusted probe: not in _CoqProject, loads into no proof. *)

From Coq Require Import Arith Bool List ZArith PArith.
From Coq Require Import FSets.FMapPositive.
From BBB4 Require Import BBB4_Statement CTape PosEnc Closure
                         ProbeWalkCommon ProbeTierCost ProbeRwDivPop.
From BBB4.Checkers Require Import Cycle RepWL.
From BBB4.Census Require Import TNF_QH Decide RepWLSearch.
Import ListNotations.

(** the failing rungs each group pays, partitioned at Definition time *)
Definition d32_22 := Eval vm_compute in filter (divg 2 2) G32.
Definition c32_22 := Eval vm_compute in filter (fun t => negb (divg 2 2 t)) G32.
Definition d42_22 := Eval vm_compute in filter (divg 2 2) G42.
Definition c42_22 := Eval vm_compute in filter (fun t => negb (divg 2 2 t)) G42.
Definition d42_32 := Eval vm_compute in filter (divg 3 2) G42.
Definition c42_32 := Eval vm_compute in filter (fun t => negb (divg 3 2 t)) G42.
Definition d23_22 := Eval vm_compute in filter (divg 2 2) G23.
Definition c23_22 := Eval vm_compute in filter (fun t => negb (divg 2 2 t)) G23.
Definition d23_32 := Eval vm_compute in filter (divg 3 2) G23.
Definition c23_32 := Eval vm_compute in filter (fun t => negb (divg 3 2 t)) G23.
Definition d23_42 := Eval vm_compute in filter (divg 4 2) G23.
Definition c23_42 := Eval vm_compute in filter (fun t => negb (divg 4 2 t)) G23.

Eval vm_compute in (List.length d32_22, List.length d42_22,
                    List.length d42_32).
Eval vm_compute in (List.length d23_22, List.length d23_32,
                    List.length d23_42).

(* warm-up *)
Time Eval vm_compute in sumf (firstn 1 G22) (csz 2 2) 0.

(* --- DIVERGING closes: what M4 could delete --------------------- *)
Time Eval vm_compute in sumf d32_22 (csz 2 2) 0.
Time Eval vm_compute in (sumf d42_22 (csz 2 2) 0, sumf d42_32 (csz 3 2) 0).
Time Eval vm_compute in (sumf d23_22 (csz 2 2) 0, sumf d23_32 (csz 3 2) 0,
                         sumf d23_42 (csz 4 2) 0).

(* --- CONVERGING-but-failing closes: what it could not ------------ *)
Time Eval vm_compute in sumf c32_22 (csz 2 2) 0.
Time Eval vm_compute in (sumf c42_22 (csz 2 2) 0, sumf c42_32 (csz 3 2) 0).
Time Eval vm_compute in (sumf c23_22 (csz 2 2) 0, sumf c23_32 (csz 3 2) 0,
                         sumf c23_42 (csz 4 2) 0).

(* --- and the whole failing ATTEMPT (close + search + checker) on
       the converging-but-failing half, so the residue of the ladder
       total is accounted for rather than inferred ----------------- *)
Time Eval vm_compute in cnt c32_22 (fun t => rw_tier t 2 2 0 FC) 0.
Time Eval vm_compute in (cnt c42_22 (fun t => rw_tier t 2 2 0 FC) 0,
                         cnt c42_32 (fun t => rw_tier t 3 2 0 FC) 0).
Time Eval vm_compute in (cnt c23_22 (fun t => rw_tier t 2 2 0 FC) 0,
                         cnt c23_32 (fun t => rw_tier t 3 2 0 FC) 0,
                         cnt c23_42 (fun t => rw_tier t 4 2 0 FC) 0).
