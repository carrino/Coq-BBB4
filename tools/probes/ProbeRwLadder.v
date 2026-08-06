(* The rw slice as the walk actually pays it: Run.v's rung order with
   the existsb short-circuit, old checker vs ClosureIdx-lex, over the
   whole ProbeTierCost residue sample (untrusted probe).

   ProbeRwIdx times rungs in isolation; this is the number that scales
   to the walk, because a machine caught at (2,2,0) never reaches the
   expensive (3,2,0) rung. *)

From Coq Require Import Arith Bool List.
From BBB4 Require Import BBB4_Statement CTape ProbeWalkCommon ProbeTierCost.
From BBB4.Census Require Import TNF_QH Decide RepWLSearch.
Import ListNotations.

Definition F8k : nat := 8192.

Definition ladder_new (tm : TM) : bool :=
  existsb (fun r => let '(L, T, t) := r in rw_tier tm L T t F8k) rwr.
Definition ladder_old (tm : TM) : bool :=
  existsb (fun r => let '(L, T, t) := r in rw_tier_ref tm L T t F8k) rwr.

Fixpoint lad (l : list TM) (f : TM -> bool) (acc : nat) : nat :=
  match l with
  | [] => acc
  | tm :: t => lad t f (acc + (if f tm then 1 else 0))
  end.

(* catch counts must match; the times are the A/B *)
Time Eval vm_compute in lad grp_RES ladder_old 0.
Time Eval vm_compute in lad grp_RES ladder_new 0.
Time Eval vm_compute in lad grp_RES ladder_old 0.
Time Eval vm_compute in lad grp_RES ladder_new 0.
