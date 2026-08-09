(* Row 1 probe (2026-08-07): Coq's [existsb] is [f a || existsb l] and
   [orb] is a FUNCTION, so under call-by-value every rung of a ladder
   runs even after an earlier rung already returned true.  The rung
   ladders in Decide.v are all written with [existsb].

   This is the shipped [try_rw] against a short-circuiting ladder with
   the SAME boolean value (nested [if], the [lp_rewind] fix shape).
   Catch counts must be identical; the times are the A/B.

   Untrusted probe: not in _CoqProject, loads into no proof. *)

From Coq Require Import Arith Bool List.
From BBB4 Require Import BBB4_Statement CTape ProbeWalkCommon ProbeTierCost.
From BBB4.Census Require Import TNF_QH Decide RepWLSearch.
Import ListNotations.

Definition F8k : nat := 8192.

(* exactly Census/Decide.v [try_rw], with Run.v's rungs *)
Definition rw_existsb (tm : TM) : bool :=
  existsb (fun r => let '(L, T, t) := r in rw_tier tm L T t F8k) rwr.

(* same boolean function, short-circuiting *)
Fixpoint rw_sc_go (rs : list (nat * nat * nat)) (tm : TM) : bool :=
  match rs with
  | [] => false
  | r :: rest =>
      let '(L, T, t) := r in
      if rw_tier tm L T t F8k then true else rw_sc_go rest tm
  end.
Definition rw_sc (tm : TM) : bool := rw_sc_go rwr tm.

Fixpoint cnt (l : list TM) (f : TM -> bool) (acc : nat) : nat :=
  match l with
  | [] => acc
  | tm :: t => cnt t f (acc + (if f tm then 1 else 0))
  end.

(* per-rung isolated cost, for attribution *)
Definition rung_only (L T t : nat) (tm : TM) : bool := rw_tier tm L T t F8k.

Time Eval vm_compute in cnt grp_RES rw_existsb 0.
Time Eval vm_compute in cnt grp_RES rw_sc 0.
Time Eval vm_compute in cnt grp_RES rw_existsb 0.
Time Eval vm_compute in cnt grp_RES rw_sc 0.

Time Eval vm_compute in cnt grp_RES (rung_only 2 2 0) 0.
Time Eval vm_compute in cnt grp_RES (rung_only 3 2 0) 0.
Time Eval vm_compute in cnt grp_RES (rung_only 4 2 0) 0.
Time Eval vm_compute in cnt grp_RES (rung_only 2 3 0) 0.
