(* 1. does rung (3,2,0) catch anything the cheap rungs miss?
   2. failing-rung costs on ladder-bound machines (the reorder's price
      is paid by machines that fail rw entirely). *)
From Coq Require Import Arith Bool List.
From BBB4 Require Import BBB4_Statement CTape ProbeWalkCommon ProbeTierCost.
From BBB4.Census Require Import TNF_QH Decide RepWLSearch.
Import ListNotations.
Definition F8k : nat := 8192.
Definition rung1 (tm : TM) : bool := rw_tier tm 2 2 0 F8k.
Definition rung2 (tm : TM) : bool := rw_tier tm 3 2 0 F8k.
Definition rung3 (tm : TM) : bool := rw_tier tm 4 2 0 F8k.
Definition rung4 (tm : TM) : bool := rw_tier tm 2 3 0 F8k.
(* rung2-exclusive over the residue sample *)
Eval vm_compute in
  List.length (filter (fun tm =>
    rung2 tm && negb (rung1 tm || rung3 tm || rung4 tm)) grp_RES).
(* failing-rung costs on the qhb-class: machines that reach rw in the
   pipeline but are NOT rw-catchable (in-census: the qhb/deferred
   sliver). approximate with residue machines failing all rw rungs *)
Definition rwfail : list TM := Eval vm_compute in
  filter (fun tm => negb (rung1 tm || rung2 tm || rung3 tm || rung4 tm))
         grp_RES.
Eval vm_compute in List.length rwfail.
Fixpoint repb (l : list TM) (f : TM -> bool) (acc : nat) : nat :=
  match l with [] => acc
  | tm :: t => repb t f (acc + (if f tm then 1 else 0)) end.
Time Eval vm_compute in repb rwfail rung1 0.
Time Eval vm_compute in repb rwfail rung2 0.
Time Eval vm_compute in repb rwfail rung3 0.
Time Eval vm_compute in repb rwfail rung4 0.
