(* winning-rung A/B rows, interned code (old: 5.32/121.9/28.6/6.1 s
   over the 32 rw-catchable residue machines) *)
From Coq Require Import Arith Bool List.
From BBB4 Require Import BBB4_Statement CTape ProbeWalkCommon ProbeTierCost.
From BBB4.Census Require Import TNF_QH Decide RepWLSearch.
Import ListNotations.
Definition F8k : nat := 8192.
Definition rung1 (tm : TM) : bool := rw_tier tm 2 2 0 F8k.
Definition rung2 (tm : TM) : bool := rw_tier tm 3 2 0 F8k.
Definition rung3 (tm : TM) : bool := rw_tier tm 4 2 0 F8k.
Definition rung4 (tm : TM) : bool := rw_tier tm 2 3 0 F8k.
Definition rwl : list TM := Eval vm_compute in
  filter (fun tm => rung1 tm || rung2 tm || rung3 tm || rung4 tm) grp_RES.
Eval vm_compute in List.length rwl.
Fixpoint repb (l : list TM) (f : TM -> bool) (acc : nat) : nat :=
  match l with [] => acc
  | tm :: t => repb t f (acc + (if f tm then 1 else 0)) end.
Time Eval vm_compute in repb rwl rung1 0.
Time Eval vm_compute in repb rwl rung2 0.
Time Eval vm_compute in repb rwl rung3 0.
Time Eval vm_compute in repb rwl rung4 0.
(* the reordered pipeline's per-machine cost: existsb in NEW rung order *)
Definition rw_new (tm : TM) : bool :=
  rung1 tm || rung3 tm || rung4 tm || rung2 tm.
Time Eval vm_compute in repb rwl rw_new 0.
Time Eval vm_compute in repb grp_RES rw_new 0.
