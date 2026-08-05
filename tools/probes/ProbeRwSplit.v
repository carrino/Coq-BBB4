(* Where do the ~7.7s rw_tier catches go?  Stage split on the real
   rw-caught residue machines.  One rung does:
     1. close (untrusted exploration, fuel 8192, rconf_enc trie)
     2. rw_procedure per premise state (SCC + ranks + Bellman-Ford,
        rebuilding the adjacency per state)
     3. rw_check_neverqh (verified): closure_check_neverqh_lex, which
        RE-RUNS close, rebuilds the apool trie twice, and recomputes
        succs per state in lex_ok. *)
From Coq Require Import Arith Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape PosEnc Closure ProbeWalkCommon ProbeTierCost.
From BBB4.Checkers Require Import RepWL.
From BBB4.Census Require Import TNF_QH Decide RepWLSearch.
Import ListNotations.

Definition F8k : nat := 8192.

Definition rung1 (tm : TM) : bool := rw_tier tm 2 2 0 F8k.
Definition rung2 (tm : TM) : bool := rw_tier tm 3 2 0 F8k.
Definition rung3 (tm : TM) : bool := rw_tier tm 4 2 0 F8k.
Definition rung4 (tm : TM) : bool := rw_tier tm 2 3 0 F8k.
Definition rw_any (tm : TM) : bool :=
  rung1 tm || rung2 tm || rung3 tm || rung4 tm.

Definition rwl : list TM := Eval vm_compute in filter rw_any grp_RES.
Eval vm_compute in List.length rwl.
(* which rung wins, per machine *)
Eval vm_compute in
  (List.length (filter rung1 rwl), List.length (filter rung2 rwl),
   List.length (filter rung3 rwl), List.length (filter rung4 rwl)).

(* per-rung cost across the rw-caught machines *)
Fixpoint repb (l : list TM) (f : TM -> bool) (acc : nat) : nat :=
  match l with [] => acc
  | tm :: t => repb t f (acc + (if f tm then 1 else 0)) end.
Time Eval vm_compute in repb rwl rung1 0.
Time Eval vm_compute in repb rwl rung2 0.
Time Eval vm_compute in repb rwl rung3 0.
Time Eval vm_compute in repb rwl rung4 0.

(* stage split at rung (2,2,0) on machines it decides *)
Definition w1 : list TM := Eval vm_compute in filter rung1 rwl.
Eval vm_compute in List.length w1.

Definition close1 (tm : TM) : option (list rconf) :=
  match csteps tm 0 c0 with
  | None => None
  | Some cc => close rconf rconf_enc (rw_succs tm 2 2) F8k
                 [] PositiveSet.empty [rw_seed 2 2 cc]
  end.

(* closure sizes -- fuel 8192: are these 100 nodes or 8000? *)
Eval vm_compute in
  map (fun tm => match close1 tm with
                 | Some Sl => List.length Sl | None => 0 end) w1.

(* stage 1: the untrusted exploration alone *)
Definition st_close (tm : TM) : bool :=
  match close1 tm with Some _ => true | None => false end.
Time Eval vm_compute in repb w1 st_close 0.

(* stage 2: + the per-state search (procedure) *)
Definition st_proc (tm : TM) : bool :=
  match close1 tm with
  | None => false
  | Some Sl =>
      Nat.ltb 0 (fold_left Nat.add
        (map (fun q => List.length (rw_procedure tm 2 2 Sl q)) all_St) 0)
  end.
Time Eval vm_compute in repb w1 st_proc 0.

(* stage 3: the verified checker alone, fed the search's cert *)
Definition st_check (tm : TM) : bool :=
  match close1 tm with
  | None => false
  | Some Sl =>
      rw_check_neverqh tm 2 2 0 F8k
        (fun q => if cvisits tm c0 0 q
                     || existsb (fun a => st_eqb (rw_state a) q) Sl
                  then rw_procedure tm 2 2 Sl q else [])
  end.
(* NB: st_check re-runs close+procedure inside; subtracting stage 1+2
   gives the checker's own cost *)
Time Eval vm_compute in repb w1 st_check 0.
