(* Row 1 probe: the same [existsb] strictness question for the C/T
   bulk.  [scan_loops] is [existsb (lp_check tm) (lp_candidates tm gas)]
   and [lp_check] is a full re-simulation per candidate, so on a CAUGHT
   machine every candidate after the winning one is pure waste.

   Untrusted probe: not in _CoqProject, loads into no proof. *)

From Coq Require Import Arith Bool List.
From BBB4 Require Import BBB4_Statement CTape GTape Mirror ProbeWalkCommon ProbeTierCost.
From BBB4.Checkers Require Import Cycle TCycler.
From BBB4.Census Require Import TNF_QH Decide.
Import ListNotations.

Definition Bs : nat := 2000.

(* Decide.v [lp_check] with B instantiated *)
Definition lp_checkP (tm : TM) (cand : lp_cand) : bool :=
  match cand with
  | LpCycle n1 p => (n1 <=? Bs) && cycle_leaf_check tm n1 p
  | LpTC DR n1 P =>
      (n1 <=? Bs) && tcycler_leaf_check tm n1 P (tc_measure_W tm n1 P)
  | LpTC DL n1 P =>
      (n1 <=? Bs) &&
      tcycler_leaf_check (mirror_tm tm) n1 P
        (tc_measure_W (mirror_tm tm) n1 P)
  end.

(* exactly Decide.v [scan_loops] *)
Definition scan_existsb (tm : TM) (gas : nat) : bool :=
  existsb (lp_checkP tm) (lp_candidates tm gas).

(* same boolean, short-circuiting *)
Fixpoint anyb (f : lp_cand -> bool) (l : list lp_cand) : bool :=
  match l with
  | [] => false
  | x :: r => if f x then true else anyb f r
  end.
Definition scan_sc (tm : TM) (gas : nat) : bool :=
  anyb (lp_checkP tm) (lp_candidates tm gas).

(* the escalating block as decide_easy pays it: gas 130 then gas 512 *)
Definition block_existsb (tm : TM) : bool :=
  if scan_existsb tm 130 then true else scan_existsb tm 512.
Definition block_sc (tm : TM) : bool :=
  if scan_sc tm 130 then true else scan_sc tm 512.

Fixpoint cnt (l : list TM) (f : TM -> bool) (acc : nat) : nat :=
  match l with
  | [] => acc
  | tm :: t => cnt t f (acc + (if f tm then 1 else 0))
  end.

(* how many candidates a machine emits, and where the winner sits *)
Fixpoint win_idx (f : lp_cand -> bool) (l : list lp_cand) (i : nat) : nat :=
  match l with
  | [] => i
  | x :: r => if f x then i else win_idx f r (S i)
  end.
Fixpoint sum_over (l : list TM) (f : TM -> nat) (acc : nat) : nat :=
  match l with [] => acc | tm :: t => sum_over t f (acc + f tm) end.

Definition ncands (tm : TM) : nat := length (lp_candidates tm 130).
Definition nwin (tm : TM) : nat :=
  win_idx (lp_checkP tm) (lp_candidates tm 130) 0.

(* C tier (in-place cyclers) and T tier (translated cyclers) *)
Time Eval vm_compute in cnt grp_C block_existsb 0.
Time Eval vm_compute in cnt grp_C block_sc 0.
Time Eval vm_compute in cnt grp_T block_existsb 0.
Time Eval vm_compute in cnt grp_T block_sc 0.

(* candidates emitted vs index of the winner, gas 130, C tier *)
Eval vm_compute in sum_over grp_C ncands 0.
Eval vm_compute in sum_over grp_C nwin 0.
Eval vm_compute in length grp_C.
