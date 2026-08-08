(* Row 2 probe (2026-08-07): instrument the (3,2,0) fuel exhaustion.

   docs/CENSUS_RUNTIME.md, from ProbeRwStage:

     roughly half the machines that reach the rung burn all 8,192 fuel
     units and get None back, after which rw_tier returns false without
     ever calling the checker.

   That half is work that produces no verdict.  Before designing an
   early-abort we need the number that decides whether one can exist:
   how many pops do the machines that DO converge actually need?  If
   every converged closure finishes well under the cap, a pop budget
   below 8,192 costs no catches and refunds the whole diverging half.
   If converged closures run right up to the cap, no budget separates
   them and the sub-lever is dead.

   [pclose] is Closure.close instrumented to report (status, pool
   size, fuel left) instead of an option; same walk, same order.

   Untrusted probe: not in _CoqProject, loads into no proof. *)

From Coq Require Import Arith Bool List ZArith PArith.
From Coq Require Import FSets.FMapPositive.
From BBB4 Require Import BBB4_Statement CTape PosEnc Closure
                         ProbeWalkCommon ProbeTierCost.
From BBB4.Checkers Require Import Cycle RepWL.
From BBB4.Census Require Import TNF_QH Decide RepWLSearch.
Import ListNotations.

Definition F8k : nat := 8192.

(* status: 0 = fuel exhausted, 1 = closed, 2 = succs gave None *)
Fixpoint pclose (tm : TM) (L T fuel nseen : nat) (sp : PositiveSet.t)
    (todo : list rconf) : nat * nat * nat :=
  match fuel with
  | 0 => (0, nseen, 0)
  | S f =>
      match todo with
      | [] => (1, nseen, S f)
      | a :: todo' =>
          if pset_mem rconf rconf_enc a sp
          then pclose tm L T f nseen sp todo'
          else match rw_succs tm L T a with
               | None => (2, nseen, S f)
               | Some l =>
                   pclose tm L T f (S nseen)
                     (pset_add rconf rconf_enc a sp) (l ++ todo')
               end
      end
  end.

Definition runc (L T : nat) (tm : TM) : nat * nat * nat :=
  match csteps tm 0 c0 with
  | None => (2, 0, 0)
  | Some cc => pclose tm L T F8k 0 PositiveSet.empty [rw_seed L T cc]
  end.

(* the machines that actually reach the (3,2,0) rung under the FIXED
   ladder: rung (2,2,0) missed them *)
Definition reach32 : list TM := Eval vm_compute in
  filter (fun tm => negb (rw_tier tm 2 2 0 F8k)) grp_RES.

Definition R32 : list (TM * (nat * nat * nat)) := Eval vm_compute in
  map (fun tm => (tm, runc 3 2 tm)) reach32.
Definition RALL : list (TM * (nat * nat * nat)) := Eval vm_compute in
  map (fun tm => (tm, runc 3 2 tm)) grp_RES.

Definition stat (r : nat * nat * nat) : nat := fst (fst r).
Definition pool (r : nat * nat * nat) : nat := snd (fst r).
Definition left_ (r : nat * nat * nat) : nat := snd r.
Definition pops (r : nat * nat * nat) : nat := F8k - left_ r.

Fixpoint cnt {B : Type} (l : list B) (f : B -> bool) (acc : nat) : nat :=
  match l with [] => acc | x :: t => cnt t f (acc + (if f x then 1 else 0)) end.
Fixpoint maxf {B : Type} (l : list B) (f : B -> nat) (acc : nat) : nat :=
  match l with [] => acc | x :: t => maxf t f (Nat.max acc (f x)) end.

Definition conv (p : TM * (nat * nat * nat)) : bool := stat (snd p) =? 1.
Definition exh (p : TM * (nat * nat * nat)) : bool := stat (snd p) =? 0.
(* does the machine's (3,2,0) closure actually CATCH it? *)
Definition caught (p : TM * (nat * nat * nat)) : bool :=
  rw_tier (fst p) 3 2 0 F8k.

(* --- how the rung's attempts split ------------------------------- *)
Eval vm_compute in List.length grp_RES.
Eval vm_compute in List.length reach32.
Eval vm_compute in cnt RALL conv 0.        (* closed *)
Eval vm_compute in cnt RALL exh 0.         (* burned all 8192 *)
Eval vm_compute in cnt RALL (fun p => stat (snd p) =? 2) 0.
Eval vm_compute in cnt RALL caught 0.

(* --- THE number: pops needed by closures that converge ------------ *)
Eval vm_compute in maxf (filter conv RALL) (fun p => pops (snd p)) 0.
Eval vm_compute in maxf (filter caught RALL) (fun p => pops (snd p)) 0.
Eval vm_compute in maxf (filter conv RALL) (fun p => pool (snd p)) 0.

(* how many converged closures would a pop budget of K lose? *)
Eval vm_compute in cnt (filter caught RALL) (fun p => 512 <? pops (snd p)) 0.
Eval vm_compute in cnt (filter caught RALL) (fun p => 1024 <? pops (snd p)) 0.
Eval vm_compute in cnt (filter caught RALL) (fun p => 2048 <? pops (snd p)) 0.
Eval vm_compute in cnt (filter caught RALL) (fun p => 4096 <? pops (snd p)) 0.

(* same three, restricted to the machines that reach the rung *)
Eval vm_compute in cnt R32 conv 0.
Eval vm_compute in cnt R32 exh 0.
Eval vm_compute in maxf (filter conv R32) (fun p => pops (snd p)) 0.
