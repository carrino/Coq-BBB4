(* M4 sizing, part B stage 2 (2026-08-12): WHEN does a diverging
   closure cross the node-size threshold?

   Stage 1 (ProbeRwDivSig) found the separation, pooled over the four
   shipped rungs on the 40-machine residue sample:

     max node size over closures that CATCH   : 12
     min node size over closures that DIVERGE : 11

   So a threshold M = 12 keeps every catch in the sample and aborts
   every diverging closure except the one that never exceeds 11.  That
   is necessary and not sufficient: a threshold crossed at pop 5,000
   refunds nothing.  The lever's size is

     refund = (FC - pop at which the closure first exceeds M) / FC

   summed over the diverging closures, and that is what this measures.

   [tclose] is [close] with one added test per pop -- if the popped
   node's [asz] exceeds M, stop and report the pop index.  Status 3 is
   that abort.  Nothing else changes: same walk, same order, same
   successors.

   The abort is MONOTONE in exactly the way the fuel cut was: it can
   only turn a [Some] into a [None], so it can lose a catch and can
   never gain one.  That is what makes the eventual gate exhaustive
   rather than sampled -- tools/repwl_residue_caught.tsv tabulates all
   25,511 kept catches, so every one can be re-checked against a
   candidate M instead of diffing a sample.

   Untrusted probe: not in _CoqProject, loads into no proof. *)

From Coq Require Import Arith Bool List ZArith PArith.
From Coq Require Import FSets.FMapPositive.
From BBB4 Require Import BBB4_Statement CTape PosEnc Closure
                         ProbeWalkCommon ProbeTierCost.
From BBB4.Checkers Require Import Cycle RepWL.
From BBB4.Census Require Import TNF_QH Decide RepWLSearch.
Import ListNotations.

Definition FC : nat := 5120.

Definition asz (a : rconf) : nat :=
  match a with
  | (_, (l, ls, _, rs, r)) =>
      List.length l + List.length r + List.length ls + List.length rs
  end.

(* status: 0 = fuel exhausted, 1 = closed, 2 = succs None,
           3 = ABORTED by the node-size threshold *)
Fixpoint tclose (tm : TM) (L T fuel M : nat) (sp : PositiveSet.t)
    (todo : list rconf) : nat * nat :=
  match fuel with
  | 0 => (0, 0)
  | S f =>
      match todo with
      | [] => (1, S f)
      | a :: todo' =>
          if pset_mem rconf rconf_enc a sp
          then tclose tm L T f M sp todo'
          else if M <? asz a then (3, S f)
          else match rw_succs tm L T a with
               | None => (2, S f)
               | Some l =>
                   tclose tm L T f M
                     (pset_add rconf rconf_enc a sp) (l ++ todo')
               end
      end
  end.

Definition runt (M L T : nat) (tm : TM) : nat * nat :=
  match csteps tm 0 c0 with
  | None => (2, 0)
  | Some cc => tclose tm L T FC M PositiveSet.empty [rw_seed L T cc]
  end.

Definition tstat (r : nat * nat) : nat := fst r.
Definition tpops (r : nat * nat) : nat := FC - snd r.

Fixpoint cnt {B} (l : list B) (f : B -> bool) (acc : nat) : nat :=
  match l with [] => acc | x :: t => cnt t f (acc + (if f x then 1 else 0)) end.
Fixpoint sumf {B} (l : list B) (f : B -> nat) (acc : nat) : nat :=
  match l with [] => acc | x :: t => sumf t f (acc + f x) end.
Fixpoint maxf {B} (l : list B) (f : B -> nat) (acc : nat) : nat :=
  match l with [] => acc | x :: t => maxf t f (Nat.max acc (f x)) end.

Definition reach (done : list (nat * nat * nat)) (ms : list TM) : list TM :=
  filter (fun tm => negb (anyb (fun '(L, T, t) => rw_tier tm L T t FC) done)) ms.

Definition pop0 : list TM := grp_RES.
Definition pop1 : list TM := Eval vm_compute in reach [(2,2,0)] pop0.
Definition pop2 : list TM := Eval vm_compute in reach [(2,2,0);(3,2,0)] pop0.
Definition pop3 : list TM :=
  Eval vm_compute in reach [(2,2,0);(3,2,0);(4,2,0)] pop0.

(** the diverging closures, per rung, identified at the SHIPPED cap *)
Definition divg (L T : nat) (tm : TM) : bool :=
  match csteps tm 0 c0 with
  | None => false
  | Some cc =>
      match close rconf rconf_enc (rw_succs tm L T) FC
                  [] MSetPositive.PositiveSet.empty [rw_seed L T cc] with
      | None => true | Some _ => false end
  end.
Definition caught (L T : nat) (tm : TM) : bool := rw_tier tm L T 0 FC.

Definition D22 := Eval vm_compute in filter (divg 2 2) pop0.
Definition D32 := Eval vm_compute in filter (divg 3 2) pop1.
Definition D42 := Eval vm_compute in filter (divg 4 2) pop2.
Definition D23 := Eval vm_compute in filter (divg 2 3) pop3.
Definition K22 := Eval vm_compute in filter (caught 2 2) pop0.
Definition K32 := Eval vm_compute in filter (caught 3 2) pop1.
Definition K42 := Eval vm_compute in filter (caught 4 2) pop2.
Definition K23 := Eval vm_compute in filter (caught 2 3) pop3.

(** per rung at threshold M, over the DIVERGING closures:
      (n, aborted, still-burns-the-cap, total pops spent, max pops)
    "total pops spent" against n * 5120 is the refund. *)
Definition drow (M L T : nat) (ms : list TM) : nat * nat * nat * nat * nat :=
  let rs := map (runt M L T) ms in
  (List.length ms,
   cnt rs (fun r => tstat r =? 3) 0,
   cnt rs (fun r => tstat r =? 0) 0,
   sumf rs tpops 0,
   maxf rs tpops 0).

(** per rung at threshold M, over the CAUGHT closures:
      (n, still caught, ABORTED = catches LOST) *)
Definition krow (M L T : nat) (ms : list TM) : nat * nat * nat :=
  let rs := map (runt M L T) ms in
  (List.length ms,
   cnt rs (fun r => tstat r =? 1) 0,
   cnt rs (fun r => tstat r =? 3) 0).

(* --- catches lost, per threshold.  Third component MUST be 0. ------ *)
Eval vm_compute in (krow 12 2 2 K22, krow 12 3 2 K32,
                    krow 12 4 2 K42, krow 12 2 3 K23).
Eval vm_compute in (krow 16 2 2 K22, krow 16 3 2 K32,
                    krow 16 4 2 K42, krow 16 2 3 K23).
Eval vm_compute in (krow 24 2 2 K22, krow 24 3 2 K32,
                    krow 24 4 2 K42, krow 24 2 3 K23).

(* --- the refund, per threshold, per rung --------------------------- *)
Eval vm_compute in (drow 12 2 2 D22, drow 12 3 2 D32,
                    drow 12 4 2 D42, drow 12 2 3 D23).
Eval vm_compute in (drow 16 2 2 D22, drow 16 3 2 D32,
                    drow 16 4 2 D42, drow 16 2 3 D23).
Eval vm_compute in (drow 24 2 2 D22, drow 24 3 2 D32,
                    drow 24 4 2 D42, drow 24 2 3 D23).

(* --- and the same in TIME, at M = 16 ------------------------------- *)
Definition tsz (M L T : nat) (tm : TM) : nat := snd (runt M L T tm).
Definition csz (L T : nat) (tm : TM) : nat :=
  match csteps tm 0 c0 with
  | None => 0
  | Some cc =>
      match close rconf rconf_enc (rw_succs tm L T) FC
                  [] MSetPositive.PositiveSet.empty [rw_seed L T cc] with
      | None => 1 | Some Sl => List.length Sl end
  end.

(* warm-up *)
Time Eval vm_compute in sumf (firstn 1 pop0) (csz 2 2) 0.

(* diverging closures, shipped close vs threshold-aborted close *)
Time Eval vm_compute in
  (sumf D22 (csz 2 2) 0, sumf D32 (csz 3 2) 0,
   sumf D42 (csz 4 2) 0, sumf D23 (csz 2 3) 0).
Time Eval vm_compute in
  (sumf D22 (tsz 16 2 2) 0, sumf D32 (tsz 16 3 2) 0,
   sumf D42 (tsz 16 4 2) 0, sumf D23 (tsz 16 2 3) 0).
