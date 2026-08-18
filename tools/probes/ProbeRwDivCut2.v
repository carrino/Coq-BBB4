(* M4 sizing, part F (2026-08-12): does a node-size cut fire EARLY, and
   does it cost a catch?

   Parts C/D size the prize on the right population: census-weighted,
   diverging closes are ~62% of the RepWL tier and ~12% of the walk.
   That is a ceiling for a detector that is free and perfect.  This
   measures the only concrete detector that stage 1 (ProbeRwDivSig)
   found a signal for, on that same right population.

   The signal: RepWL caps an item's repeat count at T, so counts cannot
   run away; the number of run-length items can.  Stage 1, on the
   40-machine residue sample, measured max node size 12 over closures
   that CATCH against 11..1221 over closures that DIVERGE.

   Two things decide the lever, and neither is the separation itself:

     1. CATCH LOSS.  A cut at M must not abort any winning closure.
        Measured here as: winning rung still catches, per group.
     2. WHEN.  A cut crossed at pop 5,000 refunds nothing.  Measured
        as the aborted close's time against the un-aborted one, whose
        baseline is ProbeRwDivPop's 23.666 / 76.683 / 41.474 s.

   The cut is MONOTONE -- it can only turn a [Some] into a [None] -- so
   a catch can be lost and never gained, which is what would make the
   real gate exhaustive over the 25,511 tabulated catches rather than
   sampled.

   Untrusted probe: not in _CoqProject, loads into no proof. *)

From Coq Require Import Arith Bool List ZArith PArith.
From Coq Require Import FSets.FMapPositive.
From BBB4 Require Import BBB4_Statement CTape PosEnc Closure
                         ProbeWalkCommon ProbeTierCost ProbeRwDivPop.
From BBB4.Checkers Require Import Cycle RepWL.
From BBB4.Census Require Import TNF_QH Decide RepWLSearch.
Import ListNotations.

Definition asz (a : rconf) : nat :=
  match a with
  | (_, (l, ls, _, rs, r)) =>
      List.length l + List.length r + List.length ls + List.length rs
  end.

(* status: 0 = fuel exhausted, 1 = closed, 2 = succs None,
           3 = ABORTED by the node-size cut *)
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

Definition tstat (M L T : nat) (tm : TM) : nat := fst (runt M L T tm).
Definition tleft (M L T : nat) (tm : TM) : nat := snd (runt M L T tm).
Definition tpops (M L T : nat) (tm : TM) : nat := FC - tleft M L T tm.

(** max node size over a closure that CONVERGES -- the number the cut
    must stay above for that closure to survive *)
Fixpoint mclose (tm : TM) (L T fuel mx : nat) (sp : PositiveSet.t)
    (todo : list rconf) : nat :=
  match fuel with
  | 0 => mx
  | S f =>
      match todo with
      | [] => mx
      | a :: todo' =>
          if pset_mem rconf rconf_enc a sp then mclose tm L T f mx sp todo'
          else match rw_succs tm L T a with
               | None => Nat.max mx (asz a)
               | Some l =>
                   mclose tm L T f (Nat.max mx (asz a))
                     (pset_add rconf rconf_enc a sp) (l ++ todo')
               end
      end
  end.
Definition runmx (L T : nat) (tm : TM) : nat :=
  match csteps tm 0 c0 with
  | None => 0
  | Some cc => mclose tm L T FC 0 PositiveSet.empty [rw_seed L T cc]
  end.

Fixpoint maxf {B} (l : list B) (f : B -> nat) (acc : nat) : nat :=
  match l with [] => acc | x :: t => maxf t f (Nat.max acc (f x)) end.

(** the diverging failing closes, from ProbeRwDivPop's groups *)
Definition d32_22 := Eval vm_compute in filter (divg 2 2) G32.
Definition d42_22 := Eval vm_compute in filter (divg 2 2) G42.
Definition d42_32 := Eval vm_compute in filter (divg 3 2) G42.
Definition d23_22 := Eval vm_compute in filter (divg 2 2) G23.
Definition d23_32 := Eval vm_compute in filter (divg 3 2) G23.
Definition d23_42 := Eval vm_compute in filter (divg 4 2) G23.

(* --- 1. the cut the WINNING closures force ------------------------ *)
(* max node size over each group's winning (catching) closure *)
Eval vm_compute in (maxf G22 (runmx 2 2) 0, maxf G32 (runmx 3 2) 0,
                    maxf G42 (runmx 4 2) 0, maxf G23 (runmx 2 3) 0).

(* --- 2. catch loss at M: each group's winning rung must still fire - *)
Definition kept (M L T : nat) (l : list TM) : nat :=
  cnt l (fun tm => tstat M L T tm =? 1) 0.
Eval vm_compute in (kept 12 2 2 G22, kept 12 3 2 G32,
                    kept 12 4 2 G42, kept 12 2 3 G23).
Eval vm_compute in (kept 16 2 2 G22, kept 16 3 2 G32,
                    kept 16 4 2 G42, kept 16 2 3 G23).
Eval vm_compute in (kept 24 2 2 G22, kept 24 3 2 G32,
                    kept 24 4 2 G42, kept 24 2 3 G23).

(* --- 3. WHEN the cut fires on the diverging closes ----------------- *)
(* aborted (status 3) count, and the pops spent before aborting *)
Definition acnt (M L T : nat) (l : list TM) : nat :=
  cnt l (fun tm => tstat M L T tm =? 3) 0.
Eval vm_compute in (acnt 16 2 2 d32_22, acnt 16 2 2 d42_22,
                    acnt 16 3 2 d42_32).
Eval vm_compute in (acnt 16 2 2 d23_22, acnt 16 3 2 d23_32,
                    acnt 16 4 2 d23_42).
Eval vm_compute in (sumf d32_22 (tpops 16 2 2) 0,
                    sumf d42_22 (tpops 16 2 2) 0,
                    sumf d42_32 (tpops 16 3 2) 0).
Eval vm_compute in (sumf d23_22 (tpops 16 2 2) 0,
                    sumf d23_32 (tpops 16 3 2) 0,
                    sumf d23_42 (tpops 16 4 2) 0).

(* warm-up *)
Time Eval vm_compute in sumf (firstn 1 G22) (csz 2 2) 0.

(* --- 4. the refund at the SAFE cut M = 24 (no catch lost above).
       Baselines, same machines, un-aborted (ProbeRwDivPop/Split):
       23.666 s / 76.683 s / 41.474 s.  Summing [tpops] not [tleft]:
       the latter sums to ~90,000 as a unary nat and overflows. ---- *)
Eval vm_compute in (acnt 24 2 2 d32_22, acnt 24 2 2 d42_22,
                    acnt 24 3 2 d42_32).
Eval vm_compute in (acnt 24 2 2 d23_22, acnt 24 3 2 d23_32,
                    acnt 24 4 2 d23_42).
Time Eval vm_compute in sumf d32_22 (tpops 24 2 2) 0.
Time Eval vm_compute in (sumf d42_22 (tpops 24 2 2) 0,
                         sumf d42_32 (tpops 24 3 2) 0).
Time Eval vm_compute in (sumf d23_22 (tpops 24 2 2) 0,
                         sumf d23_32 (tpops 24 3 2) 0,
                         sumf d23_42 (tpops 24 4 2) 0).

(* --- 5. the price of headroom.  The exhaustive gate
       (tools/probes/gen_rwcut_gate.py over all 25,511 kept catches)
       puts the census-wide max node size of a WINNING closure at 20,
       so 24 is 20% headroom and 32 is 60%.  A larger M is the SAFER
       direction here -- it aborts less -- exactly as more fuel was
       safe a fortiori when 5120 shipped over a gated 4608.  What it
       costs is measured here rather than assumed. *)
Eval vm_compute in (acnt 32 2 2 d32_22, acnt 32 2 2 d42_22,
                    acnt 32 3 2 d42_32,
                    acnt 32 2 2 d23_22, acnt 32 3 2 d23_32,
                    acnt 32 4 2 d23_42).
(* pops/64: at M = 32 two closures at (3,2,0) never cross the cut and
   burn the whole 5120, so the raw sum builds a ~40,000-deep unary nat
   and overflows -- the same trap as [tleft] above. *)
Definition tp64 (M L T : nat) (tm : TM) : nat := Nat.div (tpops M L T tm) 64.
Time Eval vm_compute in sumf d32_22 (tp64 32 2 2) 0.
Time Eval vm_compute in (sumf d42_22 (tp64 32 2 2) 0,
                         sumf d42_32 (tp64 32 3 2) 0).
Time Eval vm_compute in (sumf d23_22 (tp64 32 2 2) 0,
                         sumf d23_32 (tp64 32 3 2) 0,
                         sumf d23_42 (tp64 32 4 2) 0).
Eval vm_compute in (kept 32 2 2 G22, kept 32 3 2 G32,
                    kept 32 4 2 G42, kept 32 2 3 G23).
