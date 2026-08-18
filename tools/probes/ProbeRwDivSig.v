(* M4 sizing, part B (2026-08-12): is divergence SIGNPOSTED, or only
   discoverable by burning the cap?

   Part A (ProbeRwDivTime) sizes the prize.  This asks whether it is
   reachable at all, because "detect divergence early" is only a lever
   if diverging closures do something observable and cheap that
   converging ones do not.  Two candidate signals, and only one is new:

   (a) POPS SO FAR.  This is just a lower fuel cap, and it is already
       sized and rejected -- ProbeRwFuelDiff gated 4,608 exhaustively
       and the refund is ~10-16% of the diverging burn.  Not this.

   (b) NODE SIZE.  RepWL caps an item's repeat count at T, so counts
       cannot run away; what can is the NUMBER of run-length items,
       i.e. the abstract tape acquiring ever more distinct blocks.  If
       converging closures stay under some item count M* and diverging
       ones cross it early, then "abort when a popped node exceeds M*"
       is a cheap test -- one length comparison per pop, against
       rw_succs' per-pop cost.

   This measures (b) at stage 1: per closure, the maximum node size
   over every node POPPED, alongside the status.  What decides the
   lever is two numbers put next to each other:

     M* = max node size over closures that CONVERGE (and the tighter
          max over those that actually CATCH), and
     the node sizes diverging closures reach.

   If they overlap, no threshold separates them and M4's node-size form
   is dead for the cost of one probe rather than one round -- which is
   what row 3 of the old next-steps list was gated for, and how it
   died.  If they separate, stage 2 measures WHEN the crossing happens,
   since a threshold crossed at pop 5,000 refunds nothing.

   No catch can be lost by measuring; nothing here aborts anything.

   Untrusted probe: not in _CoqProject, loads into no proof. *)

From Coq Require Import Arith Bool List ZArith PArith.
From Coq Require Import FSets.FMapPositive.
From BBB4 Require Import BBB4_Statement CTape PosEnc Closure
                         ProbeWalkCommon ProbeTierCost.
From BBB4.Checkers Require Import Cycle RepWL.
From BBB4.Census Require Import TNF_QH Decide RepWLSearch.
Import ListNotations.

Definition FC : nat := 5120.

(** an rconf's size: how many run-length items and loose symbols the
    abstract tape carries.  [it_c] is capped at T by construction, so
    this is the only component that can grow without bound. *)
Definition asz (a : rconf) : nat :=
  match a with
  | (_, (l, ls, _, rs, r)) =>
      List.length l + List.length r + List.length ls + List.length rs
  end.

(** [close] instrumented with the running maximum of [asz] over popped
    nodes.  Same walk, same order, same successor function -- one
    Nat.max per pop added.
    status: 0 = fuel exhausted, 1 = closed, 2 = succs gave None *)
Fixpoint mclose (tm : TM) (L T fuel nseen mx : nat) (sp : PositiveSet.t)
    (todo : list rconf) : nat * nat * nat :=
  match fuel with
  | 0 => (0, nseen, mx)
  | S f =>
      match todo with
      | [] => (1, nseen, mx)
      | a :: todo' =>
          if pset_mem rconf rconf_enc a sp
          then mclose tm L T f nseen mx sp todo'
          else match rw_succs tm L T a with
               | None => (2, nseen, Nat.max mx (asz a))
               | Some l =>
                   mclose tm L T f (S nseen) (Nat.max mx (asz a))
                     (pset_add rconf rconf_enc a sp) (l ++ todo')
               end
      end
  end.

Definition runm (L T : nat) (tm : TM) : nat * nat * nat :=
  match csteps tm 0 c0 with
  | None => (2, 0, 0)
  | Some cc => mclose tm L T FC 0 0 PositiveSet.empty [rw_seed L T cc]
  end.

Definition stat (r : nat * nat * nat) : nat := fst (fst r).
Definition seen (r : nat * nat * nat) : nat := snd (fst r).
Definition mxsz (r : nat * nat * nat) : nat := snd r.

Fixpoint cnt {B} (l : list B) (f : B -> bool) (acc : nat) : nat :=
  match l with [] => acc | x :: t => cnt t f (acc + (if f x then 1 else 0)) end.
Fixpoint maxf {B} (l : list B) (f : B -> nat) (acc : nat) : nat :=
  match l with [] => acc | x :: t => maxf t f (Nat.max acc (f x)) end.
Fixpoint minf {B} (l : list B) (f : B -> nat) (acc : nat) : nat :=
  match l with [] => acc | x :: t => minf t f (Nat.min acc (f x)) end.

Definition reach (done : list (nat * nat * nat)) (ms : list TM) : list TM :=
  filter (fun tm => negb (anyb (fun '(L, T, t) => rw_tier tm L T t FC) done)) ms.

Definition pop0 : list TM := grp_RES.
Definition pop1 : list TM := Eval vm_compute in reach [(2,2,0)] pop0.
Definition pop2 : list TM := Eval vm_compute in reach [(2,2,0);(3,2,0)] pop0.
Definition pop3 : list TM :=
  Eval vm_compute in reach [(2,2,0);(3,2,0);(4,2,0)] pop0.

(** (machine, closure result, does this rung CATCH it) *)
Definition rowsof (L T : nat) (ms : list TM)
  : list (nat * nat * nat * bool) :=
  map (fun tm => let r := runm L T tm in
                 (stat r, seen r, mxsz r, rw_tier tm L T 0 FC)) ms.

Definition R22 := Eval vm_compute in rowsof 2 2 pop0.
Definition R32 := Eval vm_compute in rowsof 3 2 pop1.
Definition R42 := Eval vm_compute in rowsof 4 2 pop2.
Definition R23 := Eval vm_compute in rowsof 2 3 pop3.

Definition st_ (r : nat * nat * nat * bool) : nat := fst (fst (fst r)).
Definition sn_ (r : nat * nat * nat * bool) : nat := snd (fst (fst r)).
Definition mx_ (r : nat * nat * nat * bool) : nat := snd (fst r).
Definition ct_ (r : nat * nat * nat * bool) : bool := snd r.

Definition isconv (r : nat * nat * nat * bool) : bool := st_ r =? 1.
Definition isdiv  (r : nat * nat * nat * bool) : bool := st_ r =? 0.

(** the row that decides the lever:
      (reaching, converged, diverged, caught,
       MAX node size among CONVERGED,
       MAX node size among CAUGHT,
       MIN node size among DIVERGED,
       MAX node size among DIVERGED)
    A threshold exists iff  min-over-diverged  >  max-over-caught. *)
Definition verdict (rs : list (nat * nat * nat * bool))
  : nat * nat * nat * nat * nat * nat * nat * nat :=
  (List.length rs,
   cnt rs isconv 0,
   cnt rs isdiv 0,
   cnt rs ct_ 0,
   maxf (filter isconv rs) mx_ 0,
   maxf (filter ct_ rs) mx_ 0,
   minf (filter isdiv rs) mx_ 9999,
   maxf (filter isdiv rs) mx_ 0).

Eval vm_compute in verdict R22.
Eval vm_compute in verdict R32.
Eval vm_compute in verdict R42.
Eval vm_compute in verdict R23.

(** pooled over all four rungs -- the threshold has to hold for every
    rung the walk runs, not one *)
Eval vm_compute in verdict (R22 ++ R32 ++ R42 ++ R23).

(** and the closure SIZES, for context: a diverging closure that is
    also small in node count would mean the walk is re-treading, not
    growing *)
Eval vm_compute in (maxf (filter isconv (R22 ++ R32 ++ R42 ++ R23)) sn_ 0,
                    maxf (filter isdiv  (R22 ++ R32 ++ R42 ++ R23)) sn_ 0).
