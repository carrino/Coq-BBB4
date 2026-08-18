(* M4 sizing, part A (2026-08-12): what fraction of the WALK is closures
   that diverge?

   docs/CENSUS_RUNTIME.md sizes M4 from ProbeRwFuelRungs:

     18 diverging attempts burn 18 x 5,120 = 92,160 of the 103,529
     closure pops the tier spends: 89% of all RepWL closure work is
     closures that diverge and return no verdict.

   That is a POP COUNT, and pops are not time.  Two rows already in the
   same document disagree about what a pop costs by nearly three orders
   of magnitude:

     ProbeRwSplit, rung (2,2,0), closures 77-690 nodes:  close = 1 ms
     ProbeRwStage, rung (3,2,0), ~half burn the cap:     close = 3.65 s

   -- because an L=3 rconf carries far more run-length items than an
   L=2 one, and rw_succs/rconf_enc scale with that.  The 89% aggregates
   pops across rungs whose per-pop cost differs by ~500x, so it cannot
   be read as 89% of the tier's time.  Whether M4 has a ceiling worth a
   round depends on the TIME split, which is what this measures.

   Method: for each rung of the shipped ladder [(2,2,0); (3,2,0);
   (4,2,0); (2,3,0)] at the shipped fuel 5120, over the machines that
   actually REACH that rung under the shipped (short-circuiting) order,
   partition the closures into those that converge and those that
   return None, then time [close] over each half separately.  The
   partition is computed at Definition time (Eval vm_compute), so it is
   not inside any timed section.

   Per-row arithmetic is written out in the notes below, per the rule
   this project adopted after a 62-second row was recorded as ~0.

   Untrusted probe: not in _CoqProject, loads into no proof. *)

From Coq Require Import Arith Bool List ZArith PArith.
From Coq Require Import FSets.FMapPositive.
From BBB4 Require Import BBB4_Statement CTape PosEnc Closure
                         ProbeWalkCommon ProbeTierCost.
From BBB4.Checkers Require Import Cycle RepWL.
From BBB4.Census Require Import TNF_QH Decide RepWLSearch.
Import ListNotations.

Definition FC : nat := 5120.        (** Run_Compute.v's [rw_fuel_census] *)

Fixpoint sumf {B} (l : list B) (f : B -> nat) (acc : nat) : nat :=
  match l with [] => acc | x :: t => sumf t f (acc + f x) end.

(** [close] exactly as [rw_tier] calls it, forced to a nat so nothing is
    optimised away: pool size on success, 1 on no-verdict. *)
Definition closesz (L T : nat) (tm : TM) : nat :=
  match csteps tm 0 c0 with
  | None => 0
  | Some cc =>
      match close rconf rconf_enc (rw_succs tm L T) FC
                  [] MSetPositive.PositiveSet.empty [rw_seed L T cc] with
      | None => 1
      | Some Sl => List.length Sl
      end
  end.

(** the same call, read only for its verdict -- used to PARTITION, at
    Definition time, outside every measurement *)
Definition divg (L T : nat) (tm : TM) : bool :=
  match csteps tm 0 c0 with
  | None => false
  | Some cc =>
      match close rconf rconf_enc (rw_succs tm L T) FC
                  [] MSetPositive.PositiveSet.empty [rw_seed L T cc] with
      | None => true
      | Some _ => false
      end
  end.

(** machines still undecided by the rw rungs already tried -- the
    shipped ladder short-circuits (anyb), so a later rung is only ever
    attempted on what the earlier ones missed *)
Definition reach (done : list (nat * nat * nat)) (ms : list TM) : list TM :=
  filter (fun tm => negb (anyb (fun '(L, T, t) => rw_tier tm L T t FC) done)) ms.

Definition pop0 : list TM := grp_RES.
Definition pop1 : list TM := Eval vm_compute in reach [(2,2,0)] pop0.
Definition pop2 : list TM := Eval vm_compute in reach [(2,2,0);(3,2,0)] pop0.
Definition pop3 : list TM :=
  Eval vm_compute in reach [(2,2,0);(3,2,0);(4,2,0)] pop0.

(** the four partitions, computed once, NOT timed *)
Definition D22 : list TM := Eval vm_compute in filter (divg 2 2) pop0.
Definition C22 : list TM := Eval vm_compute in filter (fun t => negb (divg 2 2 t)) pop0.
Definition D32 : list TM := Eval vm_compute in filter (divg 3 2) pop1.
Definition C32 : list TM := Eval vm_compute in filter (fun t => negb (divg 3 2 t)) pop1.
Definition D42 : list TM := Eval vm_compute in filter (divg 4 2) pop2.
Definition C42 : list TM := Eval vm_compute in filter (fun t => negb (divg 4 2 t)) pop2.
Definition D23 : list TM := Eval vm_compute in filter (divg 2 3) pop3.
Definition C23 : list TM := Eval vm_compute in filter (fun t => negb (divg 2 3 t)) pop3.

(** the shipped rw ladder, as the walk pays it *)
Definition rwladder (tm : TM) : bool :=
  anyb (fun '(L, T, t) => rw_tier tm L T t FC)
       [(2,2,0); (3,2,0); (4,2,0); (2,3,0)].

(* --- population sizes (counts, not measurements) ------------------ *)
Eval vm_compute in (List.length pop0, List.length pop1,
                    List.length pop2, List.length pop3).
Eval vm_compute in (List.length D22, List.length C22).
Eval vm_compute in (List.length D32, List.length C32).
Eval vm_compute in (List.length D42, List.length C42).
Eval vm_compute in (List.length D23, List.length C23).

(* warm-up, not a measurement *)
Time Eval vm_compute in sumf (firstn 1 pop0) (closesz 2 2) 0.

(* --- A1. the denominator: the whole decider on the residue sample -- *)
Time Eval vm_compute in
  (List.length (filter decided (map decider0 grp_RES))).

(* --- A2. the whole rw ladder on the same sample -------------------- *)
Time Eval vm_compute in
  sumf pop0 (fun tm => if rwladder tm then 1 else 0) 0.

(* --- A3. close alone, DIVERGING half, per rung --------------------- *)
Time Eval vm_compute in sumf D22 (closesz 2 2) 0.
Time Eval vm_compute in sumf D32 (closesz 3 2) 0.
Time Eval vm_compute in sumf D42 (closesz 4 2) 0.
Time Eval vm_compute in sumf D23 (closesz 2 3) 0.

(* --- A4. close alone, CONVERGING half, per rung -------------------- *)
Time Eval vm_compute in sumf C22 (closesz 2 2) 0.
Time Eval vm_compute in sumf C32 (closesz 3 2) 0.
Time Eval vm_compute in sumf C42 (closesz 4 2) 0.
Time Eval vm_compute in sumf C23 (closesz 2 3) 0.
