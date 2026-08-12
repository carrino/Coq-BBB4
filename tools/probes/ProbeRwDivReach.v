(* M4 sizing, part A' (2026-08-12): the denominator ProbeRwDivTime got
   wrong, and the correction.

   ProbeRwDivTime timed the rw ladder forced onto all 40 residue-sample
   machines and got 26.7 s -- against 7.3 s for the WHOLE decider on the
   same 40.  A tier cannot cost 3.6x the pipeline that contains it: the
   real [decide_easy] decides most of these machines in cheaper tiers
   and never reaches rw at all.  ProbeResBurn measured the same shape
   (33 of 40 decided with the RepWL rungs removed).

   So the ladder-forced number is an upper bound on a population the
   walk does not have, and the diverging-close share has to be taken
   over the machines that ACTUALLY reach the tier.

   [rwr] is a parameter of [decide_easy], so the ablation is exact:

     decider_norw = decider0 with the rw rung list emptied

   and rw is the last tier, so removing it cannot push work into a
   deeper one -- the subtraction T(full) - T(norw) is the tier's real
   cost, and the machines it leaves undecided are exactly those that
   reach it.

   Untrusted probe: not in _CoqProject, loads into no proof. *)

From Coq Require Import Arith Bool List ZArith PArith.
From Coq Require Import FSets.FMapPositive.
From BBB4 Require Import BBB4_Statement CTape PosEnc Closure
                         ProbeWalkCommon ProbeTierCost.
From BBB4.Checkers Require Import Cycle RepWL.
From BBB4.Census Require Import TNF_QH Decide RepWLSearch.
Import ListNotations.

Definition FC : nat := 5120.

Fixpoint sumf {B} (l : list B) (f : B -> nat) (acc : nat) : nat :=
  match l with [] => acc | x :: t => sumf t f (acc + f x) end.

(** the pipeline with the rw tier removed -- same parameters otherwise *)
Definition decider_norw : TM -> QHResult :=
  decide_easy Bc 130 512 200000 512 ngr rkr qhr [] 5120 pmap0 emap dmap0 hmap0.

(** the machines that actually reach the rw tier in the real pipeline *)
Definition reachrw : list TM := Eval vm_compute in
  filter (fun tm => negb (decided (decider_norw tm))) grp_RES.

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

(** rung reach WITHIN the machines that get to the tier at all *)
Definition reach (done : list (nat * nat * nat)) (ms : list TM) : list TM :=
  filter (fun tm => negb (anyb (fun '(L, T, t) => rw_tier tm L T t FC) done)) ms.

Definition q0 : list TM := reachrw.
Definition q1 : list TM := Eval vm_compute in reach [(2,2,0)] q0.
Definition q2 : list TM := Eval vm_compute in reach [(2,2,0);(3,2,0)] q0.
Definition q3 : list TM :=
  Eval vm_compute in reach [(2,2,0);(3,2,0);(4,2,0)] q0.

Definition E22 := Eval vm_compute in filter (divg 2 2) q0.
Definition E32 := Eval vm_compute in filter (divg 3 2) q1.
Definition E42 := Eval vm_compute in filter (divg 4 2) q2.
Definition E23 := Eval vm_compute in filter (divg 2 3) q3.
Definition V22 := Eval vm_compute in filter (fun t => negb (divg 2 2 t)) q0.
Definition V32 := Eval vm_compute in filter (fun t => negb (divg 3 2 t)) q1.
Definition V42 := Eval vm_compute in filter (fun t => negb (divg 4 2 t)) q2.
Definition V23 := Eval vm_compute in filter (fun t => negb (divg 2 3 t)) q3.

(* --- populations --------------------------------------------------- *)
Eval vm_compute in (List.length grp_RES, List.length reachrw).
Eval vm_compute in (List.length q0, List.length q1,
                    List.length q2, List.length q3).
Eval vm_compute in (List.length E22, List.length E32,
                    List.length E42, List.length E23).
Eval vm_compute in (List.length V22, List.length V32,
                    List.length V42, List.length V23).
(* how many of the 40 does each pipeline decide *)
Eval vm_compute in List.length (filter decided (map decider0 grp_RES)).
Eval vm_compute in List.length (filter decided (map decider_norw grp_RES)).

(* warm-up, not a measurement *)
Time Eval vm_compute in sumf (firstn 1 grp_RES) (closesz 2 2) 0.

(* --- B1. the denominator: the real decider on the residue sample --- *)
Time Eval vm_compute in
  (List.length (filter decided (map decider0 grp_RES))).

(* --- B2. the same pipeline with the rw tier removed ---------------- *)
Time Eval vm_compute in
  (List.length (filter decided (map decider_norw grp_RES))).

(* --- B3. diverging close, ONLY on machines that reach the tier ----- *)
Time Eval vm_compute in sumf E22 (closesz 2 2) 0.
Time Eval vm_compute in sumf E32 (closesz 3 2) 0.
Time Eval vm_compute in sumf E42 (closesz 4 2) 0.
Time Eval vm_compute in sumf E23 (closesz 2 3) 0.

(* --- B4. converging close, same population ------------------------- *)
Time Eval vm_compute in sumf V22 (closesz 2 2) 0.
Time Eval vm_compute in sumf V32 (closesz 3 2) 0.
Time Eval vm_compute in sumf V42 (closesz 4 2) 0.
Time Eval vm_compute in sumf V23 (closesz 2 3) 0.
