(* ClosureIdx-lex A/B on the RepWL tier (untrusted probe).

   Three rows, in order of how much they tell you:

   1. CHECKER STAGE, isolated.  The certificate is computed ONCE per
      machine into data ([certdata]) and replayed into both checkers,
      so this row is the verified stage alone -- the 43% of a winning
      rw attempt that ProbeRwWin found the interned SEARCH had not
      touched.
   2. WHOLE ATTEMPT, winning rungs, old vs new pipeline.
   3. WHOLE ATTEMPT, failing rungs (the machines no rung catches).

   Same 40-machine residue sample as ProbeTierCost/ProbeRwWin, so the
   numbers line up with the tables already in docs/CENSUS_RUNTIME.md. *)

From Coq Require Import Arith Bool List ZArith PArith.
From Coq Require Import FSets.FMapPositive.
From BBB4 Require Import BBB4_Statement CTape PosEnc Closure
                         ProbeWalkCommon ProbeTierCost.
From BBB4.Checkers Require Import Cycle RepWL.
From BBB4.Census Require Import TNF_QH Decide RepWLSearch.
Import ListNotations.

Definition F8k : nat := 8192.

(* --- the four census rungs, both pipelines --- *)

Definition n1 (tm : TM) : bool := rw_tier tm 2 2 0 F8k.
Definition n2 (tm : TM) : bool := rw_tier tm 3 2 0 F8k.
Definition n3 (tm : TM) : bool := rw_tier tm 4 2 0 F8k.
Definition n4 (tm : TM) : bool := rw_tier tm 2 3 0 F8k.

Definition o1 (tm : TM) : bool := rw_tier_ref tm 2 2 0 F8k.
Definition o2 (tm : TM) : bool := rw_tier_ref tm 3 2 0 F8k.
Definition o3 (tm : TM) : bool := rw_tier_ref tm 4 2 0 F8k.
Definition o4 (tm : TM) : bool := rw_tier_ref tm 2 3 0 F8k.

Fixpoint repb (l : list TM) (f : TM -> bool) (acc : nat) : nat :=
  match l with
  | [] => acc
  | tm :: t => repb t f (acc + (if f tm then 1 else 0))
  end.

(* the rw-catchable machines: winning attempts live here *)
Definition rwl : list TM := Eval vm_compute in
  filter (fun tm => n1 tm || n2 tm || n3 tm || n4 tm) grp_RES.

(* and the ones nothing catches: failing attempts, full search to
   exhaustion, no short-circuit anywhere *)
Definition rwf : list TM := Eval vm_compute in
  filter (fun tm => negb (n1 tm || n2 tm || n3 tm || n4 tm)) grp_RES.

Eval vm_compute in (List.length rwl, List.length rwf).

(* --- 1. the verified stage, isolated ---------------------------- *)

(* rw_tier's certificate, materialised as data so it can be replayed
   into both checkers without re-running the untrusted search *)
Definition certdata (tm : TM) (L T t fuel : nat) : list (St * list rwcomp) :=
  match csteps tm t c0 with
  | None => []
  | Some cc =>
      match close rconf rconf_enc (rw_succs tm L T) fuel
                  [] MSetPositive.PositiveSet.empty [rw_seed L T cc] with
      | None => []
      | Some Sl =>
          map (fun q =>
                 (q, if cvisits tm c0 t q
                        || existsb (fun a => st_eqb (rw_state a) q) Sl
                     then rw_procedure tm L T Sl q
                     else [])) all_St
      end
  end.

Definition certfun (d : list (St * list rwcomp)) (q : St) : list rwcomp :=
  match List.find (fun p => st_eqb (fst p) q) d with
  | Some p => snd p
  | None => []
  end.

(* winning-rung certificates for the (2,2,0) rung -- the rung that
   catches 30 of the 32 catchable machines *)
Definition C1 : list (TM * list (St * list rwcomp)) := Eval vm_compute in
  map (fun tm => (tm, certdata tm 2 2 0 F8k)) rwl.

(* ... and for (3,2,0), the big-L closures where ProbeRwWin measured
   the verified checker dominating a winning attempt *)
Definition C2 : list (TM * list (St * list rwcomp)) := Eval vm_compute in
  map (fun tm => (tm, certdata tm 3 2 0 F8k)) rwl.

Fixpoint repc (l : list (TM * list (St * list rwcomp)))
    (f : TM -> (St -> list rwcomp) -> bool) (acc : nat) : nat :=
  match l with
  | [] => acc
  | p :: t => repc t f (acc + (if f (fst p) (certfun (snd p)) then 1 else 0))
  end.

Definition chk_old_1 (tm : TM) (c : St -> list rwcomp) : bool :=
  rw_check_neverqh tm 2 2 0 F8k c.
Definition chk_new_1 (tm : TM) (c : St -> list rwcomp) : bool :=
  rw_check_neverqh_idx tm 2 2 0 F8k c.
Definition chk_old_2 (tm : TM) (c : St -> list rwcomp) : bool :=
  rw_check_neverqh tm 3 2 0 F8k c.
Definition chk_new_2 (tm : TM) (c : St -> list rwcomp) : bool :=
  rw_check_neverqh_idx tm 3 2 0 F8k c.

(* checker stage, rung (2,2,0): old then new (accept counts must match) *)
Time Eval vm_compute in repc C1 chk_old_1 0.
Time Eval vm_compute in repc C1 chk_new_1 0.

(* checker stage, rung (3,2,0): old then new *)
Time Eval vm_compute in repc C2 chk_old_2 0.
Time Eval vm_compute in repc C2 chk_new_2 0.

(* --- 2. whole attempt, winning rungs ---------------------------- *)

Time Eval vm_compute in repb rwl o1 0.
Time Eval vm_compute in repb rwl n1 0.
Time Eval vm_compute in repb rwl o2 0.
Time Eval vm_compute in repb rwl n2 0.
Time Eval vm_compute in repb rwl o3 0.
Time Eval vm_compute in repb rwl n3 0.
Time Eval vm_compute in repb rwl o4 0.
Time Eval vm_compute in repb rwl n4 0.

(* --- 3. whole attempt, failing rungs ---------------------------- *)

Time Eval vm_compute in repb rwf o1 0.
Time Eval vm_compute in repb rwf n1 0.
Time Eval vm_compute in repb rwf o3 0.
Time Eval vm_compute in repb rwf n3 0.
Time Eval vm_compute in repb rwf o4 0.
Time Eval vm_compute in repb rwf n4 0.
