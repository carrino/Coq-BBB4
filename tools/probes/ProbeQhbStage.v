(* Row 3 probe (2026-08-07): the ProbeRwStage recipe pointed at
   [try_qhb_lex_at], to decide whether the ClosureIdx-lex treatment is
   worth a round on the qhb tier BEFORE spending one.

   The rw round's lesson: at rung (3,2,0) ~98% of the attempt is
   [close], so interning the verified CHECKER bought ~nothing there.
   The analogous question here is whether the qhb lex rung is
   [ng_grow]/[ng_explore]-bound (untrusted search -> treatment worth
   ~nothing) or verified-stage-bound (treatment worth a round).

   Sample: the ProbeTierCost residue group, i.e. machines that really
   do reach this tier in the walk.  Rungs and parameters are Run.v's.

   Untrusted probe: not in _CoqProject, loads into no proof. *)

From Coq Require Import Arith Bool List ZArith PArith.
From Coq Require Import FSets.FMapPositive.
From BBB4 Require Import BBB4_Statement CTape PosEnc Closure
                         ProbeWalkCommon ProbeTierCost.
From BBB4.Checkers Require Import Cycle NGram Wrap.
From BBB4.Census Require Import TNF_QH Decide RankSearch.
Import ListNotations.

Definition Bq : nat := 2000.
Definition NGF : nat := 200000.
Definition NGR : nat := 512.

(* Decide.v [qhb_tmax] / [qh_candidate], Run.v's rungs *)
Definition tmaxP : nat := Eval vm_compute in fold_left Nat.max (map snd qhr) 0.

Definition qh_candidateP (tm : TM) (q : St) : bool :=
  match last_visit tm (4 * tmaxP) c0 0 q None with
  | Some s => s <? tmaxP
  | None => false
  end.

(* the (state, rung) pairs this tier actually attempts, per machine *)
Definition workP (tm : TM) : list (St * (nat * nat)) :=
  flat_map (fun q => map (fun nt => (q, nt)) qhr)
           (filter (qh_candidateP tm) all_St).

Fixpoint sumf {B : Type} (l : list B) (f : B -> nat) (acc : nat) : nat :=
  match l with [] => acc | x :: t => sumf t f (acc + f x) end.

Definition WK : list (TM * list (St * (nat * nat))) := Eval vm_compute in
  map (fun tm => (tm, workP tm)) grp_RES.

Definition total_work : nat := Eval vm_compute in
  sumf WK (fun p => List.length (snd p)) 0.

(* ---- the stages of ONE [try_qhb_lex_at] attempt ------------------ *)

(* A. everything up to the grown gram sets (the untrusted growth) *)
Definition st_grow (tm : TM) (q : St) (nt : nat * nat) : nat :=
  let '(n, t) := nt in
  match csteps tm t c0 with
  | None => 0
  | Some ct =>
      let tmw := tm_wrap tm q in
      let '(q1, (l, h, r)) := ct in
      let '(lset, rset) :=
        ng_grow tmw (ng_start n ct) NGF NGR
                (gadds (ng_seed_side n l) gempty)
                (gadds (ng_seed_side n r) gempty) in
      PositiveSet.cardinal lset + PositiveSet.cardinal rset
  end.

(* B. grow + the [ng_explore] closure the certificate search needs *)
Definition st_explore (tm : TM) (q : St) (nt : nat * nat) : nat :=
  let '(n, t) := nt in
  match csteps tm t c0 with
  | None => 0
  | Some ct =>
      let tmw := tm_wrap tm q in
      let '(q1, (l, h, r)) := ct in
      let a0 := ng_start n ct in
      let '(lset, rset) :=
        ng_grow tmw a0 NGF NGR
                (gadds (ng_seed_side n l) gempty)
                (gadds (ng_seed_side n r) gempty) in
      List.length (ng_explore tmw lset rset NGF [] PositiveSet.empty [a0])
  end.

(* C. grow + explore + the untrusted certificate search *)
Definition st_cert (tm : TM) (q : St) (nt : nat * nat) : nat :=
  let '(n, t) := nt in
  match csteps tm t c0 with
  | None => 0
  | Some ct =>
      let tmw := tm_wrap tm q in
      let '(q1, (l, h, r)) := ct in
      let a0 := ng_start n ct in
      let '(lset, rset) :=
        ng_grow tmw a0 NGF NGR
                (gadds (ng_seed_side n l) gempty)
                (gadds (ng_seed_side n r) gempty) in
      let cl := ng_explore tmw lset rset NGF [] PositiveSet.empty [a0] in
      sumf all_St (fun q' => List.length (rank_procedure tmw lset rset cl q')) 0
  end.

(* D. the WHOLE attempt, i.e. C plus the verified stage
   ([ngram_check_qhbound_lex], which re-runs [ng_grow] internally) *)
Definition st_all (tm : TM) (q : St) (nt : nat * nat) : nat :=
  if (let '(n, t) := nt in
      (S t <=? Bq) &&
      match last_visit tm t c0 0 q None with
      | None => false
      | Some s =>
          match csteps tm t c0 with
          | None => false
          | Some ct =>
              let tmw := tm_wrap tm q in
              let '(q1, (l, h, r)) := ct in
              let a0 := ng_start n ct in
              let '(lset, rset) :=
                ng_grow tmw a0 NGF NGR
                        (gadds (ng_seed_side n l) gempty)
                        (gadds (ng_seed_side n r) gempty) in
              let cl := ng_explore tmw lset rset NGF [] PositiveSet.empty [a0] in
              ngram_check_qhbound_lex tm q s n t NGF NGR
                (fun q' => rank_procedure tmw lset rset cl q')
          end
      end)
  then 1 else 0.

(* E. the PLAIN rung, for the tier split *)
Definition st_plain (tm : TM) (q : St) (nt : nat * nat) : nat :=
  if (let '(n, t) := nt in
      (S t <=? Bq) &&
      match last_visit tm t c0 0 q None with
      | Some s => ngram_check_qhbound tm q s n t NGF NGR
      | None => false
      end)
  then 1 else 0.

Definition over (f : TM -> St -> (nat * nat) -> nat) : nat :=
  sumf WK (fun p => sumf (snd p) (fun w => f (fst p) (fst w) (snd w)) 0) 0.

Eval vm_compute in List.length grp_RES.
Eval vm_compute in total_work.
Time Eval vm_compute in over st_grow.
Time Eval vm_compute in over st_explore.
Time Eval vm_compute in over st_cert.
Time Eval vm_compute in over st_all.
Time Eval vm_compute in over st_plain.
