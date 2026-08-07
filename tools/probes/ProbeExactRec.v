(* Validation gate for the scan_ct deletion.
   1. lp_records must equal scan_records EXACTLY (N->nat) per machine;
   2. every ct-only machine must now be caught by the one-pass;
   3. the new scan block's catches must be a superset of the old
      (loops130 | loops512 | scan_ct) on the whole big sample. *)
From Coq Require Import Arith Bool List NArith ZArith.
From BBB4 Require Import BBB4_Statement CTape ProbeWalkCommon ProbeTierBig.
From BBB4.Census Require Import TNF_QH Decide.
Import ListNotations.

Definition g130 : nat := 130.
Definition g512 : nat := 512.

(* -- 1: record-list equality ------------------------------------- *)
Fixpoint recs_eq (a : list (N * St)) (b : list (nat * St)) : bool :=
  match a, b with
  | [], [] => true
  | (ka, qa) :: ta, (kb, qb) :: tb =>
      Nat.eqb (N.to_nat ka) kb && st_eqb qa qb && recs_eq ta tb
  | _, _ => false
  end.

Definition records_agree (tm : TM) (gas : nat) : bool :=
  let hist := lp_run tm gas 0%N c0 0%Z [] in
  let '(rR, rL) := lp_records tm hist in
  let '(sR, sL) := scan_records tm gas in
  recs_eq rR sR && recs_eq rL sL.

Definition agree_count (l : list TM) (gas : nat) : nat :=
  List.length (filter (fun tm => records_agree tm gas) l).

Eval vm_compute in
  (agree_count grp_T g512, agree_count grp_C g512,
   agree_count grp_N6 g512, agree_count grp_T g130).

(* -- 2 & 3: verdict superset ------------------------------------- *)
Definition old_block (tm : TM) : bool :=
  (* the pre-deletion pipeline: both one-pass rungs (with the OLD
     approximate rec rule now gone -- so re-check via scan_ct too) *)
  scan_loops Bc tm g130 || scan_loops Bc tm g512 || scan_ct Bc tm g512.
Definition new_block (tm : TM) : bool :=
  scan_loops Bc tm g130 || scan_loops Bc tm g512.

(* machines the old block catches that the new one misses: MUST be 0 *)
Definition lost (l : list TM) : nat :=
  List.length (filter (fun tm => old_block tm && negb (new_block tm)) l).

Eval vm_compute in (lost grp_T, lost grp_C, lost grp_N6).

(* gained is fine (strictly more catches = fewer ladder pops) *)
Definition gained (l : list TM) : nat :=
  List.length (filter (fun tm => new_block tm && negb (old_block tm)) l).
Eval vm_compute in (gained grp_T, gained grp_C, gained grp_N6).
