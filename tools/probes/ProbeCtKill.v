(** Can a widened one-pass subsume scan_ct?  (UNTRUSTED, scratch.)

    scan_ct (the old rolling-hash + PositiveMap-snapshot block) costs
    42.6 ms and runs on every machine that survives both one-pass
    rungs -- by the census-weighted model that is ~half of ALL
    remaining decider time.  It survives because it still catches
    machines the one-pass misses (4/40 T, 3/40 C in the small sample).
    The one-pass has two hard-coded width limits: lp_scan's candidate
    cap (6) and lp_rec_cands' records-per-side (2).  This measures, on
    the 1,440-machine sample:

      1. how many machines are caught ONLY by scan_ct;
      2. whether cap/recs widenings catch every one of them;
      3. what the widenings cost on ladder-bound machines (which pay
         all candidate checks with no short-circuit). *)

From Coq Require Import Arith Bool List NArith ZArith.
From BBB4 Require Import BBB4_Statement CTape ProbeWalkCommon ProbeTierBig.
From BBB4.Census Require Import TNF_QH Decide.
Import ListNotations.

Definition g130 : nat := 130.
Definition g512 : nat := 512.

(* the machines scan_ct alone catches *)
Definition ct_only (tm : TM) : bool :=
  if scan_loops Bc tm g130 then false
  else if scan_loops Bc tm g512 then false
  else scan_ct Bc tm g512.

(* lp_rec_cands with the records-per-side as a parameter *)
Definition rec_cands_n (n : nat) (hist : list lp_ent) (side : bool)
  : list lp_cand :=
  let d := if side then DR else DL in
  concat (map (fun e =>
    match lp_first_same (lp_q e)
            (filter (fun e' => N.ltb (lp_k e') (lp_k e)) hist) side with
    | Some a => [LpTC d (N.to_nat a) (N.to_nat (N.sub (lp_k e) a))]
    | None => []
    end) (lp_recs hist side n)).

(* the one-pass with both knobs as parameters *)
Definition cands_wide (cap recs : nat) (tm : TM) (gas : nat)
  : list lp_cand :=
  match lp_run tm gas 0%N c0 0%Z [] with
  | [] => []
  | h0 :: tl =>
      lp_scan h0 tl tl cap []
      ++ rec_cands_n recs (h0 :: tl) true
      ++ rec_cands_n recs (h0 :: tl) false
  end.

Definition wide_catches (cap recs : nat) (tm : TM) : bool :=
  existsb (lp_check Bc tm) (cands_wide cap recs tm g512).

(* -- 1: the ct-only population, per tier ------------------------- *)
Definition ct_T : list TM := Eval vm_compute in filter ct_only grp_T.
Definition ct_C : list TM := Eval vm_compute in filter ct_only grp_C.
Definition ct_N6 : list TM := Eval vm_compute in filter ct_only grp_N6.
Eval vm_compute in (List.length ct_T, List.length ct_C, List.length ct_N6).

(* -- 2: coverage of the ct-only machines by each widening -------- *)
Definition covered (cap recs : nat) (l : list TM) : nat :=
  List.length (filter (wide_catches cap recs) l).

(* current knobs, for reference: cap 6, recs 2 *)
Eval vm_compute in
  (covered 6 2 ct_T, covered 24 2 ct_T, covered 6 8 ct_T,
   covered 24 8 ct_T, covered 96 32 ct_T).
Eval vm_compute in
  (covered 6 2 ct_C, covered 24 2 ct_C, covered 6 8 ct_C,
   covered 24 8 ct_C, covered 96 32 ct_C).
Eval vm_compute in
  (covered 6 2 ct_N6, covered 24 8 ct_N6, covered 96 32 ct_N6).

(* which half does the catching: scan with big cap alone, or recs? *)
Definition scan_part (cap : nat) (tm : TM) : bool :=
  match lp_run tm g512 0%N c0 0%Z [] with
  | [] => false
  | h0 :: tl => existsb (lp_check Bc tm) (lp_scan h0 tl tl cap [])
  end.
Definition rec_part (recs : nat) (tm : TM) : bool :=
  match lp_run tm g512 0%N c0 0%Z [] with
  | [] => false
  | h0 :: tl =>
      existsb (lp_check Bc tm)
        (rec_cands_n recs (h0 :: tl) true
         ++ rec_cands_n recs (h0 :: tl) false)
  end.
Eval vm_compute in
  (List.length (filter (scan_part 96) ct_T),
   List.length (filter (rec_part 32) ct_T),
   List.length (filter (scan_part 96) ct_C),
   List.length (filter (rec_part 32) ct_C)).

(* -- 3: cost of the widening where it hurts most ----------------- *)
(* ladder-bound machines pay every candidate check; T machines are
   the bulk.  Compare per-machine scan cost at the candidate knobs. *)
Fixpoint repv (k : nat) (cap recs : nat) (l : list TM) (acc : bool)
  : bool :=
  match k with
  | O => acc
  | S j => repv j cap recs l
             (acc && Nat.leb 0 (List.length (filter (wide_catches cap recs) l)))
  end.
Time Eval vm_compute in repv 1 6 2 grp_N6 true.
Time Eval vm_compute in repv 1 24 8 grp_N6 true.
Time Eval vm_compute in repv 1 96 32 grp_N6 true.
Time Eval vm_compute in repv 1 6 2 grp_T true.
Time Eval vm_compute in repv 1 24 8 grp_T true.
Time Eval vm_compute in repv 1 96 32 grp_T true.
