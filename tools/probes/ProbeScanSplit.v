(** NOTE (exact-records round): [scan_ct] has since been DELETED from
    [decide_easy] -- the definition survives for A/B probes like this
    one, but the pipeline timings below predate the deletion. *)
(** Why does the translated-cycle tier cost ~3x the in-place one?
    (UNTRUSTED probe, not in _CoqProject.)

    T is 2,282,976 of the census's 3,995,005 nodes, so by Amdahl it is
    THE target.  [decide_easy] runs, in order:

      scan_loops tm 130   (lp_run 130 steps, backward scan, verified
                           re-check of each candidate)
      scan_loops tm 512   (lp_run AGAIN from scratch, 512 steps)
      scan_ct    tm 512   (the old block: scan_cycle's per-step
                           rolling hash + PositiveMap insert, plus a
                           separate scan_records walk)

    so anything not caught at 130 re-simulates its first 130 steps.
    This splits each rung into SIMULATION+SCAN ([lp_candidates], no
    verified checks) versus VERIFICATION ([scan_loops] = the same plus
    [lp_check] per candidate), on the same real machines the tier-cost
    probe sampled. *)

From Coq Require Import Arith Bool List ZArith.
From BBB4 Require Import BBB4_Statement CTape ProbeWalkCommon ProbeTierCost.
From BBB4.Census Require Import TNF_QH Decide.
Import ListNotations.

(* Run.v's gas rungs, as ProbeWalkCommon instantiates them *)
Definition g130 : nat := 130.
Definition g512 : nat := 512.

Definition ncands (tm : TM) (gas : nat) : nat :=
  List.length (lp_candidates tm gas).

(* how many of each group are caught at the CHEAP rung vs only at the
   full rung vs not at all -- the shape that decides whether the
   double pass is worth removing *)
Definition caught130 (l : list TM) : nat :=
  List.length (filter (fun tm => scan_loops Bc tm g130) l).
Definition caught512 (l : list TM) : nat :=
  List.length (filter (fun tm => scan_loops Bc tm g512) l).

(* (caught@130, caught@512, total) *)
Eval vm_compute in
  (caught130 grp_T, caught512 grp_T, List.length grp_T).
Eval vm_compute in
  (caught130 grp_C, caught512 grp_C, List.length grp_C).

(* candidate counts: how much verified re-checking each rung triggers *)
Eval vm_compute in
  (fold_left Nat.add (map (fun tm => ncands tm g130) grp_T) 0,
   fold_left Nat.add (map (fun tm => ncands tm g512) grp_T) 0).

(** ** simulation+scan versus verification, per rung *)

Definition sim_only (l : list TM) (gas : nat) : nat :=
  fold_left Nat.add (map (fun tm => ncands tm gas) l) 0.
Definition full (l : list TM) (gas : nat) : nat :=
  List.length (filter (fun tm => scan_loops Bc tm gas) l).

(* T tier *)
Time Eval vm_compute in sim_only grp_T g130.   (* lp_run 130 + scan *)
Time Eval vm_compute in full     grp_T g130.   (* + verified checks *)
Time Eval vm_compute in sim_only grp_T g512.   (* lp_run 512 + scan *)
Time Eval vm_compute in full     grp_T g512.   (* + verified checks *)

(* C tier, for contrast *)
Time Eval vm_compute in sim_only grp_C g130.
Time Eval vm_compute in full     grp_C g130.

(* the old fallback block, on machines that reach it (n-gram tier):
   this is the per-step hash + PositiveMap insert path *)
Time Eval vm_compute in
  (List.length (filter (fun tm => scan_ct Bc tm g512) grp_N2)).
Time Eval vm_compute in
  (List.length (filter (fun tm => scan_loops Bc tm g512) grp_N2)).

(** ** The decisive question for the bulk

    [scan_ct] is the OLD block (scan_cycle's per-step rolling hash +
    PositiveMap insert, plus a separate scan_records walk) and it
    measures ~42 ms/machine against ~18 ms for scan_loops@512 and
    ~1.8 ms for scan_loops@130.  Every machine that reaches the ladder
    pays it.  It is kept only as "a full-gas fallback so no catch is
    lost" -- so: does it ever catch a machine BOTH one-pass rungs
    miss? *)

Definition reaches_ct (tm : TM) : bool :=
  negb (scan_loops Bc tm g130) && negb (scan_loops Bc tm g512).

Definition ct_saves (l : list TM) : nat :=
  List.length (filter (fun tm => reaches_ct tm && scan_ct Bc tm g512) l).
Definition reach_n (l : list TM) : nat :=
  List.length (filter reaches_ct l).

(* per tier: (machines reaching scan_ct, of those caught ONLY by it) *)
Eval vm_compute in (reach_n grp_C, ct_saves grp_C).
Eval vm_compute in (reach_n grp_T, ct_saves grp_T).
Eval vm_compute in (reach_n grp_H, ct_saves grp_H).
Eval vm_compute in (reach_n grp_N2, ct_saves grp_N2).
Eval vm_compute in (reach_n grp_N3, ct_saves grp_N3).
Eval vm_compute in (reach_n grp_N4, ct_saves grp_N4).
Eval vm_compute in (reach_n grp_N6, ct_saves grp_N6).
