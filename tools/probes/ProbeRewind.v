(** STALE as of the exact-records/cycle-twin round: [lp_ent.lp_k]
    moved to binary [N] and the record rule was replaced, so this
    file no longer compiles against Decide.v.  It is kept as the
    measurement record for the andb-rewind round it validated
    (commit 8286251); do not re-run it against current sources. *)
(** Is [lp_rewind] really the quadratic term, and what does capping it
    cost?  (UNTRUSTED probe, not in _CoqProject.)

    ProbeScanSplit measures the 130 -> 512 rung at 13.4x for 4x the
    gas.  History length scales 4x, so a linear scan would give ~4x;
    the extra ~3.3x is consistent with [lp_scan]'s [lp_rewind] filter
    being O(P) per matched entry over an O(n) history.  "Consistent
    with" is not "measured", so: re-implement [lp_scan] with the
    rewind (a) as-is, (b) capped at K entries, (c) disabled, and time
    all three on the real translated-cycle sample.

    The rewind is a FILTER in front of the verified re-check, so
    weakening it cannot break soundness -- but it can change which
    candidates fill [lp_scan]'s 6 slots, hence which machines get
    caught.  So this also diffs the emitted candidate lists. *)

From Coq Require Import Arith Bool List ZArith.
From BBB4 Require Import BBB4_Statement CTape ProbeWalkCommon ProbeTierCost.
From BBB4.Census Require Import TNF_QH Decide.
Import ListNotations.

Definition g512 : nat := 512.

(** [lp_scan] with the rewind depth as a parameter.
    [rw = None] disables it; [rw = Some k] caps it at k entries. *)
Fixpoint rewind_cap (l0 l1 : list lp_ent) (n : nat) : bool :=
  match n with
  | 0 => true
  | S m =>
      match l0, l1 with
      | a :: l0', b :: l1' =>
          st_eqb (lp_q a) (lp_q b) && sym_eqb (lp_s a) (lp_s b)
          && rewind_cap l0' l1' m
      | _, _ => false
      end
  end.

Definition rw_filter (rw : option nat) (tl0 l1' : list lp_ent)
    (P k0 : nat) : bool :=
  match rw with
  | None => true
  | Some k =>
      if 2 * P <=? k0 then rewind_cap tl0 l1' (Nat.min P k) else true
  end.

Fixpoint lp_scan_v (rw : option nat) (h0 : lp_ent) (tl0 l1 : list lp_ent)
    (cap : nat) (acc : list lp_cand) : list lp_cand :=
  match l1 with
  | [] => rev acc
  | h1 :: l1' =>
      match cap with
      | 0 => rev acc
      | S cap' =>
          let P := lp_k h0 - lp_k h1 in
          if st_eqb (lp_q h0) (lp_q h1) && sym_eqb (lp_s h0) (lp_s h1)
             && rw_filter rw tl0 l1' P (lp_k h0)
          then
            match
              match Z.compare (lp_pos h0) (lp_pos h1) with
              | Eq => Some (fun n1 => LpCycle n1 P)
              | Gt => if lp_rrec h1 then Some (fun n1 => LpTC DR n1 P)
                      else None
              | Lt => if lp_lrec h1 then Some (fun n1 => LpTC DL n1 P)
                      else None
              end
            with
            | Some mk =>
                let n1 := lp_k h1 in
                let b := n1 mod P in
                let cs :=
                  if b + P <? n1 then [mk b; mk (b + P); mk n1]
                  else if b <? n1 then [mk b; mk n1]
                  else [mk n1] in
                lp_scan_v rw h0 tl0 l1' cap' (rev_append cs acc)
            | None => lp_scan_v rw h0 tl0 l1' (S cap') acc
            end
          else lp_scan_v rw h0 tl0 l1' (S cap') acc
      end
  end.

Definition cands_v (rw : option nat) (tm : TM) (gas : nat)
  : list lp_cand :=
  match lp_run tm gas 0 c0 0%Z [] with
  | [] => []
  | h0 :: tl => lp_scan_v rw h0 tl tl 6 []
  end.

(* the shipped scan, for the same anchor, as the reference *)
Definition cands_ref (tm : TM) (gas : nat) : list lp_cand :=
  cands_v (Some 1000000) tm gas.

Definition ncand (rw : option nat) (l : list TM) (gas : nat) : nat :=
  fold_left Nat.add
    (map (fun tm => List.length (cands_v rw tm gas)) l) 0.

(** ** timing: same machines, same gas, three rewind depths *)

Time Eval vm_compute in ncand (Some 1000000) grp_T g512.  (* as shipped *)
Time Eval vm_compute in ncand (Some 32) grp_T g512.        (* capped 32 *)
Time Eval vm_compute in ncand (Some 8) grp_T g512.         (* capped 8 *)
Time Eval vm_compute in ncand None grp_T g512.             (* disabled *)

(** ** divergence: does capping change the candidates? *)

Definition cand_eqb (a b : lp_cand) : bool :=
  match a, b with
  | LpCycle n p, LpCycle n' p' => (n =? n') && (p =? p')
  | LpTC d n p, LpTC d' n' p' =>
      (match d, d' with DR, DR | DL, DL => true | _, _ => false end)
      && (n =? n') && (p =? p')
  | _, _ => false
  end.

Fixpoint list_eqb (a b : list lp_cand) : bool :=
  match a, b with
  | [], [] => true
  | x :: t, y :: u => cand_eqb x y && list_eqb t u
  | _, _ => false
  end.

Definition diverge (rw : option nat) (l : list TM) (gas : nat) : nat :=
  List.length (filter (fun tm =>
    negb (list_eqb (cands_v rw tm gas) (cands_ref tm gas))) l).

(* machines whose candidate list changes, out of 40 *)
Eval vm_compute in (diverge (Some 32) grp_T g512,
                    diverge (Some 8) grp_T g512,
                    diverge None grp_T g512).

(* and what actually matters: does the VERDICT change? *)
Definition verdict (rw : option nat) (tm : TM) : bool :=
  existsb (lp_check Bc tm) (cands_v rw tm g512).

Definition verdict_diff (rw : option nat) (l : list TM) : nat :=
  List.length (filter (fun tm =>
    negb (Bool.eqb (verdict rw tm) (verdict (Some 1000000) tm))) l).

Eval vm_compute in (verdict_diff (Some 32) grp_T,
                    verdict_diff (Some 8) grp_T,
                    verdict_diff None grp_T).

(** ** The decisive number: generation PLUS verified re-checks

    [ncand] above times candidate GENERATION only.  Disabling the
    rewind makes generation 6.9x faster but emits 27% more candidates,
    and each one costs a verified re-simulation downstream -- so the
    net can go either way.  This times the whole [scan_loops]
    equivalent (existsb short-circuits, exactly as the decider does). *)

Definition verdicts (rw : option nat) (l : list TM) : nat :=
  List.length (filter (verdict rw) l).

Time Eval vm_compute in verdicts (Some 1000000) grp_T.  (* as shipped *)
Time Eval vm_compute in verdicts (Some 32) grp_T.
Time Eval vm_compute in verdicts (Some 8) grp_T.
Time Eval vm_compute in verdicts None grp_T.

(* same, on the in-place tier *)
Time Eval vm_compute in verdicts (Some 1000000) grp_C.
Time Eval vm_compute in verdicts (Some 32) grp_C.
Time Eval vm_compute in verdicts None grp_C.

(* and on the n-gram tier, where every machine fails the scan and so
   pays the FULL cost with no short-circuit *)
Time Eval vm_compute in verdicts (Some 1000000) grp_N6.
Time Eval vm_compute in verdicts (Some 32) grp_N6.
Time Eval vm_compute in verdicts None grp_N6.

Eval vm_compute in (verdict_diff (Some 32) grp_C, verdict_diff None grp_C,
                    verdict_diff (Some 32) grp_N6, verdict_diff None grp_N6).

(** ** The behaviour-preserving fix

    Coq's [&&] is [andb], a FUNCTION -- so under call-by-value both
    arguments are evaluated before the call.  [lp_rewind]'s

      st_eqb .. && sym_eqb .. && lp_rewind l0' l1' m

    therefore evaluates the recursive call even when the head compare
    has already failed: every rewind walks its full P entries no
    matter what.  That is the quadratic term, and it can be removed
    with NO semantic change at all by nesting the tests, which is the
    same boolean function with an early exit.  Unlike capping, this
    cannot alter a single candidate. *)

Fixpoint rewind_fast (l0 l1 : list lp_ent) (n : nat) : bool :=
  match n with
  | 0 => true
  | S m =>
      match l0, l1 with
      | a :: l0', b :: l1' =>
          if st_eqb (lp_q a) (lp_q b)
          then if sym_eqb (lp_s a) (lp_s b)
               then rewind_fast l0' l1' m
               else false
          else false
      | _, _ => false
      end
  end.

Fixpoint lp_scan_f (h0 : lp_ent) (tl0 l1 : list lp_ent)
    (cap : nat) (acc : list lp_cand) : list lp_cand :=
  match l1 with
  | [] => rev acc
  | h1 :: l1' =>
      match cap with
      | 0 => rev acc
      | S cap' =>
          let P := lp_k h0 - lp_k h1 in
          if (if st_eqb (lp_q h0) (lp_q h1)
              then if sym_eqb (lp_s h0) (lp_s h1)
                   then (if 2 * P <=? lp_k h0
                         then rewind_fast tl0 l1' P else true)
                   else false
              else false)
          then
            match
              match Z.compare (lp_pos h0) (lp_pos h1) with
              | Eq => Some (fun n1 => LpCycle n1 P)
              | Gt => if lp_rrec h1 then Some (fun n1 => LpTC DR n1 P)
                      else None
              | Lt => if lp_lrec h1 then Some (fun n1 => LpTC DL n1 P)
                      else None
              end
            with
            | Some mk =>
                let n1 := lp_k h1 in
                let b := n1 mod P in
                let cs :=
                  if b + P <? n1 then [mk b; mk (b + P); mk n1]
                  else if b <? n1 then [mk b; mk n1]
                  else [mk n1] in
                lp_scan_f h0 tl0 l1' cap' (rev_append cs acc)
            | None => lp_scan_f h0 tl0 l1' (S cap') acc
            end
          else lp_scan_f h0 tl0 l1' (S cap') acc
      end
  end.

Definition cands_f (tm : TM) (gas : nat) : list lp_cand :=
  match lp_run tm gas 0 c0 0%Z [] with
  | [] => []
  | h0 :: tl => lp_scan_f h0 tl tl 6 []
  end.

(* candidate lists must be bit-identical to the shipped scan *)
Definition fast_diverge (l : list TM) (gas : nat) : nat :=
  List.length (filter (fun tm =>
    negb (list_eqb (cands_f tm gas) (cands_ref tm gas))) l).

Eval vm_compute in (fast_diverge grp_T g512, fast_diverge grp_C g512,
                    fast_diverge grp_N6 g512).

Definition verdict_f (tm : TM) : bool :=
  existsb (lp_check Bc tm) (cands_f tm g512).
Definition verdicts_f (l : list TM) : nat :=
  List.length (filter verdict_f l).

Time Eval vm_compute in verdicts (Some 1000000) grp_T.
Time Eval vm_compute in verdicts_f grp_T.
Time Eval vm_compute in verdicts (Some 1000000) grp_N6.
Time Eval vm_compute in verdicts_f grp_N6.
