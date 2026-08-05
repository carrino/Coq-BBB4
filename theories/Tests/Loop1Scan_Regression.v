(** * Loop1Scan_Regression: the one-pass scan's early-exit rewrite is
      semantics-preserving.

    [lp_rewind] and [lp_scan]'s guard were written with [&&].  Coq's
    [&&] is [andb], a FUNCTION, so under call-by-value both arguments
    are evaluated: the rewind ran to its full depth even when the head
    comparison had already failed, and it ran for EVERY history entry
    even when the state or symbol already differed.  That is an O(n)
    rewind per entry over an O(n) history -- the quadratic that made
    the gas-512 rung cost 13.4x the gas-130 rung for 4x the gas
    (docs/CENSUS_RUNTIME.md).

    Both were rewritten with nested [if]s.  That is the same boolean
    function, so no candidate, no catch and no census result may
    change -- and this file pins exactly that, against reference
    copies of the original [&&] forms.  If someone "simplifies" the
    nested ifs back to [&&], these still pass (they are equal); what
    they protect against is a rewrite that changes the CONDITION. *)

From Coq Require Import Arith Bool List NArith ZArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import Decide.
Import ListNotations.

(** ** Reference copies of the original [&&] forms *)

Fixpoint lp_rewind_ref (l0 l1 : list lp_ent) (n : N) : bool :=
  match l0, l1 with
  | a :: l0', b :: l1' =>
      if N.eqb n 0 then true
      else st_eqb (lp_q a) (lp_q b) && sym_eqb (lp_s a) (lp_s b)
           && lp_rewind_ref l0' l1' (N.pred n)
  | _, _ => N.eqb n 0
  end.

Lemma lp_rewind_eq : forall l0 l1 n,
  lp_rewind l0 l1 n = lp_rewind_ref l0 l1 n.
Proof.
  induction l0 as [|a l0' IH]; intros l1 n;
    destruct l1 as [|b l1']; try reflexivity.
  cbn [lp_rewind lp_rewind_ref].
  destruct (N.eqb n 0); [reflexivity|].
  destruct (st_eqb (lp_q a) (lp_q b)); cbn [andb]; [|reflexivity].
  destruct (sym_eqb (lp_s a) (lp_s b)); cbn [andb]; [|reflexivity].
  apply IH.
Qed.

(** The scan guard, in its original form. *)
Definition lp_guard_ref (h0 h1 : lp_ent) (tl0 l1' : list lp_ent) : bool :=
  let P := N.sub (lp_k h0) (lp_k h1) in
  st_eqb (lp_q h0) (lp_q h1) && sym_eqb (lp_s h0) (lp_s h1)
  && (if N.leb (N.mul 2 P) (lp_k h0) then lp_rewind_ref tl0 l1' P
      else true).

(** [lp_guard] is what [lp_scan] now calls. *)
Lemma lp_guard_eq : forall h0 h1 tl0 l1',
  lp_guard h0 h1 tl0 l1' = lp_guard_ref h0 h1 tl0 l1'.
Proof.
  intros h0 h1 tl0 l1'.
  unfold lp_guard, lp_guard_ref.
  destruct (st_eqb (lp_q h0) (lp_q h1)); cbn [andb]; [|reflexivity].
  destruct (sym_eqb (lp_s h0) (lp_s h1)); cbn [andb]; [|reflexivity].
  rewrite lp_rewind_eq. reflexivity.
Qed.

(** ** The whole scan, against a reference built on the old guard *)

Fixpoint lp_scan_ref (h0 : lp_ent) (tl0 l1 : list lp_ent) (cap : nat)
    (acc : list lp_cand) : list lp_cand :=
  match l1 with
  | [] => rev acc
  | h1 :: l1' =>
      match cap with
      | 0 => rev acc
      | S cap' =>
          let P := N.sub (lp_k h0) (lp_k h1) in
          if lp_guard_ref h0 h1 tl0 l1'
          then
            match
              match Z.compare (lp_pos h0) (lp_pos h1) with
              | Eq => Some (fun n1 => LpCycle n1 (N.to_nat P))
              | Gt => if lp_rrec h1
                      then Some (fun n1 => LpTC DR n1 (N.to_nat P))
                      else None
              | Lt => if lp_lrec h1
                      then Some (fun n1 => LpTC DL n1 (N.to_nat P))
                      else None
              end
            with
            | Some mk =>
                let n1 := lp_k h1 in
                let b := if N.eqb P 0 then n1 else N.modulo n1 P in
                let mkn := fun x : N => mk (N.to_nat x) in
                let cs :=
                  if N.ltb (N.add b P) n1
                  then [mkn b; mkn (N.add b P); mkn n1]
                  else if N.ltb b n1 then [mkn b; mkn n1]
                  else [mkn n1] in
                lp_scan_ref h0 tl0 l1' cap' (rev_append cs acc)
            | None => lp_scan_ref h0 tl0 l1' (S cap') acc
            end
          else lp_scan_ref h0 tl0 l1' (S cap') acc
      end
  end.

Lemma lp_scan_eq : forall l1 h0 tl0 cap acc,
  lp_scan h0 tl0 l1 cap acc = lp_scan_ref h0 tl0 l1 cap acc.
Proof.
  induction l1 as [|h1 l1' IH]; intros h0 tl0 cap acc; [reflexivity|].
  destruct cap as [|cap']; [reflexivity|].
  cbn [lp_scan lp_scan_ref].
  rewrite (lp_guard_eq h0 h1 tl0 l1').
  destruct (lp_guard_ref h0 h1 tl0 l1');
    [| apply IH].
  repeat (match goal with
          | |- context [match Z.compare ?a ?b with _ => _ end] =>
              destruct (Z.compare a b)
          | |- context [if lp_rrec ?e then _ else _] => destruct (lp_rrec e)
          | |- context [if lp_lrec ?e then _ else _] => destruct (lp_lrec e)
          | |- context [if ?c then _ else _] => destruct c
          end); apply IH.
Qed.

(** so the candidate lists the decider sees are unchanged *)
Theorem lp_candidates_unchanged : forall tm gas,
  lp_candidates tm gas
  = match lp_run tm gas 0%N c0 0%Z [] with
    | [] => []
    | h0 :: tl =>
        lp_scan_ref h0 tl tl 6 []
        ++ lp_rec_cands (h0 :: tl) true
        ++ lp_rec_cands (h0 :: tl) false
    end.
Proof.
  intros tm gas. unfold lp_candidates.
  destruct (lp_run tm gas 0%N c0 0%Z []) as [|h0 tl]; [reflexivity|].
  rewrite lp_scan_eq. reflexivity.
Qed.

Print Assumptions lp_candidates_unchanged.
