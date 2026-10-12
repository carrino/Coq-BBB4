(** The short-circuit instruction checks must preserve successful checks,
    reject bad successors/liveness, and preserve prefix-fire semantics. *)
From Coq Require Import Arith Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.CensusTr Require Import DecideTr.
Import ListNotations.

(** The old strict prefix scan, retained only for a universal equivalence
    check. This covers early hits, late hits, halting and absent targets. *)
Fixpoint cfires_eager (tm : TM) (c : cconf) (len : nat) (tg : Instr) : bool :=
  match len with
  | 0 => false
  | S m => instr_eqb (cinstr c) tg ||
      match cstep tm c with
      | Some c' => cfires_eager tm c' m tg
      | None => false
      end
  end.

Lemma cfires_short_equiv : forall tm len c tg,
  cfires tm c len tg = cfires_eager tm c len tg.
Proof.
  intros tm len. induction len as [|len IH]; intros c tg; simpl.
  - reflexivity.
  - destruct (instr_eqb (cinstr c) tg); [reflexivity|].
    destruct (cstep tm c); [apply IH|reflexivity].
Qed.

(** All eight instructions in a cycle: every target's rank check passes.
    A self-loop added at node zero creates an infinite path avoiding the
    other seven targets, while a missing successor breaks closedness. *)
Definition enc (n : nat) := Pos.of_nat (S n).
Definition instruction (n : nat) := nth n all_Instr (StA, S0).
Definition cycle_succs (n : nat) : option (list nat) :=
  Some [(S n) mod 8].
Definition bypass_succs (n : nat) : option (list nat) :=
  if Nat.eqb n 0 then Some [0; 1] else cycle_succs n.
Definition broken_succs (n : nat) : option (list nat) :=
  if Nat.eqb n 7 then None else cycle_succs n.

Example cycle_live_vm :
  live_ok_tr nat enc instruction cycle_succs (seq 0 8) = true.
Proof. vm_compute. reflexivity. Qed.

Example cycle_live_native :
  live_ok_tr nat enc instruction cycle_succs (seq 0 8) = true.
Proof. native_compute. reflexivity. Qed.

Example reject_bypass_vm :
  live_ok_tr nat enc instruction bypass_succs (seq 0 8) = false.
Proof. vm_compute. reflexivity. Qed.

Example reject_bypass_native :
  live_ok_tr nat enc instruction bypass_succs (seq 0 8) = false.
Proof. native_compute. reflexivity. Qed.

Example reject_missing_successor :
  closed_tr_b nat enc broken_succs (seq 0 8) = false.
Proof. vm_compute. reflexivity. Qed.

Example reject_missing_node :
  closed_tr_b nat enc cycle_succs (seq 0 7) = false.
Proof. native_compute. reflexivity. Qed.

Example reject_empty_lex_certificate :
  live_lex_ok_tr nat enc instruction bypass_succs (seq 0 8)
    (fun _ => []) = false.
Proof. native_compute. reflexivity. Qed.

Print Assumptions allb_tr_eq.
Print Assumptions cfires_short_equiv.
Print Assumptions last_fires_spec.
Print Assumptions qh_last_fires_spec.
Print Assumptions closure_check_neverqhtr_sound.
Print Assumptions closure_check_neverqhtr_lex_sound.
Print Assumptions decide_easy_tr_WF.
