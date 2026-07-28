(** * BlankTail_2568: 1RB1RA_0RC0RB_0RD1RA_1LD1LB quasihalts at 2568.

    Board off [Counters.BlankTail].  After 2568 steps the machine is in [StD]
    with the half-tape ahead blank, and [StD] on a blank reads a SELF-LOOP,
    so it marches off across virgin tape forever in one state.  The other
    three states are quiet from step 2568 on, giving [QHBound 2568]. *)

From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4 Require Import Census.TNF_QH.
From BBB4.Counters Require Import BlankTail.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB1RA_0RC0RB_0RD1RA_1LD1LB *)
Definition tm_2568 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DR StA
  | StB, S0 => mk S0 DR StC | StB, S1 => mk S0 DR StB
  | StC, S0 => mk S0 DR StD | StC, S1 => mk S1 DR StA
  | StD, S0 => mk S1 DL StD | StD, S1 => mk S1 DL StB
  end.

Lemma tm_2568_selfloop : tm_2568 StD S0 = Some (mkTrans S1 DL StD).
Proof. reflexivity. Qed.

Theorem tm_2568_qhbound : QHBound 2568 tm_2568.
Proof.
  apply (qhbound_blank_tail_check tm_2568 StD S1 DL 2568 2568).
  - exact tm_2568_selfloop.
  - vm_compute. reflexivity.
  - lia.
Qed.

Print Assumptions tm_2568_qhbound.

(** The full census triple, for the closeout's explicit-bound stage entry
    (kind iqh_le): [StA] is visited at index 0 and quiet from the prefix on,
    and the blank-tail march never halts. *)
Definition iqh_le (B : nat) (tm : TM) : Prop :=
  NonHalt tm /\ QHBound B tm /\ QuasiHaltsSt tm.

Theorem tm_2568_board : iqh_le 2568 tm_2568.
Proof.
  apply (blank_tail_board tm_2568 StD S1 DL 2568 2568).
  - exact tm_2568_selfloop.
  - reflexivity.
  - vm_compute. reflexivity.
  - lia.
Qed.

Print Assumptions tm_2568_board.
