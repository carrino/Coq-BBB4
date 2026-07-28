(** * BlankTail_2819: 1RB1RC_1LC1RD_1RA1LD_0RD0LB quasihalts at 2819.

    Board off [Counters.BlankTail].  After 2819 steps the machine is in [StD]
    with the half-tape ahead blank, and [StD] on a blank reads a SELF-LOOP,
    so it marches off across virgin tape forever in one state.  The other
    three states are quiet from step 2819 on, giving [QHBound 2819]. *)

From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4 Require Import Census.TNF_QH.
From BBB4.Counters Require Import BlankTail.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB1RC_1LC1RD_1RA1LD_0RD0LB *)
Definition tm_2819 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DR StC
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S1 DR StA | StC, S1 => mk S1 DL StD
  | StD, S0 => mk S0 DR StD | StD, S1 => mk S0 DL StB
  end.

Lemma tm_2819_selfloop : tm_2819 StD S0 = Some (mkTrans S0 DR StD).
Proof. reflexivity. Qed.

Theorem tm_2819_qhbound : QHBound 2819 tm_2819.
Proof.
  apply (qhbound_blank_tail_check tm_2819 StD S0 DR 2819 2819).
  - exact tm_2819_selfloop.
  - vm_compute. reflexivity.
  - lia.
Qed.

Print Assumptions tm_2819_qhbound.

(** The full census triple, for the closeout's explicit-bound stage entry
    (kind iqh_le): [StA] is visited at index 0 and quiet from the prefix on,
    and the blank-tail march never halts. *)
Definition iqh_le (B : nat) (tm : TM) : Prop :=
  NonHalt tm /\ QHBound B tm /\ QuasiHaltsSt tm.

Theorem tm_2819_board : iqh_le 2819 tm_2819.
Proof.
  apply (blank_tail_board tm_2819 StD S0 DR 2819 2819).
  - exact tm_2819_selfloop.
  - reflexivity.
  - vm_compute. reflexivity.
  - lia.
Qed.

Print Assumptions tm_2819_board.
