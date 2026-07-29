(** * BlankTail_66349: 1RB0LD_1LC0LA_1LA0LC_1RD1RC quasihalts at 66349.

    Board off [Counters.BlankTail].  After 66349 steps the machine is in [StD]
    with the half-tape ahead blank, and [StD] on a blank reads a SELF-LOOP,
    so it marches off across virgin tape forever in one state.  The other
    three states are quiet from step 66349 on, giving [QHBound 66349]. *)

From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4 Require Import Census.TNF_QH.
From BBB4.Counters Require Import BlankTail.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB0LD_1LC0LA_1LA0LC_1RD1RC *)
Definition tm_66349 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StD
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DL StA
  | StC, S0 => mk S1 DL StA | StC, S1 => mk S0 DL StC
  | StD, S0 => mk S1 DR StD | StD, S1 => mk S1 DR StC
  end.

Lemma tm_66349_selfloop : tm_66349 StD S0 = Some (mkTrans S1 DR StD).
Proof. reflexivity. Qed.

Theorem tm_66349_qhbound : QHBound 66349 tm_66349.
Proof.
  apply (qhbound_blank_tail_check tm_66349 StD S1 DR 66349 66349).
  - exact tm_66349_selfloop.
  - vm_compute. reflexivity.
  - lia.
Qed.

Print Assumptions tm_66349_qhbound.

(** The full census triple, for the closeout's explicit-bound stage entry
    (kind iqh_le): [StA] is visited at index 0 and quiet from the prefix on,
    and the blank-tail march never halts. *)
Definition iqh_le (B : nat) (tm : TM) : Prop :=
  NonHalt tm /\ QHBound B tm /\ QuasiHaltsSt tm.

Theorem tm_66349_board : iqh_le 66349 tm_66349.
Proof.
  apply (blank_tail_board tm_66349 StD S1 DR 66349 66349).
  - exact tm_66349_selfloop.
  - reflexivity.
  - vm_compute. reflexivity.
  - lia.
Qed.

Print Assumptions tm_66349_board.
