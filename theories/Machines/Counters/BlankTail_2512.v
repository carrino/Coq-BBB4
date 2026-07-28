(** * BlankTail_2512: 1RB1RA_0RC1LA_1LC1LD_0RB0RD quasihalts at 2512.

    First board off [Counters.BlankTail].  Measured shape
    (`docs/RESIDUE_VISIT_MEASUREMENT.md` section 4b): after 2512 steps the
    machine is in [StC] on a completely blank tape, and [StC] on a blank
    reads [1LC] -- a self-loop.  So it marches left forever across virgin
    tape in one state, and [StA], [StB], [StD] are quiet from step 2512 on.

    Their last visits are therefore at configuration index < 2512, giving
    [QHBound 2512].  The bound is tight: [StA]'s last visit is at
    configuration index 2511.

    Note this machine cannot leave [D_census] through the [QHBound 2000]
    tier -- 2512 > 2000 -- no matter how strong the liveness argument gets.
    It is blocked by the CONSTANT, which is why the [B_final] predicate
    change is what unlocks it. *)

From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4 Require Import Census.TNF_QH.
From BBB4.Counters Require Import BlankTail.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB1RA_0RC1LA_1LC1LD_0RB0RD *)
Definition tm_2512 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DR StA
  | StB, S0 => mk S0 DR StC | StB, S1 => mk S1 DL StA
  | StC, S0 => mk S1 DL StC | StC, S1 => mk S1 DL StD
  | StD, S0 => mk S0 DR StB | StD, S1 => mk S0 DR StD
  end.

(** [StC] self-loops on a blank, travelling left. *)
Lemma tm_2512_selfloop : tm_2512 StC S0 = Some (mkTrans S1 DL StC).
Proof. reflexivity. Qed.

Theorem tm_2512_qhbound : QHBound 2512 tm_2512.
Proof.
  apply (qhbound_blank_tail_check tm_2512 StC S1 DL 2512 2512).
  - exact tm_2512_selfloop.
  - vm_compute. reflexivity.
  - lia.
Qed.

Print Assumptions tm_2512_qhbound.

(** The full census triple, for the closeout's explicit-bound stage entry
    (kind iqh_le): [StA] is visited at index 0 and quiet from the prefix on,
    and the blank-tail march never halts. *)
Definition iqh_le (B : nat) (tm : TM) : Prop :=
  NonHalt tm /\ QHBound B tm /\ QuasiHaltsSt tm.

Theorem tm_2512_board : iqh_le 2512 tm_2512.
Proof.
  apply (blank_tail_board tm_2512 StC S1 DL 2512 2512).
  - exact tm_2512_selfloop.
  - reflexivity.
  - vm_compute. reflexivity.
  - lia.
Qed.

Print Assumptions tm_2512_board.
