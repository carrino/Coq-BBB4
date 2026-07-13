(** * Cycle_Examples: first end-to-end machine theorems.

    Two concrete 4-state machines from the (4,2) enumeration
    (bbchallenge text format, verified against the BBB harness), each
    decided by the relative-configuration cycle checker with
    [vm_compute]:

    - [tm_ex_neverqh] = 1RB0LC_0LA0LC_0LD0RD_1LA---
      enters a 4-step cycle after 8 steps whose window visits all four
      states: it never quasihalts at state level.  (At *transition*
      level this machine does quasihalt -- transitions A1, B0, C0 fire
      exactly once -- the standing example that the two levels differ;
      transition-level semantics is a later increment.)

    - [tm_ex_qh] = 1RB0LC_0LA0LC_0LD1RA_1LA---
      enters a 4-step cycle after 12 steps that avoids state D; D's
      last visit is configuration index 4 (its transition fires last
      at step 5, the machine's state-level score): a non-halting
      quasihalter with an exact last-visit index. *)

From Coq Require Import List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import Cycle.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB0LC_0LA0LC_0LD0RD_1LA--- *)
Definition tm_ex_neverqh : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StC
  | StB, S0 => mk S0 DL StA | StB, S1 => mk S0 DL StC
  | StC, S0 => mk S0 DL StD | StC, S1 => mk S0 DR StD
  | StD, S0 => mk S1 DL StA | StD, S1 => None
  end.

Theorem tm_ex_neverqh_never_quasihalts : NeverQuasiHaltsSt tm_ex_neverqh.
Proof.
  apply (cycle_check_neverqh_sound _ 8 4).
  vm_compute. reflexivity.
Qed.

Theorem tm_ex_neverqh_not_qh : ~ QuasiHaltsSt tm_ex_neverqh.
Proof. apply never_qh_not_qh, tm_ex_neverqh_never_quasihalts. Qed.

Theorem tm_ex_neverqh_nonhalt : NonHalt tm_ex_neverqh.
Proof. apply never_qh_nonhalt, tm_ex_neverqh_never_quasihalts. Qed.

(** 1RB0LC_0LA0LC_0LD1RA_1LA--- *)
Definition tm_ex_qh : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StC
  | StB, S0 => mk S0 DL StA | StB, S1 => mk S0 DL StC
  | StC, S0 => mk S0 DL StD | StC, S1 => mk S1 DR StA
  | StD, S0 => mk S1 DL StA | StD, S1 => None
  end.

Theorem tm_ex_qh_decided :
  NonHalt tm_ex_qh /\ QuietAfter tm_ex_qh StD 4 /\ QuasiHaltsSt tm_ex_qh.
Proof.
  apply (cycle_check_qh_sound _ 12 4 StD 4).
  vm_compute. reflexivity.
Qed.

Theorem tm_ex_qh_quasihalts_nonhalting :
  QuasiHaltsSt tm_ex_qh /\ NonHalt tm_ex_qh.
Proof.
  destruct tm_ex_qh_decided as (Hnh & _ & Hqh). auto.
Qed.
