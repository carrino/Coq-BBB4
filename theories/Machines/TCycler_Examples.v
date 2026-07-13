(** * TCycler_Examples: translated-cycler machine theorems.

    Machines from the (4,2) enumeration (parameters verified against
    the BBB harness).  All three are left-moving translated cyclers
    (side L), so the right-handed checker runs on the mirrored
    machine and the result transfers through the [Mirror] lemmas.

    - [tm_tc_neverqh] = 1RB0LC_0LA---_0LD---_0LB---
      translated cycler (anchor 771, period 6, reach 0) whose lap
      visits all four states: never quasihalts at state level.

    - [tm_tc_qh] = 1RB0LC_0LA---_0LD---_1RC0LC
      translated cycler (anchor 1027, period 4, reach 0) whose lap
      avoids states A and B; A is last visited at configuration
      index 2: a non-halting quasihalter.

    - [tm_bbb_sample] = 1RB1LD_1LC0LD_1RC1RA_0LB0RA
      the BBB harness README's worked example: translated cycler
      with anchor 2,487,033, period 17,620 steps (118 records),
      reach 91.  All eight transitions fire infinitely often, so it
      never quasihalts.  This is the machine whose C certificate is
      shipped as tests/known_tcycler.txt upstream. *)

From Coq Require Import List.
From BBB4 Require Import BBB4_Statement CTape GTape Mirror.
From BBB4.Checkers Require Import TCycler.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB0LC_0LA---_0LD---_0LB--- *)
Definition tm_tc_neverqh : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StC
  | StB, S0 => mk S0 DL StA | StB, S1 => None
  | StC, S0 => mk S0 DL StD | StC, S1 => None
  | StD, S0 => mk S0 DL StB | StD, S1 => None
  end.

Theorem tm_tc_neverqh_never_quasihalts : NeverQuasiHaltsSt tm_tc_neverqh.
Proof.
  apply (tcycler_check_neverqh_sound_L _ 771 6 0).
  vm_compute. reflexivity.
Qed.

Theorem tm_tc_neverqh_nonhalt : NonHalt tm_tc_neverqh.
Proof. apply never_qh_nonhalt, tm_tc_neverqh_never_quasihalts. Qed.

(** 1RB0LC_0LA---_0LD---_1RC0LC *)
Definition tm_tc_qh : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StC
  | StB, S0 => mk S0 DL StA | StB, S1 => None
  | StC, S0 => mk S0 DL StD | StC, S1 => None
  | StD, S0 => mk S1 DR StC | StD, S1 => mk S0 DL StC
  end.

Theorem tm_tc_qh_decided :
  NonHalt tm_tc_qh /\ QuietAfter tm_tc_qh StA 2 /\ QuasiHaltsSt tm_tc_qh.
Proof.
  apply (tcycler_check_qh_sound_L _ 1027 4 0 StA 2).
  vm_compute. reflexivity.
Qed.

(** 1RB1LD_1LC0LD_1RC1RA_0LB0RA -- the BBB README sample machine.
    Parameters straight from its C certificate: anchor_step 2487033,
    period_steps 17620, reach 91, side L.  The [vm_compute] here
    re-simulates the 2.5M-step prefix and the 17,620-step guarded lap
    (about 15 seconds). *)
Definition tm_bbb_sample : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StD
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DL StD
  | StC, S0 => mk S1 DR StC | StC, S1 => mk S1 DR StA
  | StD, S0 => mk S0 DL StB | StD, S1 => mk S0 DR StA
  end.

Theorem tm_bbb_sample_never_quasihalts : NeverQuasiHaltsSt tm_bbb_sample.
Proof.
  apply (tcycler_check_neverqh_sound_L _ 2487033 17620 91).
  vm_compute. reflexivity.
Qed.

Theorem tm_bbb_sample_nonhalt : NonHalt tm_bbb_sample.
Proof. apply never_qh_nonhalt, tm_bbb_sample_never_quasihalts. Qed.
