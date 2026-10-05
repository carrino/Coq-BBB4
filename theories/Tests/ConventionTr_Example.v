(** * ConventionTr_Example: the harness's own example of the two conventions.

    The BBB harness README (carrino/BBB, "The two levels give different
    censuses") gives the (2,2) machine [1RB1LA_0LA1RA]: a translated
    cycler whose transition B0 fires exactly twice, last at step 7,
    while both states are visited forever -- so it quasihalts at
    TRANSITION level with score 7 but does NOT quasihalt at state level.

    This file checks that BBB4_Statement.v / BBBT4_Statement.v say the
    same about it (as a (4,2) table with C and D unused), through the
    existing translated-cycler checkers (left-moving variants: the
    machine translates left):

    - [example_qh_tr]:    [QuasiHaltsTr]                        (quasihalts)
    - [example_not_qh_st]: [~ QuasiHaltsSt]                     (but not at state level)
    - [example_B0_step7]: instruction (B, 0) fires at configuration index
      6, i.e. at step 7, the harness's last-fire step for B0;
    - [example_score_le7]: every quiet instruction scores at most 7.

    A statement-level sanity check: the definitions reproduce the
    harness's documented distinction, not just its numbers. *)

From Coq Require Import Arith List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers Require Import TCycler TCyclerQHTr.
Import ListNotations.

Definition tm_example : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB) | StA, S1 => Some (mkTrans S1 DL StA)
  | StB, S0 => Some (mkTrans S0 DL StA) | StB, S1 => Some (mkTrans S1 DR StA)
  | _, _ => None
  end.

Lemma example_tr :
  NonHalt tm_example
  /\ (forall tg s, QuietAfterTr tm_example tg s -> S s <= 7)
  /\ QuasiHaltsTr tm_example.
Proof. apply (tcycler_check_qhboundtr_sound_L _ 7 5 0). vm_compute. reflexivity. Qed.

Theorem example_qh_tr : QuasiHaltsTr tm_example.
Proof. exact (proj2 (proj2 example_tr)). Qed.

Theorem example_score_le7 : forall tg s, QuietAfterTr tm_example tg s -> S s <= 7.
Proof. exact (proj1 (proj2 example_tr)). Qed.

Theorem example_not_qh_st : ~ QuasiHaltsSt tm_example.
Proof.
  apply never_qh_not_qh.
  apply (tcycler_check_neverqh_sound_L _ 7 5 0). vm_compute. reflexivity.
Qed.

Theorem example_B0_step7 : FiresAt tm_example (StB, S0) 6.
Proof.
  eexists. split.
  - rewrite <- lift_c0. apply csteps_lift. reflexivity.
  - reflexivity.
Qed.
