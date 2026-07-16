(** * CountersB_Corruption: negative controls for the session-B counters.

    BBB corruption-test tradition (see Counters_Corruption.v for the
    session-A machines): every computable ingredient of the counter
    proofs must REJECT mutated inputs.  Session B adds the
    interleave/exp/bounce machines and the MeasureGlue closer, so the
    controls here cover:

    - wall discipline: unit runs that need cells beyond their window
      must die, not fabricate blanks;
    - unit mutations: wrong period or wrong exit configuration
      rejected;
    - machine mutations: a one-transition mutant of each of the seven
      machines breaks a unit that fires the changed rule;
    - bootstrap anchors: a wrong anchor index is rejected by [ceqb];
    - the MeasureGlue recurrence and measure (bounce): a double-sweep
      that fails to increment the digit word, or fails to grow the
      comb, is rejected against the concrete run, and the reversed
      recurrence INCREASES the measure (so a mutated [mrun] instance
      cannot discharge its decrease obligation).

    Everything here is decided by [vm_compute]/[discriminate]; a
    regression that made any of these pass would be a soundness
    alarm. *)

From Coq Require Import Arith Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape MonoCounter ILCounter ExpCounter
  BounceCounter.
From BBB4.Machines.Counters Require Import Interleave_18 Interleave_35
  Exp_2 Exp_4 Exp_12 Bounce_8 Bounce_33.
Import ListNotations.

(** ** Wall discipline *)

(** #18's overflow stop writes the fresh MSB pair beyond the left
    edge: with the left wall ON it must die. *)
Example wall_18_U4o : wsteps true true tm_18 6 (StC, ([S1], S1, []))
                      = None.
Proof. reflexivity. Qed.

(** #2's overflow marker stop runs off the left edge likewise. *)
Example wall_2_UMo : wsteps true true tm_2 8 (StA, ([], S1, []))
                     = None.
Proof. reflexivity. Qed.

(** #8's sweep exit steps onto the blank cell left of the comb. *)
Example wall_8_UE : wsteps true true tm_8 2 (StA, ([S1], S1, []))
                    = None.
Proof. reflexivity. Qed.

(** #33's terminal step walks onto the blank beyond the old extent. *)
Example wall_33_UTD : wsteps true true tm_33 1 (StB, ([], S1, []))
                      = None.
Proof. reflexivity. Qed.

(** ** Unit-run mutations *)

(** #18's comb crossing takes exactly 3 steps; at period 2 the run is
    mid-cycle. *)
Example U2_18_wrong_period :
  wsteps true true tm_18 2 (StC, ([S0; S1; S1], S1, []))
  <> Some (StC, ([], S1, [S0; S1; S1])).
Proof. discriminate. Qed.

(** #8's collapse deposits 11, not 10. *)
Example UC_8_wrong_exit :
  wsteps true true tm_8 4 (StB, ([], S1, [S0; S1]))
  <> Some (StB, ([S1; S0], S1, [])).
Proof. discriminate. Qed.

(** #12's right stride must leave a solid trail, not the marker form. *)
Example URs_12_wrong_exit :
  wsteps true true tm_12 3 (StB, ([], S1, [S0; S0; S1]))
  <> Some (StB, ([S0; S0; S1], S1, [])).
Proof. discriminate. Qed.

(** ** Machine mutations break the units that fire the changed rule *)

Definition tm_18_mutD1 : TM := fun q s =>
  match q, s with
  | StD, S1 => mk S1 DR StB
  | _, _ => tm_18 q s
  end.

Example mutD1_breaks_U10_18 :
  wsteps true true tm_18_mutD1 3 (StD, ([], S1, [S0; S1; S1]))
  <> Some (StD, ([S0; S1; S1], S1, [])).
Proof. discriminate. Qed.

Definition tm_35_mutC1 : TM := fun q s =>
  match q, s with
  | StC, S1 => mk S0 DL StA
  | _, _ => tm_35 q s
  end.

Example mutC1_breaks_U2_35 :
  wsteps true true tm_35_mutC1 3 (StD, ([S0; S1; S1], S1, []))
  <> Some (StD, ([], S1, [S0; S1; S1])).
Proof. discriminate. Qed.

Definition tm_2_mutD1 : TM := fun q s =>
  match q, s with
  | StD, S1 => mk S1 DR StD
  | _, _ => tm_2 q s
  end.

Example mutD1_breaks_UWout_2 :
  wsteps true true tm_2_mutD1 2 (StD, ([], S1, [S0; S1]))
  <> Some (StD, ([S1; S1], S1, [])).
Proof. discriminate. Qed.

Definition tm_4_mutC1 : TM := fun q s =>
  match q, s with
  | StC, S1 => mk S1 DL StD
  | _, _ => tm_4 q s
  end.

Example mutC1_breaks_UWout_4 :
  wsteps true true tm_4_mutC1 2 (StC, ([S0; S1], S1, []))
  <> Some (StC, ([], S1, [S1; S1])).
Proof. discriminate. Qed.

Definition tm_12_mutB1 : TM := fun q s =>
  match q, s with
  | StB, S1 => mk S1 DR StB
  | _, _ => tm_12 q s
  end.

Example mutB1_breaks_URs_12 :
  wsteps true true tm_12_mutB1 3 (StB, ([], S1, [S0; S0; S1]))
  <> Some (StB, ([S1; S1; S1], S1, [])).
Proof. discriminate. Qed.

Definition tm_8_mutB1 : TM := fun q s =>
  match q, s with
  | StB, S1 => mk S1 DR StB
  | _, _ => tm_8 q s
  end.

Example mutB1_breaks_UC_8 :
  wsteps true true tm_8_mutB1 4 (StB, ([], S1, [S0; S1]))
  <> Some (StB, ([S1; S1], S1, [])).
Proof. discriminate. Qed.

Definition tm_33_mutC1 : TM := fun q s =>
  match q, s with
  | StC, S1 => mk S1 DL StB
  | _, _ => tm_33 q s
  end.

Example mutC1_breaks_UC_33 :
  wsteps true true tm_33_mutC1 2 (StB, ([], S0, [S1; S0]))
  <> Some (StB, ([S1; S1], S0, [])).
Proof. discriminate. Qed.

(** ** Bootstrap anchor mutations *)

Example boot_18_wrong_anchor :
  match csteps tm_18 256 c0 with
  | Some c => ceqb c (Interleave_18.Cc 5)
  | None => false
  end = false.
Proof. vm_compute. reflexivity. Qed.

Example boot_2_wrong_anchor :
  match csteps tm_2 34 c0 with
  | Some c => ceqb c (Exp_2.Cc 2)
  | None => false
  end = false.
Proof. vm_compute. reflexivity. Qed.

Example boot_8_wrong_anchor :
  match csteps tm_8 34 c0 with
  | Some c => ceqb c (Bounce_8.Cc 2)
  | None => false
  end = false.
Proof. vm_compute. reflexivity. Qed.

Example mut_boot_8 :
  match csteps tm_8_mutB1 34 c0 with
  | Some c => ceqb c (Bounce_8.Cc 1)
  | None => false
  end = false.
Proof. vm_compute. reflexivity. Qed.

(** ** MeasureGlue negative controls (the bounce recurrence) *)

(** The genuine double-sweep: from Sc 1 [0] the #8 run reaches
    Sc 2 [1] in exactly 40 steps (positive control). *)
Example dlap_8_true :
  match csteps tm_8 40 (Bounce_8.Sc 1 [false]) with
  | Some c => ceqb c (Bounce_8.Sc 2 [true])
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** A mutated recurrence that fails to increment the word is
    rejected against the concrete run... *)
Example dlap_8_word_not_incremented :
  match csteps tm_8 40 (Bounce_8.Sc 1 [false]) with
  | Some c => ceqb c (Bounce_8.Sc 2 [false])
  | None => false
  end = false.
Proof. vm_compute. reflexivity. Qed.

(** ... and so is one that fails to grow the comb. *)
Example dlap_8_comb_not_grown :
  match csteps tm_8 40 (Bounce_8.Sc 1 [false]) with
  | Some c => ceqb c (Bounce_8.Sc 1 [true])
  | None => false
  end = false.
Proof. vm_compute. reflexivity. Qed.

(** The same pair for #33 (28-step double-sweep). *)
Example dlap_33_true :
  match csteps tm_33 28 (Bounce_33.Sc 1 [false]) with
  | Some c => ceqb c (Bounce_33.Sc 2 [true])
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

Example dlap_33_word_not_incremented :
  match csteps tm_33 28 (Bounce_33.Sc 1 [false]) with
  | Some c => ceqb c (Bounce_33.Sc 2 [false])
  | None => false
  end = false.
Proof. vm_compute. reflexivity. Qed.

(** The measure: the genuine increment decrements [cval] by one
    (positive control)... *)
Example cval_step_decreases :
  Nat.ltb (cval (repeat false 2 ++ [true]))
          (cval (repeat true 2 ++ [false])) = true.
Proof. vm_compute. reflexivity. Qed.

(** ... and the REVERSED recurrence increases it, so a mutated mrun
    instance cannot discharge its measure obligation. *)
Example cval_reversed_step_grows :
  Nat.ltb (cval (repeat true 2 ++ [false]))
          (cval (repeat false 2 ++ [true])) = false.
Proof. vm_compute. reflexivity. Qed.

(** A "recurrence" that keeps the word fixed does not decrease the
    measure either. *)
Example cval_stalled_step_rejected :
  Nat.ltb (cval (repeat true 2 ++ [false]))
          (cval (repeat true 2 ++ [false])) = false.
Proof. vm_compute. reflexivity. Qed.
