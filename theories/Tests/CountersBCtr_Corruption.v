(** * CountersBCtr_Corruption: negative controls for the bouncer counters.

    BBB corruption-test tradition: every computable ingredient of the
    bouncer-counter proof must REJECT mutated inputs.  For #11
    (1RB0LD_1RC0RC_1LA1RB_0LC0LD) and #13 (its [sigma]-relabel) we
    cover:

    - the two constants that are NOT free: the boot step count and the
      gap offset [g0].  A bouncer counter's whole content is that the
      bouncer length is affine in the counter VALUE, so an off-by-one
      in [g0] must break the anchor -- and it does, at the boot.
    - the walk rule: the digit walk must stop at a digit-0 pair and
      continue at a digit-1 pair.  A mutant that swaps where [StB]
      goes on S0 destroys the alternation and no longer realises
      [g_walk1].
    - the D-sweep must terminate at the separator, not run through it:
      [g_d10] leaves the head ON the separator in [StD], and a run one
      step longer is a different configuration.
    - the lap is exact, not "up to blanks": one step short of the lap
      is not the next anchor.

    Everything is decided by [vm_compute]/[reflexivity]/[discriminate];
    a regression that made any of these pass would be a soundness
    alarm. *)

From Coq Require Import Arith Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import BCtrCounter.
From BBB4.Machines.Counters Require Import BCtr_11 BCtr_13.
Import ListNotations.

Definition mkt (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** ** The boot constants are exact *)

(** #11 reaches [anchor StA 3 (bits 1)] at step 34 -- and at no
    neighbouring step. *)
Example boot11_exact :
  match csteps tm_11 34 c0 with
  | Some c => ceqb c (Cc StA 3 1) | None => false end = true.
Proof. vm_compute; reflexivity. Qed.

Example boot11_not_33 :
  match csteps tm_11 33 c0 with
  | Some c => ceqb c (Cc StA 3 1) | None => false end = false.
Proof. vm_compute; reflexivity. Qed.

Example boot11_not_35 :
  match csteps tm_11 35 c0 with
  | Some c => ceqb c (Cc StA 3 1) | None => false end = false.
Proof. vm_compute; reflexivity. Qed.

Example boot13_exact :
  match csteps tm_13 28 c0 with
  | Some c => ceqb c (Cc StC 2 1) | None => false end = true.
Proof. vm_compute; reflexivity. Qed.

Example boot13_not_27 :
  match csteps tm_13 27 c0 with
  | Some c => ceqb c (Cc StC 2 1) | None => false end = false.
Proof. vm_compute; reflexivity. Qed.

(** ** The gap offset is not free

    [g0] is the bouncer's length at counter value 0.  #11 has 3 and
    #13 has 2; swapping them (or using the other machine's) breaks the
    anchor at the boot, which is the cheapest place the affine
    bouncer-length claim can be falsified. *)

Example g0_11_is_not_2 :
  match csteps tm_11 34 c0 with
  | Some c => ceqb c (Cc StA 2 1) | None => false end = false.
Proof. vm_compute; reflexivity. Qed.

Example g0_11_is_not_4 :
  match csteps tm_11 34 c0 with
  | Some c => ceqb c (Cc StA 4 1) | None => false end = false.
Proof. vm_compute; reflexivity. Qed.

Example g0_13_is_not_3 :
  match csteps tm_13 28 c0 with
  | Some c => ceqb c (Cc StC 3 1) | None => false end = false.
Proof. vm_compute; reflexivity. Qed.

(** ** The anchor state is not free *)

Example anchor11_state :
  match csteps tm_11 34 c0 with
  | Some c => ceqb c (Cc StC 3 1) | None => false end = false.
Proof. vm_compute; reflexivity. Qed.

(** ** The lap is exact

    One bouncer sweep from [anchor (bits 1)] is
    [4*gap + 4*carry + 15 = 4*6 + 4*1 + 15 = 43] steps for #11.  One
    step short is not the next anchor. *)

Example lap11_exact :
  match csteps tm_11 43 (anchor StA 3 (bits 1)) with
  | Some c => ceqb c (anchor StA 3 (incr (bits 1))) | None => false end = true.
Proof. vm_compute; reflexivity. Qed.

Example lap11_not_42 :
  match csteps tm_11 42 (anchor StA 3 (bits 1)) with
  | Some c => ceqb c (anchor StA 3 (incr (bits 1))) | None => false end = false.
Proof. vm_compute; reflexivity. Qed.

(** The overflow lap (counter 3 -> 4, carry length 2) is
    [4*(3*3+3) + 4*2 + 15 = 71] steps and lands on a 3-digit word. *)
Example lap11_overflow :
  match csteps tm_11 71 (anchor StA 3 (bits 3)) with
  | Some c => ceqb c (anchor StA 3 (bits 4)) | None => false end = true.
Proof. vm_compute; reflexivity. Qed.

Example lap11_overflow_short :
  match csteps tm_11 70 (anchor StA 3 (bits 3)) with
  | Some c => ceqb c (anchor StA 3 (bits 4)) | None => false end = false.
Proof. vm_compute; reflexivity. Qed.

(** ** Unit mutation: break the digit walk

    [tm_11] with [B0] re-routed to StA instead of StC.  The StB/StC
    alternation that walks a digit-1 pair is destroyed, so the
    two-step [g_walk1] no longer holds. *)
Definition tm_11_mut : TM := fun q s =>
  match q, s with
  | StA, S0 => mkt S1 DR StB | StA, S1 => mkt S0 DL StD
  | StB, S0 => mkt S1 DR StA | StB, S1 => mkt S0 DR StC
  | StC, S0 => mkt S1 DL StA | StC, S1 => mkt S1 DR StB
  | StD, S0 => mkt S0 DL StC | StD, S1 => mkt S0 DL StD
  end.

Example mut_breaks_walk1 :
  csteps tm_11_mut 2 (StB, ([], S0, [S1]))
  <> Some (StB, ([S1; S1], chd (@nil Sym), ctl (@nil Sym))).
Proof. vm_compute. discriminate. Qed.

(** The genuine walk step does hold. *)
Example genuine_walk1 :
  csteps tm_11 2 (StB, ([], S0, [S1]))
  = Some (StB, ([S1; S1], chd (@nil Sym), ctl (@nil Sym))).
Proof. reflexivity. Qed.

(** ** The D-sweep stops at the separator

    [g_d10] fires exactly when the cell left of the head is the
    separator [S0]; running one step further leaves [StD]. *)
Example sweep_stops :
  csteps tm_11 1 (StD, ([S0; S1; S1], S1, []))
  = Some (StD, ([S1; S1], S0, [S0])).
Proof. reflexivity. Qed.

Example sweep_past_separator_leaves_D :
  match csteps tm_11 2 (StD, ([S0; S1; S1], S1, [])) with
  | Some (q, _) => st_eqb q StD | None => false end = false.
Proof. vm_compute; reflexivity. Qed.

(** ** The blank pair past the top digit really is a digit-0 pair

    This is the "simpler than a sync bouncer counter" claim: the walk
    needs no overflow rule, because [chd []]/[ctl []] hand it a
    digit-0 pair.  The two runs agree. *)
Example blank_pair_is_digit0 :
  csteps tm_11 2 (StB, ([S1], S0, [])) = Some (StA, ([S1], S1, [S1])).
Proof. reflexivity. Qed.

Example real_digit0_same :
  csteps tm_11 2 (StB, ([S1], S0, [S0; S1])) = Some (StA, ([S1], S1, [S1; S1])).
Proof. reflexivity. Qed.
