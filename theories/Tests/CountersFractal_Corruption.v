(** * CountersFractal_Corruption: negative controls for the two fractals.

    BBB corruption-test tradition: every computable ingredient of the
    fractal proofs must REJECT mutated inputs.  Both boards rest on a
    handful of [wsteps] units plus two bootstrap anchors, so that is
    what is attacked here:

    - unit mutation: a one-transition mutant of each machine no longer
      realises the unit its cycle lemma is built from, so [cycL]/[cycR]
      could not have been instantiated;
    - wall discipline: each unit is stated with BOTH walls on, so a
      run that tried to fabricate a cell beyond the declared window
      dies ([None]) instead of inventing a blank;
    - bootstrap anchors: the genuine step counts land on the anchors
      ([ceqb] true) and neighbouring counts do not, so the [boot]
      lemmas cannot be satisfied by an off-by-one;
    - the two machines are DISTINCT and neither is the other's mirror,
      so the two boards are not accidentally the same proof twice.

    Everything is decided by [vm_compute]/[reflexivity]/[discriminate];
    a regression that made any of these pass would be a soundness
    alarm. *)

From Coq Require Import Arith Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From BBB4.Counters Require Import WTape.
From BBB4.Machines.Counters Require Import Fractal_3 Fractal_5.
Import ListNotations.

Definition mkt (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).

(** ** #5: 1RB0LA_1LC1RD_0LC1LA_0RD0RB *)

(** The genuine units of the three translated cycles. *)
Example ok5_C0 : wsteps true true tm_f5 1 (StC, ([S0], S0, []))
                 = Some (StC, ([], S0, [S0])).
Proof. reflexivity. Qed.

Example ok5_D0 : wsteps true true tm_f5 1 (StD, ([], S0, [S0]))
                 = Some (StD, ([S0], S0, [])).
Proof. reflexivity. Qed.

Example ok5_A1 : wsteps true true tm_f5 1 (StA, ([S1], S1, []))
                 = Some (StA, ([], S1, [S0])).
Proof. reflexivity. Qed.

(** Wall discipline: each unit steps off one end of its window, so
    with that side walled and the list empty the run must die. *)
Example wall5_C0 : wsteps true true tm_f5 1 (StC, ([], S0, [])) = None.
Proof. reflexivity. Qed.

Example wall5_D0 : wsteps true true tm_f5 1 (StD, ([], S0, [])) = None.
Proof. reflexivity. Qed.

Example wall5_A1 : wsteps true true tm_f5 1 (StA, ([], S1, [])) = None.
Proof. reflexivity. Qed.

(** [tm_f5] with [C1] re-routed to StC instead of StA: the left
    turnaround never hands to the eraser, so [uCA] dies. *)
Definition tm_f5_mut : TM := fun q s =>
  match q, s with
  | StA, S0 => mkt S1 DR StB | StA, S1 => mkt S0 DL StA
  | StB, S0 => mkt S1 DL StC | StB, S1 => mkt S1 DR StD
  | StC, S0 => mkt S0 DL StC | StC, S1 => mkt S1 DL StC  (* was StA *)
  | StD, S0 => mkt S0 DR StD | StD, S1 => mkt S0 DR StB
  end.

Example ok5_CA : wsteps true true tm_f5 2 (StC, ([S0], S1, []))
                 = Some (StB, ([S1], S1, [])).
Proof. reflexivity. Qed.

Example mut5_CA : wsteps true true tm_f5_mut 2 (StC, ([S0], S1, []))
                  <> Some (StB, ([S1], S1, [])).
Proof. vm_compute. discriminate. Qed.

(** Bootstrap: 6 steps land on the level-0 anchor, 5 and 7 do not. *)
Example boot5_hit : match csteps tm_f5 6 c0 with
                    | Some c => ceqb c (Fractal_5.Cf 1) | None => false end = true.
Proof. vm_compute. reflexivity. Qed.

Example boot5_miss5 : match csteps tm_f5 5 c0 with
                      | Some c => ceqb c (Fractal_5.Cf 1) | None => false end = false.
Proof. vm_compute. reflexivity. Qed.

Example boot5_miss7 : match csteps tm_f5 7 c0 with
                      | Some c => ceqb c (Fractal_5.Cf 1) | None => false end = false.
Proof. vm_compute. reflexivity. Qed.

(** ** #3: 1RB0LA_1LC0RD_0LB1LA_0RB1LA *)

Example ok3_LD : wsteps true true tm_f3 2 (StB, ([S0; S0], S0, []))
                 = Some (StB, ([], S0, [S0; S1])).
Proof. reflexivity. Qed.

Example ok3_BRun : wsteps true true tm_f3 3 (StB, ([], S1, [S1]))
                   = Some (StB, ([S1], S1, [])).
Proof. reflexivity. Qed.

Example ok3_BSkip : wsteps true true tm_f3 2 (StB, ([], S1, [S0; S1]))
                    = Some (StB, ([S0; S0], S1, [])).
Proof. reflexivity. Qed.

Example ok3_A1 : wsteps true true tm_f3 1 (StA, ([S1], S1, []))
                 = Some (StA, ([], S1, [S0])).
Proof. reflexivity. Qed.

(** Wall discipline. *)
Example wall3_LD : wsteps true true tm_f3 2 (StB, ([S0], S0, [])) = None.
Proof. reflexivity. Qed.

Example wall3_BRun : wsteps true true tm_f3 3 (StB, ([], S1, [])) = None.
Proof. reflexivity. Qed.

Example wall3_A1 : wsteps true true tm_f3 1 (StA, ([], S1, [])) = None.
Proof. reflexivity. Qed.

(** [tm_f3] with [C0] re-routed to StC instead of StB: the left drift
    never hands back to [B], so the [LD] unit dies. *)
Definition tm_f3_mut : TM := fun q s =>
  match q, s with
  | StA, S0 => mkt S1 DR StB | StA, S1 => mkt S0 DL StA
  | StB, S0 => mkt S1 DL StC | StB, S1 => mkt S0 DR StD
  | StC, S0 => mkt S0 DL StC | StC, S1 => mkt S1 DL StA  (* was StB *)
  | StD, S0 => mkt S0 DR StB | StD, S1 => mkt S1 DL StA
  end.

Example mut3_LD : wsteps true true tm_f3_mut 2 (StB, ([S0; S0], S0, []))
                  <> Some (StB, ([], S0, [S0; S1])).
Proof. vm_compute. congruence. Qed.

(** The eight-step one-digit bump, and a mutant that misses it. *)
Example ok3_g1 : wsteps true true tm_f3 8 (StB, ([S1; S0], S0, [S0; S0]))
                 = Some (StB, ([S0; S0; S1; S1], S0, [])).
Proof. reflexivity. Qed.

(** A second mutant, [D1] re-routed to StB: the bump's fifth step no
    longer hands to the eraser and the run walks off its window. *)
Definition tm_f3_mut2 : TM := fun q s =>
  match q, s with
  | StA, S0 => mkt S1 DR StB | StA, S1 => mkt S0 DL StA
  | StB, S0 => mkt S1 DL StC | StB, S1 => mkt S0 DR StD
  | StC, S0 => mkt S0 DL StB | StC, S1 => mkt S1 DL StA
  | StD, S0 => mkt S0 DR StB | StD, S1 => mkt S1 DL StB  (* was StA *)
  end.

Example mut3_g1 : wsteps true true tm_f3_mut2 8 (StB, ([S1; S0], S0, [S0; S0]))
                  <> Some (StB, ([S0; S0; S1; S1], S0, [])).
Proof. vm_compute. discriminate. Qed.

(** Bootstrap: 31 steps land on the level-0 anchor, 30 and 32 do not. *)
Example boot3_hit : match csteps tm_f3 31 c0 with
                    | Some c => ceqb c (Fractal_3.Cf 1) | None => false end = true.
Proof. vm_compute. reflexivity. Qed.

Example boot3_miss30 : match csteps tm_f3 30 c0 with
                       | Some c => ceqb c (Fractal_3.Cf 1) | None => false end = false.
Proof. vm_compute. reflexivity. Qed.

Example boot3_miss32 : match csteps tm_f3 32 c0 with
                       | Some c => ceqb c (Fractal_3.Cf 1) | None => false end = false.
Proof. vm_compute. reflexivity. Qed.

(** ** The two boards are genuinely two machines *)

Example f3_neq_f5 : tm_f3 StB S1 <> tm_f5 StB S1.
Proof. vm_compute. discriminate. Qed.

Example f3_not_mirror_f5 : mirror_tm tm_f3 StB S1 <> tm_f5 StB S1.
Proof. vm_compute. discriminate. Qed.
