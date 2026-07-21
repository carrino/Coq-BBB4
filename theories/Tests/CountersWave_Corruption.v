(** * CountersWave_Corruption: negative controls for the wave counters.

    BBB corruption-test tradition: every computable ingredient of the
    wave proof must REJECT mutated inputs.  For #17
    (1RB0RD_0LB1LC_1RA1LB_1RA1RD) we cover:

    - wall discipline: the frontier turnaround digs into the RIGHT
      blank and the spawn digs into the LEFT blank, so with the
      corresponding wall ON they must die (return [None]), not
      fabricate cells;
    - unit mutation: a one-transition mutant that breaks the leftward
      cross cycle no longer realises the cross-pair unit;
    - bootstrap anchor: a wrong anchor is rejected by [ceqb], and the
      genuine boot config is NOT the next event config.

    Everything is decided by [vm_compute]/[reflexivity]/[discriminate];
    a regression that made any of these pass would be a soundness
    alarm. *)

From Coq Require Import Arith Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape WaveCounter.
From BBB4.Machines.Counters Require Import Wave_17 Wave_27 Wave_36.
Import ListNotations.

(** ** Wall discipline *)

(** The frontier turnaround (FT) writes into the right blank; the
    genuine run declares [br = false].  With the right wall ON it dies. *)
Example wall_FT_right : wsteps true true tm_17 1 (StD, ([S1], S0, [])) = None.
Proof. reflexivity. Qed.

(** The genuine FT (right wall OFF) succeeds. *)
Example ok_FT : wsteps true false tm_17 3 (StD, ([], S0, [])) = Some (StB, ([S1], S1, [S0])).
Proof. reflexivity. Qed.

(** The spawn crosses the lead into the LEFT blank; with the left wall
    ON it dies at the [B1] step that pops the empty left list. *)
Example wall_spawn_left : wsteps true true tm_17 2 (StB, ([], S1, [S0])) = None.
Proof. reflexivity. Qed.

(** ** Unit mutation: break the leftward cross cycle *)

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).

(** tm_17 with [B1] re-routed to StD instead of StC: the B/C
    alternation of [cross_run] is destroyed. *)
Definition tm_17_mut : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DR StD
  | StB, S0 => mk S0 DL StB | StB, S1 => mk S1 DL StD  (* was StC *)
  | StC, S0 => mk S1 DR StA | StC, S1 => mk S1 DL StB
  | StD, S0 => mk S1 DR StA | StD, S1 => mk S1 DR StD
  end.

(** The genuine cross-pair unit. *)
Example ok_crosspair : wsteps true true tm_17 2 (StB, ([S1; S1], S1, []))
                       = Some (StB, ([], S1, [S1; S1])).
Proof. reflexivity. Qed.

(** The mutant does NOT realise it. *)
Example mut_crosspair : wsteps true true tm_17_mut 2 (StB, ([S1; S1], S1, []))
                        <> Some (StB, ([], S1, [S1; S1])).
Proof. vm_compute. discriminate. Qed.

(** ** Bootstrap anchor *)

(** Distinct anchors are distinguished by [ceqb]. *)
Example boot_anchor_distinct : ceqb (Cf17 [3; 2; 1]) (Cf17 [4; 3; 1]) = false.
Proof. reflexivity. Qed.

(** The genuine boot config is NOT the next event (a lap does something). *)
Example boot_not_next : ceqb (Cf17 [3; 2; 1]) (Cf17 (nextf 0 [3; 2; 1])) = false.
Proof. reflexivity. Qed.

(** The boot really reaches [Cf17 [3;2;1]] from the blank tape at 49 steps. *)
Example boot_reaches : match csteps tm_17 49 CTape.c0 with
                       | Some c => ceqb c (Cf17 [3; 2; 1])
                       | None => false
                       end = true.
Proof. vm_compute. reflexivity. Qed.

(** A wrong boot step count does not land on the anchor. *)
Example boot_wrong_index : match csteps tm_17 48 CTape.c0 with
                           | Some c => ceqb c (Cf17 [3; 2; 1])
                           | None => false
                           end = false.
Proof. vm_compute. reflexivity. Qed.

(** ** #27 (1RB1LC_1LC0RD_0LC1LA_1RB1RD, poff 1) -- same controls.

    The #27 FT is a 2-step [D0/1R>B B0/1L>C] digging the right blank; the
    spawn digs the left blank at the [C1] step; the leftward cross is the
    C/A pair. *)

(** FT writes into the right blank; with the right wall ON it dies. *)
Example wall_FT_right_27 : wsteps true true tm_27 1 (StD, ([S1], S0, [])) = None.
Proof. reflexivity. Qed.

(** The genuine FT (right wall OFF) succeeds. *)
Example ok_FT_27 : wsteps true false tm_27 2 (StD, ([], S0, [])) = Some (StC, ([], S1, [S1])).
Proof. reflexivity. Qed.

(** The spawn crosses the lead into the LEFT blank; with the left wall ON
    it dies at the [C1] step that pops the empty left list. *)
Example wall_spawn_left_27 : wsteps true true tm_27 1 (StC, ([], S1, [S0])) = None.
Proof. reflexivity. Qed.

(** tm_27 with [C1] re-routed to StD instead of StA: the C/A alternation
    of [cross_run27] is destroyed. *)
Definition tm_27_mut : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StC
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DR StD
  | StC, S0 => mk S0 DL StC | StC, S1 => mk S1 DL StD  (* was StA *)
  | StD, S0 => mk S1 DR StB | StD, S1 => mk S1 DR StD
  end.

(** The genuine cross-pair unit (C/A). *)
Example ok_crosspair_27 : wsteps true true tm_27 2 (StC, ([S1; S1], S1, []))
                        = Some (StC, ([], S1, [S1; S1])).
Proof. reflexivity. Qed.

(** The mutant does NOT realise it. *)
Example mut_crosspair_27 : wsteps true true tm_27_mut 2 (StC, ([S1; S1], S1, []))
                         <> Some (StC, ([], S1, [S1; S1])).
Proof. vm_compute. discriminate. Qed.

(** Distinct #27 anchors are distinguished by [ceqb]; the boot config is
    not the next event; the boot reaches [Cf27 [4;2;1]] at 50 steps only. *)
Example boot_anchor_distinct_27 : ceqb (Cf27 [4; 2; 1]) (Cf27 [5; 3; 1]) = false.
Proof. reflexivity. Qed.

Example boot_not_next_27 : ceqb (Cf27 [4; 2; 1]) (Cf27 (nextf 1 [4; 2; 1])) = false.
Proof. reflexivity. Qed.

Example boot_reaches_27 : match csteps tm_27 50 CTape.c0 with
                          | Some c => ceqb c (Cf27 [4; 2; 1])
                          | None => false
                          end = true.
Proof. vm_compute. reflexivity. Qed.

Example boot_wrong_index_27 : match csteps tm_27 49 CTape.c0 with
                              | Some c => ceqb c (Cf27 [4; 2; 1])
                              | None => false
                              end = false.
Proof. vm_compute. reflexivity. Qed.

(** ** #36 (1RB1RA_1LC0RA_0LC1LD_1RB1LC, poff 1) -- the #27 machine under
    A<->D; edge state A, cross pair C/D. *)

(** FT digs the right blank (A0/1R>B); right wall ON kills it. *)
Example wall_FT_right_36 : wsteps true true tm_36 1 (StA, ([S1], S0, [])) = None.
Proof. reflexivity. Qed.

Example ok_FT_36 : wsteps true false tm_36 2 (StA, ([], S0, [])) = Some (StC, ([], S1, [S1])).
Proof. reflexivity. Qed.

(** Spawn digs the left blank at the [C1] step. *)
Example wall_spawn_left_36 : wsteps true true tm_36 1 (StC, ([], S1, [S0])) = None.
Proof. reflexivity. Qed.

(** tm_36 with [C1] re-routed to StA instead of StD: the C/D alternation
    of [cross_run36] is destroyed. *)
Definition tm_36_mut : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DR StA
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DR StA
  | StC, S0 => mk S0 DL StC | StC, S1 => mk S1 DL StA  (* was StD *)
  | StD, S0 => mk S1 DR StB | StD, S1 => mk S1 DL StC
  end.

Example ok_crosspair_36 : wsteps true true tm_36 2 (StC, ([S1; S1], S1, []))
                        = Some (StC, ([], S1, [S1; S1])).
Proof. reflexivity. Qed.

Example mut_crosspair_36 : wsteps true true tm_36_mut 2 (StC, ([S1; S1], S1, []))
                         <> Some (StC, ([], S1, [S1; S1])).
Proof. vm_compute. discriminate. Qed.

Example boot_anchor_distinct_36 : ceqb (Cf36 [4; 2; 1]) (Cf36 [5; 3; 1]) = false.
Proof. reflexivity. Qed.

Example boot_not_next_36 : ceqb (Cf36 [4; 2; 1]) (Cf36 (nextf 1 [4; 2; 1])) = false.
Proof. reflexivity. Qed.

Example boot_reaches_36 : match csteps tm_36 50 CTape.c0 with
                          | Some c => ceqb c (Cf36 [4; 2; 1])
                          | None => false
                          end = true.
Proof. vm_compute. reflexivity. Qed.

Example boot_wrong_index_36 : match csteps tm_36 49 CTape.c0 with
                              | Some c => ceqb c (Cf36 [4; 2; 1])
                              | None => false
                              end = false.
Proof. vm_compute. reflexivity. Qed.
