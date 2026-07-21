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
From BBB4.Machines.Counters Require Import Wave_17.
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
