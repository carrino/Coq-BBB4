(** * CountersTower20_Corruption: negative controls for tower #20.

    BBB corruption-test tradition: every computable ingredient of the
    [nqh_tower20] board must REJECT mutated inputs.  The board rests on

    - a three-record boot that settles on the left-record anchor
      [CfW [1;4]] at exactly t = 50 ([boot20_W]);
    - the long lap, whose exact step count lands the [k]-th anchor on the
      [(k+1)]-th ([Cf20 (next20 a) reached from Cf20 a]).

    So those are what is attacked here: the boot lands at 50 and NOT at its
    neighbours; the first three laps land at their measured counts (36, 56,
    52) and NOT one step early or late; and a one-transition mutant of
    [tm_20] can no longer take the very first step the counter needs, so no
    joint of the board could have been instantiated from it.

    Everything is decided by [vm_compute]/[reflexivity]/[discriminate]; a
    regression that made any of these pass would be a soundness alarm. *)

From Coq Require Import Arith Bool List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Machines.Counters Require Import Tower_20.
Import ListNotations.

Definition mkt (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).

(** ** The three anchors used below *)
Definition T0 := Cf20 a020.                          (* [1;4] *)
Definition T1 := Cf20 (next20 a020).                 (* [7]   *)
Definition T2 := Cf20 (next20 (next20 a020)).
Definition T3 := Cf20 (next20 (next20 (next20 a020))).

(** ** The boot lands at t = 50 and nowhere adjacent *)

Example t20_boot_50 :
  match csteps tm_20 50 c0 with Some c => ceqb c (CfW w0_20) | None => false end = true.
Proof. vm_compute. reflexivity. Qed.

Example t20_boot_not_49 :
  match csteps tm_20 49 c0 with Some c => ceqb c (CfW w0_20) | None => false end = false.
Proof. vm_compute. reflexivity. Qed.

Example t20_boot_not_51 :
  match csteps tm_20 51 c0 with Some c => ceqb c (CfW w0_20) | None => false end = false.
Proof. vm_compute. reflexivity. Qed.

(** ** The lap step counts are exact

    A0 -> A1 in 36, A1 -> A2 in 56, A2 -> A3 in 52; one step off in either
    direction misses.  [ceqb] absorbs trailing blanks, so the end-of-tape
    turn (where the return sweep lands one cell short of a written [0]) is
    still recognised -- and STILL rejected at the wrong count. *)

Example t20_lap01 :
  match csteps tm_20 36 T0 with Some c => ceqb c T1 | None => false end = true.
Proof. vm_compute. reflexivity. Qed.

Example t20_lap01_not_35 :
  match csteps tm_20 35 T0 with Some c => ceqb c T1 | None => false end = false.
Proof. vm_compute. reflexivity. Qed.

Example t20_lap01_not_37 :
  match csteps tm_20 37 T0 with Some c => ceqb c T1 | None => false end = false.
Proof. vm_compute. reflexivity. Qed.

Example t20_lap12 :
  match csteps tm_20 56 T1 with Some c => ceqb c T2 | None => false end = true.
Proof. vm_compute. reflexivity. Qed.

Example t20_lap12_not_55 :
  match csteps tm_20 55 T1 with Some c => ceqb c T2 | None => false end = false.
Proof. vm_compute. reflexivity. Qed.

Example t20_lap12_not_57 :
  match csteps tm_20 57 T1 with Some c => ceqb c T2 | None => false end = false.
Proof. vm_compute. reflexivity. Qed.

Example t20_lap23 :
  match csteps tm_20 52 T2 with Some c => ceqb c T3 | None => false end = true.
Proof. vm_compute. reflexivity. Qed.

Example t20_lap23_not_51 :
  match csteps tm_20 51 T2 with Some c => ceqb c T3 | None => false end = false.
Proof. vm_compute. reflexivity. Qed.

Example t20_lap23_not_53 :
  match csteps tm_20 53 T2 with Some c => ceqb c T3 | None => false end = false.
Proof. vm_compute. reflexivity. Qed.

(** The two anchors are DISTINCT laps: the count that runs A0 does not run
    A1 (36 <> 56), so the laps are not one shared parametric run. *)
Example t20_laps_distinct :
  match csteps tm_20 36 T1 with Some c => ceqb c T2 | None => false end = false.
Proof. vm_compute. reflexivity. Qed.

(** ** A one-transition mutant cannot even start the counter

    [tm_20] has [StC, S0 => 1RA]: the outward sweep's return into [StA].
    Re-route it to [StB] and the very first joint [jca]
    ([csteps 1 (StC,(L,S0,R)) = (StA, ...)]) can no longer hold, so nothing
    the board is built from survives. *)

Definition tm_20_mut : TM := fun q s =>
  match q, s with
  | StA, S0 => mkt S1 DR StB | StA, S1 => mkt S0 DR StD
  | StB, S0 => mkt S1 DL StC | StB, S1 => mkt S1 DL StB
  | StC, S0 => mkt S1 DR StB | StC, S1 => mkt S0 DL StB   (* C0: StA -> StB *)
  | StD, S0 => mkt S1 DL StC | StD, S1 => mkt S1 DR StA
  end.

Example t20_mut_breaks_jca :
  csteps tm_20_mut 1 (StC, ([], S0, [S1]))
    <> csteps tm_20 1 (StC, ([], S0, [S1])).
Proof. vm_compute. discriminate. Qed.

(** ...and the mutant's run never settles on the genuine boot anchor. *)
Example t20_mut_boot_fails :
  match csteps tm_20_mut 50 c0 with Some c => ceqb c (CfW w0_20) | None => false end = false.
Proof. vm_compute. reflexivity. Qed.
