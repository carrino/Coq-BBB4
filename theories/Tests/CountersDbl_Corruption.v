(** * CountersDbl_Corruption: negative controls for the double_counter #9.

    BBB corruption-test tradition: every computable ingredient of the
    proof must REJECT mutated inputs.  For #9
    (1RB0LC_1RC0RD_1LA0LC_1RD0RA) we cover:

    - unit mutation: a one-transition mutant ([C0] turns the wrong way)
      no longer realises the collapse cycle [Ucol], so the transported
      collapse phase would not hold;
    - wall discipline: the doubling poke digs into the RIGHT blank
      ([D1 = 0RA]), so with the right wall ON it must die (return
      [None]) rather than fabricate cells;
    - bootstrap anchor: distinct anchors [D9 2]/[D9 3] are separated by
      [ceqb], the genuine boot lands on [D9 2] at exactly 47 steps, and
      a wrong step count does not.

    Everything is decided by [vm_compute]/[reflexivity]/[discriminate];
    a regression that made any of these pass would be a soundness
    alarm. *)

From Coq Require Import Arith Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape.
From BBB4.Machines.Counters Require Import Double_9.
Import ListNotations.

(** ** Unit mutation *)

(** A mutant that turns [C0] the wrong way (rightward instead of
    leftward). *)
Definition tm_9_mut : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StC
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S0 DR StD
  | StC, S0 => mk S1 DR StA | StC, S1 => mk S0 DL StC
  | StD, S0 => mk S1 DR StD | StD, S1 => mk S0 DR StA
  end.

(** The genuine collapse cycle unit. *)
Example ok_Ucol : wsteps true true tm_9 2 (StA, ([S0; S1], S1, []))
                  = Some (StA, ([], S1, [S1; S0])).
Proof. reflexivity. Qed.

(** The mutant does NOT realise it. *)
Example mut_Ucol : wsteps true true tm_9_mut 2 (StA, ([S0; S1], S1, []))
                   <> Some (StA, ([], S1, [S1; S0])).
Proof. vm_compute. discriminate. Qed.

(** ** Wall discipline *)

(** The doubling poke [D1 = 0RA] digs into the right blank; the genuine
    run declares [br = false] ([Upokein]).  With the right wall ON it
    dies rather than fabricating the seed. *)
Example wall_poke_right : wsteps true true tm_9 3 (StD, ([], S1, [])) = None.
Proof. reflexivity. Qed.

(** The genuine poke (right wall OFF) succeeds. *)
Example ok_poke : wsteps true false tm_9 3 (StD, ([], S1, []))
                  = Some (StC, ([S1; S1; S0], S0, [])).
Proof. reflexivity. Qed.

(** ** Bootstrap anchor *)

(** Distinct anchors are distinguished by [ceqb]. *)
Example boot_anchor_distinct : ceqb (D9 2) (D9 3) = false.
Proof. reflexivity. Qed.

(** The boot really reaches [D9 2] from the blank tape at 47 steps. *)
Example boot_reaches : match csteps tm_9 47 c0 with
                       | Some c => ceqb c (D9 2)
                       | None => false
                       end = true.
Proof. vm_compute. reflexivity. Qed.

(** A wrong boot step count does not land on the anchor. *)
Example boot_wrong_index : match csteps tm_9 46 c0 with
                           | Some c => ceqb c (D9 2)
                           | None => false
                           end = false.
Proof. vm_compute. reflexivity. Qed.
