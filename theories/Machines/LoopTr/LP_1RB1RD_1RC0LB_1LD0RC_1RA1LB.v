(** * LP_1RB1RD_1RC0LB_1LD0RC_1RA1LB (SCOPING_INSTR 7.4.LE10)

    A state-renamed copy ([A B C D] plays [B C D A]) of the binary /
    base-3 mirror counter [LP_1RB0LA_1LC0RB_1RD1LA_1RA1RC].  Its blank run
    reaches that row's anchor with left [1] and right [0] after one step,
    off the source's own orbit, so [LoopConjTr.conj_family_neverqhtr]
    carries [inc] and [fires_g], which hold for every pair of digit strings.

    Hand-stated, kernel-checked.  Axiom footprint: [functional_extensionality_dep]. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr CConjugateTr LoopConjTr.
From BBB4.Machines.LoopTr Require LP_1RB0LA_1LC0RB_1RD1LA_1RA1RC.
Import ListNotations.

Definition tm_1RB1RD_1RC0LB_1LD0RC_1RA1LB : TM := fun q s => match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB) | StA, S1 => Some (mkTrans S1 DR StD)
  | StB, S0 => Some (mkTrans S1 DR StC) | StB, S1 => Some (mkTrans S0 DL StB)
  | StC, S0 => Some (mkTrans S1 DL StD) | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DR StA) | StD, S1 => Some (mkTrans S1 DL StB)
  end.
Definition p_1RB1RD_1RC0LB_1LD0RC_1RA1LB (q : St) : St :=
  match q with StA => StB | StB => StC | StC => StD | StD => StA end.

Module P := LP_1RB0LA_1LC0RB_1RD1LA_1RA1RC.

Definition Cg (n : nat) : cconf :=
  P.mk1 (bcells [S0; S0] [S1; S0] (Nat.iter n binc [true])) (P.tcells (Nat.iter n P.tinc [])).

Theorem nqhtr_1RB1RD_1RC0LB_1LD0RC_1RA1LB : NeverQuasiHaltsTr tm_1RB1RD_1RC0LB_1LD0RC_1RA1LB.
Proof.
  apply (conj_family_neverqhtr P.tm_1RB0LA_1LC0RB_1RD1LA_1RA1RC tm_1RB1RD_1RC0LB_1LD0RC_1RA1LB
           p_1RB1RD_1RC0LB_1LD0RC_1RA1LB false Cg).
  - intros q s; destruct q, s; reflexivity.
  - intros q; destruct q; [exists StD | exists StA | exists StB | exists StC]; reflexivity.
  - exists 1, 0. apply conj_boot_ok. vm_compute. reflexivity.
  - intros n. exists (S n). unfold Cg. cbn [Nat.iter nat_rect]. apply P.inc.
  - intros n t. apply P.fires_g.
Qed.
