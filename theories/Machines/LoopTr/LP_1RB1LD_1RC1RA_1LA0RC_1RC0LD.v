(** * LP_1RB1LD_1RC1RA_1LA0RC_1RC0LD (SCOPING_INSTR 7.4.LE10)

    A state-renamed copy ([A B C D] plays [D C A B]) of the 4-cell
    binary / base-3 mirror counter [LP_1RB0LA_1LC0RB_1RD1LA_1RB1RC].  Its
    blank run reaches that row's anchor with left [2] and right [1] after
    23 steps, off the source's own orbit, so
    [LoopConjTr.conj_family_neverqhtr] carries [inc] and [fires_g].

    Hand-stated, kernel-checked.  Axiom footprint: [functional_extensionality_dep]. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr CConjugateTr LoopConjTr.
From BBB4.Machines.LoopTr Require LP_1RB0LA_1LC0RB_1RD1LA_1RB1RC.
Import ListNotations.

Definition tm_1RB1LD_1RC1RA_1LA0RC_1RC0LD : TM := fun q s => match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB) | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DR StC) | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S1 DL StA) | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DR StC) | StD, S1 => Some (mkTrans S0 DL StD)
  end.
Definition p_1RB1LD_1RC1RA_1LA0RC_1RC0LD (q : St) : St :=
  match q with StA => StD | StB => StC | StC => StA | StD => StB end.

Module P := LP_1RB0LA_1LC0RB_1RD1LA_1RB1RC.

Definition Cg (n : nat) : cconf :=
  P.mk1 (bcells [S0; S0] [S1; S0] (Nat.iter n binc [false; true])) (P.tcells (Nat.iter n P.tinc [P.t1])).

Theorem nqhtr_1RB1LD_1RC1RA_1LA0RC_1RC0LD : NeverQuasiHaltsTr tm_1RB1LD_1RC1RA_1LA0RC_1RC0LD.
Proof.
  apply (conj_family_neverqhtr P.tm_1RB0LA_1LC0RB_1RD1LA_1RB1RC tm_1RB1LD_1RC1RA_1LA0RC_1RC0LD
           p_1RB1LD_1RC1RA_1LA0RC_1RC0LD false Cg).
  - intros q s; destruct q, s; reflexivity.
  - intros q; destruct q; [exists StC | exists StD | exists StB | exists StA]; reflexivity.
  - exists 23, 0. apply conj_boot_ok. vm_compute. reflexivity.
  - intros n. exists (S n). unfold Cg. cbn [Nat.iter nat_rect]. apply P.inc.
  - intros n t. apply P.fires_g.
Qed.
