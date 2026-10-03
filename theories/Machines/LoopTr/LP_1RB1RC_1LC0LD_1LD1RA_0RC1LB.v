(** * LP_1RB1RC_1LC0LD_1LD1RA_0RC1LB (SCOPING_INSTR 7.4.LE10)

    A state-renamed copy of [LP_0RB1LD_1LA1RC_1RD1RB_1LB0LA].  Its blank run enters
    that row's lap family [Cg] at [Cg 0] (after 25 steps), which the
    source's own run never visits, so the two runs never fall into lockstep
    and [CConjCoverTr] does not apply.  [LoopConjTr.conj_family_neverqhtr]
    carries the source's lap for every member of the family.

    Axiom footprint: [functional_extensionality_dep]. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import CConjugateTr LoopConjTr.
From BBB4.Machines.LoopTr Require LP_0RB1LD_1LA1RC_1RD1RB_1LB0LA.
Import ListNotations.

Definition tm_1RB1RC_1LC0LD_1LD1RA_0RC1LB : TM := fun q s => match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StC)
  | StB, S0 => Some (mkTrans S1 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StA)
  | StD, S0 => Some (mkTrans S0 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.
Definition p_1RB1RC_1LC0LD_1LD1RA_0RC1LB (q : St) : St := match q with StA => StD | StB => StC | StC => StA | StD => StB end.

Theorem nqhtr_1RB1RC_1LC0LD_1LD1RA_0RC1LB : NeverQuasiHaltsTr tm_1RB1RC_1LC0LD_1LD1RA_0RC1LB.
Proof.
  apply (conj_family_neverqhtr LP_0RB1LD_1LA1RC_1RD1RB_1LB0LA.tm_0RB1LD_1LA1RC_1RD1RB_1LB0LA tm_1RB1RC_1LC0LD_1LD1RA_0RC1LB p_1RB1RC_1LC0LD_1LD1RA_0RC1LB false LP_0RB1LD_1LA1RC_1RD1RB_1LB0LA.Cg).
  - intros q s; destruct q, s; reflexivity.
  - intros q; destruct q; [exists StC | exists StD | exists StB | exists StA]; reflexivity.
  - exists 25, 0. apply conj_boot_ok. vm_compute. reflexivity.
  - intros m. exists (3 + m). apply LP_0RB1LD_1LA1RC_1RD1RB_1LB0LA.lap_g.
  - exact LP_0RB1LD_1LA1RC_1RD1RB_1LB0LA.fires_g.
Qed.
