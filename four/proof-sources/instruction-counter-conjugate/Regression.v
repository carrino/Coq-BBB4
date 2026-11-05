From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement StatementTr Spec CTape Instructions.
From BBB24SparseTwos Require Import TwosCounter.
From BBB24CounterConjugate Require Import ConjugateCounter.
Import ListNotations.
Example actual_boundary_after_three:
 stepn actual 3 InitES=Some(phi(lift(main 0 S1))).
Proof. exact entry_three. Qed.
Example boundary_is_not_blank_start:
 csteps(tc_tm None)2 c0=None.
Proof. reflexivity. Qed.
Example erased_boundary_survives_every_horizon:forall n,
 exists d,csteps(tc_tm None)n(main 0 S1)=Some d.
Proof. apply every_from. Qed.
Example last_A0_is_initial:QuietAfterTr actual(StA,S0)0.
Proof.
 split;[eexists;split;reflexivity|].
 intros n Hn;apply A0_quiet_one;lia.
Qed.
Example A1_recurrent:forall N,exists k,N<=k/\FiresAt actual(StA,S1)k.
Proof. apply seven_recurrent;discriminate. Qed.
Example B0_recurrent:forall N,exists k,N<=k/\FiresAt actual(StB,S0)k.
Proof. apply seven_recurrent;discriminate. Qed.
Example exact_score_one:AttainsTr actual 1/\QHBoundTr 1 actual.
Proof. split;[apply instruction_attains|apply instruction_bound]. Qed.
