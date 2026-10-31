From Coq Require Import List Arith Bool.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn22S053Counter Require Import S053Core Odd Outer.
Import ListNotations.

Example actual_entry : csteps sc_tm 51 c0=Some(sc_main 3 3).
Proof. reflexivity. Qed.
Example pair_context :
 csteps sc_tm 10(sc_back StB[S3;S3;S1;S0][S3;S3;S2;S1])=
 Some(sc_back StB[S1;S0][S3;S3;S2;S2;S2;S1]).
Proof. reflexivity. Qed.
Example even_context :
 csteps sc_tm 43(sc_back StB(repeat S3 6)[S3;S3;S3;S0;S2])=
 Some(sc_back StB(repeat S3 10)[S0;S2]).
Proof. reflexivity. Qed.
Example odd_context :
 csteps sc_tm 175(sc_front StA(repeat S1 5++[S3;S3;S2])[S3;S3;S0;S2])=
 Some(sc_back StB(repeat S3 12)[S2;S2;S0;S2]).
Proof. reflexivity. Qed.
Example even_base_two : csteps sc_tm 38(sc_C 2 4)=Some(sc_main 3 5).
Proof. reflexivity. Qed.
Example even_base_three : csteps sc_tm 41(sc_C 3 4)=Some(sc_main 4 5).
Proof. reflexivity. Qed.
Example even_base_four : csteps sc_tm 86(sc_C 4 4)=Some(sc_main 2 9).
Proof. reflexivity. Qed.
Example odd_base_two : csteps sc_tm 156(sc_C 2 5)=Some(sc_main 6 6).
Proof. reflexivity. Qed.
Example odd_base_three : csteps sc_tm 97(sc_C 3 3)=Some(sc_main 4 6).
Proof. reflexivity. Qed.
Example odd_base_four : csteps sc_tm 326(sc_C 4 3)=Some(sc_main 8 8).
Proof. reflexivity. Qed.
Example decreasing_outer_parameter :
 csteps sc_tm 1235(sc_main 8 1)=Some(sc_main 6 22).
Proof. vm_compute;reflexivity. Qed.
Example weak_word_grammar_rejected :
 csteps sc_tm 13(StA,([S3;S1],S0,[]))=Some(StB,([S3;S3;S3;S3],S0,[])).
Proof. reflexivity. Qed.
Example changed_pair_boundary_rejected :
 csteps sc_tm 10(sc_back StB[S3;S3][S3;S1])<>
 Some(sc_back StB[][S3;S3;S2;S2]).
Proof. discriminate. Qed.
Example both_states_recur :
 (forall N,exists t,N<=t /\ VisitsAt sc_tm StA t) /\
 (forall N,exists t,N<=t /\ VisitsAt sc_tm StB t).
Proof. split;[exact so_A_recurrent|exact so_B_recurrent]. Qed.
