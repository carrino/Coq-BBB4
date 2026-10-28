From Coq Require Import List Arith Bool.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn18DoublePair Require Import DoublePair.
Import ListNotations.

Example actual_zero_entry : csteps(dp_tm false)35 c0=Some(dp_main 0 false[]).
Proof. reflexivity. Qed.
Example actual_two_entry : csteps(dp_tm true)33 c0=Some(dp_main 0 false[]).
Proof. reflexivity. Qed.
Example zero_three_context :
 csteps(dp_tm false)6(dp_back StB[S3;S3;S1;S0][S2;S3])=
 Some(dp_back StB[S1;S0][S2;S2;S2;S3]).
Proof. reflexivity. Qed.
Example two_three_context :
 csteps(dp_tm true)4(dp_back StB[S3;S3;S1;S0][S2;S3])=
 Some(dp_back StB[S1;S0][S2;S2;S2;S3]).
Proof. reflexivity. Qed.
Example empty_boundary_context : forall b,
 csteps(dp_tm b)10(dp_back StA[][S1;S0;S3])=
 Some(dp_front StA[S1;S1;S3][S0;S3]).
Proof. intro b;reflexivity. Qed.
Example zero_mode_one :
 csteps(dp_tm false)42(dp_main 1 false[false;true])=
 Some(dp_main 2 true[false;true]).
Proof. reflexivity. Qed.
Example two_mode_one :
 csteps(dp_tm true)40(dp_main 1 false[false;true])=
 Some(dp_main 2 true[false;true]).
Proof. reflexivity. Qed.
Example zero_binary_carry :
 csteps(dp_tm false)56(dp_main 1 true[false;true;false])=
 Some(dp_main 2 false[true;false;false]).
Proof. reflexivity. Qed.
Example two_binary_carry :
 csteps(dp_tm true)52(dp_main 1 true[false;true;false])=
 Some(dp_main 2 false[true;false;false]).
Proof. reflexivity. Qed.
Example zero_counter_growth :
 csteps(dp_tm false)70(dp_main 1 true[false;false])=
 Some(dp_main 2 false[true;true;true]).
Proof. reflexivity. Qed.
Example two_counter_growth :
 csteps(dp_tm true)68(dp_main 1 true[false;false])=
 Some(dp_main 2 false[true;true;true]).
Proof. reflexivity. Qed.
Example weak_zero_grammar_unprotected_B :
 csteps(dp_tm false)9(StA,([S1;S1;S3;S3],S0,[]))=
 Some(StB,([S2],S2,[S2;S1;S2])).
Proof. reflexivity. Qed.
Example weak_two_grammar_unprotected_B :
 csteps(dp_tm true)8(StA,([S1;S1;S3;S3],S0,[]))=
 Some(StB,([],S2,[S2;S2;S1;S2])).
Proof. reflexivity. Qed.
