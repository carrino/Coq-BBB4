From Coq Require Import List Arith Bool.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn17BinaryRank Require Import BinaryRank.
Import ListNotations.

Example actual_entry : csteps br_tm 7 c0=Some(br_main 0).
Proof. reflexivity. Qed.
Example rank_decreases :
 br_value[false;false;true;true]=S(br_value[true;true;false;true]).
Proof. reflexivity. Qed.
Example direct_decrement :
 csteps br_tm 2(br_front StA[S3;S0][S2;S3])=
 Some(br_front StA[S3;S0][S0;S3]).
Proof. reflexivity. Qed.
Example carry_decrement :
 csteps br_tm 14(br_front StA[S3;S2][S0;S0;S2;S1])=
 Some(br_front StA[S3;S2][S2;S2;S0;S1]).
Proof. reflexivity. Qed.
Example nonempty_finish :
 csteps br_tm 7(br_front StA[S3;S1][S0;S1])=
 Some(br_front StA[S2;S3;S1][S3]).
Proof. reflexivity. Qed.
Example first_growth : csteps br_tm 13(br_main 0)=Some(br_main 1).
Proof. reflexivity. Qed.
Example empty_block_enters_blank_B :
 csteps br_tm 1(br_front StA[S3;S1][S1])=Some(StB,([S1;S3;S1],S0,[])).
Proof. reflexivity. Qed.
Example empty_block_invalid_finish :
 csteps br_tm 4(br_front StA[S3;S1][S1])<>Some(br_front StA[S3;S1][S3]).
Proof. discriminate. Qed.
