From Coq Require Import List Arith.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn15BinaryCounter Require Import BinaryCounter.
Import ListNotations.

Example entry_boundary : csteps bc_tm 7 c0=Some(bc_main 0 S0).
Proof. reflexivity. Qed.
Example recursive_cost : bc_work 4=185.
Proof. reflexivity. Qed.
Example block_arbitrary_context :
 csteps bc_tm 5(bc_back StB[S1;S0;S3;S2][S2;S0])=
 Some(bc_front StA[S1;S0;S3;S2][S2;S0]).
Proof. reflexivity. Qed.
Example first_recursive_block :
 csteps bc_tm 17(bc_back StB[S1;S1;S1;S0;S2][S3])=
 Some(bc_front StA[S1;S1;S1;S0;S2][S3]).
Proof. reflexivity. Qed.
Example reset_arbitrary_right :
 csteps bc_tm 7(StA,([],S0,[S3;S2;S1]))=
 Some(bc_front StA[S1;S0][S3;S2;S1]).
Proof. reflexivity. Qed.
Example first_growth : csteps bc_tm 11(bc_main 0 S1)=Some(bc_main 1 S0).
Proof. reflexivity. Qed.
Example later_growth : csteps bc_tm 19(bc_main 2 S1)=Some(bc_main 3 S0).
Proof. reflexivity. Qed.
Example even_block_is_different :
 csteps bc_tm 5(bc_back StB[S1;S1;S0][])=Some(StB,([S0],S2,[S3])).
Proof. reflexivity. Qed.
