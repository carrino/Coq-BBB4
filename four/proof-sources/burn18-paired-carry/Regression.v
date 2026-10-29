From Coq Require Import List Arith Bool.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn18PairedCarry Require Import PairedCarry.
Import ListNotations.

Example actual_left_entry : csteps(pc_tm false)32 c0=Some(pc_main 2[S1]).
Proof. reflexivity. Qed.
Example actual_bounce_entry : csteps(pc_tm true)34 c0=Some(pc_main 2[S1]).
Proof. reflexivity. Qed.
Example left_zero_context :
 csteps(pc_tm false)6(pc_back StB[S0;S0;S3;S1][S2;S0;S2])=
 Some(pc_back StB[S3;S1][S2;S2;S2;S0;S2]).
Proof. reflexivity. Qed.
Example bounce_zero_context :
 csteps(pc_tm true)10(pc_back StB[S0;S0;S3;S1][S2;S0;S2])=
 Some(pc_back StB[S3;S1][S2;S2;S2;S0;S2]).
Proof. reflexivity. Qed.
Example third_digit_context : forall b,
 csteps(pc_tm b)3(pc_back StB[S1;S3;S0;S2][S3;S0])=
 Some(pc_front StA[S1;S1;S0;S2][S3;S0]).
Proof. intro b;reflexivity. Qed.
Example nonzero_left_return :
 csteps(pc_tm false)19(pc_main 1[S0;S0;S3;S2])=
 Some(pc_main 2[S2;S2;S1;S2]).
Proof. reflexivity. Qed.
Example nonzero_bounce_return :
 csteps(pc_tm true)21(pc_main 1[S0;S0;S3;S2])=
 Some(pc_main 2[S2;S2;S1;S2]).
Proof. reflexivity. Qed.
Example empty_left_return :
 csteps(pc_tm false)23(pc_main 1[S0;S0])=Some(pc_main 2[S2;S2;S1]).
Proof. reflexivity. Qed.
Example empty_bounce_return :
 csteps(pc_tm true)25(pc_main 1[S0;S0])=Some(pc_main 2[S2;S2;S1]).
Proof. reflexivity. Qed.
Example changed_right_boundary_invalid :
 csteps(pc_tm false)3(pc_back StB[S0;S1][S0])<>
 Some(pc_back StB[S1][S2;S0]).
Proof. discriminate. Qed.
Example extended_empty_boundary_invalid :
 csteps(pc_tm false)7(pc_back StB[S1;S1][S2;S1])<>
 Some(pc_front StA[S1;S1;S1;S1][S2;S1]).
Proof. discriminate. Qed.
