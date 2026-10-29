From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn19BinaryTrio Require Import BinaryTrio.
Import ListNotations.
Example entry_S001 : csteps(bt_tm 0)6 c0=Some(bt_main[true]K1[]).
Proof. reflexivity. Qed.
Example entry_S002 : csteps(bt_tm 1)5 c0=Some(bt_main[true]K1[]).
Proof. reflexivity. Qed.
Example entry_S003 : csteps(bt_tm 2)6 c0=Some(bt_main[true]K3[]).
Proof. reflexivity. Qed.
Example direct_increment : forall v,
 csteps(bt_tm v)3(bt_back StB(bt_enc[false;true])[S2;S1;S3])=
 Some(bt_front StA(bt_enc[true;true])[S2;S1;S3]).
Proof. reflexivity. Qed.
Example carry_increment_context : forall v,
 csteps(bt_tm v)15(bt_back StB(bt_enc[true;true;true;false;true;false])[S1;S0;S3])=
 Some(bt_front StA(bt_enc[false;false;false;true;true;false])[S1;S0;S3]).
Proof. reflexivity. Qed.
Example even_overflow : forall v,
 csteps(bt_tm v)8(bt_back StB(bt_enc[true;true])[S1;S0])=
 Some(bt_front StA(bt_enc[false;true])[S2;S1;S0]).
Proof. reflexivity. Qed.
Example empty_double_overflow : forall v,
 csteps(bt_tm v)2(bt_back StB[][S2;S3])=Some(bt_main[true]K3[]).
Proof. reflexivity. Qed.
Example head_one_requires_checksum : forall v,~bt_valid v[false]K1.
Proof. intros v H;discriminate. Qed.
Example wrong_checksum_exposes_blank_B : forall v,
 match csteps(bt_tm v)8(bt_main[false]K1[])with
 |Some(StB,(_,S0,r))=>all_blank r=true|_=>False end.
Proof. reflexivity. Qed.
Example all_true_cannot_have_checksum_two : forall n,~bt_valid 2(repeat true n)K21.
Proof. intros n H;exact(bt_true_not_two n H). Qed.
Example odd_length_required_at_three : forall v,~bt_valid v[true;true]K3.
Proof. intros v H;discriminate. Qed.
Example corrupted_pair_invalidates_increment :
 csteps(bt_tm 0)3(bt_back StB[S3;S2;S3;S3][S1])<>
 Some(bt_front StA(bt_enc[true;true])[S1]).
Proof. discriminate. Qed.
