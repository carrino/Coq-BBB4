From Coq Require Import List Arith Bool.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn17PairedZeroCounter Require Import PairedZero.
Import ListNotations.
Example actual_entry : csteps pz_tm 5 c0=Some(pz_main[true]).
Proof. reflexivity. Qed.
Example direct_increment_context :
 csteps pz_tm 4(StA,([S2;S0;S3;S1],S2,[S2;S0]))=
 Some(StA,([S2;S2;S3;S1],S0,[S2;S0])).
Proof. reflexivity. Qed.
Example carry_increment : csteps pz_tm 8(pz_main[true;false;true])=Some(pz_main[false;true;true]).
Proof. reflexivity. Qed.
Example checksum_zero_overflow : csteps pz_tm 13(pz_main[true;true])=Some(pz_main[false;false;true]).
Proof. reflexivity. Qed.
Example checksum_one_overflow : csteps pz_tm 9(pz_main[true])=Some(pz_main[true;true]).
Proof. reflexivity. Qed.
Example empty_word_is_safe : csteps pz_tm 5(pz_main[])=Some(pz_main[true]).
Proof. reflexivity. Qed.
Example wrong_head_invalidates_overflow :
 csteps pz_tm 9(StA,([S2;S2],S2,[]))<>Some(pz_main[false;true]).
Proof. discriminate. Qed.
Example checksum_excludes_head_two : forall n,pz_head(repeat true n)<>S2.
Proof. intros n H;destruct(pz_head_max n)as[E|E];congruence. Qed.
