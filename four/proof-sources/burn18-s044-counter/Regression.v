From Coq Require Import List Arith Bool.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn18S044Counter Require Import S044Counter.
Import ListNotations.
Example actual_entry : csteps s44_tm 6 c0=Some(s44_main[true]).
Proof. reflexivity. Qed.
Example direct_increment_context :
 csteps s44_tm 4(StA,([S2;S0;S3;S1],S2,[S2;S0]))=
 Some(StA,([S2;S2;S3;S1],S0,[S2;S0])).
Proof. reflexivity. Qed.
Example carry_increment : csteps s44_tm 8(s44_main[true;false;true])=Some(s44_main[false;true;true]).
Proof. reflexivity. Qed.
Example checksum_zero_overflow : csteps s44_tm 32(s44_main[true;true])=Some(s44_main[false;false;true]).
Proof. reflexivity. Qed.
Example checksum_one_overflow : csteps s44_tm 9(s44_main[true])=Some(s44_main[true;true]).
Proof. reflexivity. Qed.
Example empty_word_is_safe : csteps s44_tm 6(s44_main[])=Some(s44_main[true]).
Proof. reflexivity. Qed.
Example auxiliary_increment_context :
 csteps s44_tm 6(StB,([S2;S2;S0;S2;S3;S1],S1,[S2;S0]))=
 Some(StB,([S0;S2;S2;S2;S3;S1],S1,[S2;S0])).
Proof. reflexivity. Qed.
Example auxiliary_empty_finish :
 csteps s44_tm 4(StB,([S2],S1,[]))=Some(StA,([S2;S2],S1,[])).
Proof. reflexivity. Qed.
Example missing_auxiliary_boundary_invalidates_cost :
 csteps s44_tm 4(StB,([],S1,[]))<>Some(StA,([S2;S2],S1,[])).
Proof. discriminate. Qed.
Example wrong_head_invalidates_overflow :
 csteps s44_tm 9(StA,([S2;S2],S2,[]))<>Some(s44_main[false;true]).
Proof. discriminate. Qed.
Example checksum_excludes_head_two : forall n,s44_head(repeat true n)<>S2.
Proof. intros n H;destruct(s44_head_max n)as[E|E];congruence. Qed.
