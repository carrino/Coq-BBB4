From Coq Require Import List Arith.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn30S020Counter Require Import BinaryCuts.
Import ListNotations.
Example actual_blank_cut : csteps s20_tm 176 c0=Some(s20_cut 0(s20_O++s20_E)).
Proof. exact s20_blank_entry. Qed.
Example no_parity_restriction :
 csteps s20_tm 178(s20_cut 1(s20_Z++s20_E))=
 Some(s20_cut 2(s20_O++s20_E)).
Proof. exact(s20_increment 1 0 s20_E). Qed.
Example two_carries :
 csteps s20_tm 274(s20_cut 2(s20_pow s20_O 2++s20_Z++s20_E))=
 Some(s20_cut 3(s20_pow s20_Z 2++s20_O++s20_E)).
Proof. exact(s20_increment 2 2 s20_E). Qed.
Example end_overflow :
 csteps s20_tm 281(s20_cut 2(s20_O++s20_E))=
 Some(s20_cut 0(s20_O++s20_pow s20_Z 2++s20_G 1)).
Proof. exact(s20_overflow_E 2 1). Qed.
Example tag_overflow :
 csteps s20_tm 276(s20_cut 1(s20_O++s20_G 2))=
 Some(s20_cut 2(s20_Z++s20_O++s20_pow s20_Z 2++s20_E)).
Proof. exact(s20_overflow_G 1 1 2). Qed.
Example empty_counter_allowed :
 csteps s20_tm 147(s20_cut 0 s20_E)=Some(s20_cut 0(s20_O++s20_G 0)).
Proof. exact(s20_overflow_E 0 0). Qed.
Example unmarked_B_drifts : forall n l,
 csteps s20_tm n(StB,(l,S0,[]))=Some(StB,(repeat S1 n++l,S0,[])).
Proof.
 induction n;intro l;[reflexivity|].
 change(csteps s20_tm n(StB,(S1::l,S0,[]))=
 Some(StB,(S1::(repeat S1 n++l),S0,[]))).
 rewrite IHn.
 assert(E:forall m r,repeat S1 m++S1::r=S1::(repeat S1 m++r)).
 {intro m;induction m;intro r;cbn;[reflexivity|now rewrite IHm]. }
 now rewrite E.
Qed.
Example broad_old_grammar_really_escapes :
 csteps s20_tm 29(StA,([],S0,[S3;S1;S3;S1;S1]))=
 Some(StB,([S0;S2;S2;S0;S2;S3;S2;S0],S0,[])).
Proof. reflexivity. Qed.
Example A0_boundary_really_escapes :
 csteps s20_tm 3(StA,([S3],S0,[]))=Some(StB,([S0;S2],S0,[])).
Proof. reflexivity. Qed.
Example A2_boundary_really_escapes :
 csteps s20_tm 3(StA,([S3],S2,[]))=Some(StB,([S0;S3],S0,[])).
Proof. reflexivity. Qed.
Example unsafe_word_is_not_a_main_cut : forall n w,
 s20_cut n w<>(StA,([],S0,[S3;S1;S3;S1;S1])).
Proof. intros n w;discriminate. Qed.
Print Assumptions s20_sound.
