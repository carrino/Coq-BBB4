From Coq Require Import List Arith.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn23S004S005Unary Require Import UnaryPhases.
Import ListNotations.
Example actual_blank_entry : forall bit,csteps(pu_tm bit)1 c0=Some(pu_main 0[]).
Proof. apply pu_entry_blank. Qed.
Example actual_first_left_cut : forall bit,csteps(pu_tm bit)23 c0=Some(pu_main 0 pu_T1).
Proof. intro bit;replace 23 with(1+22)by reflexivity;rewrite csteps_add,pu_entry_blank;exact(pu_phase0 bit 0). Qed.
Example actual_second_left_cut : forall bit,csteps(pu_tm bit)53 c0=Some(pu_main 0 pu_T2).
Proof.
 intro bit;replace 53 with(23+30)by reflexivity;rewrite csteps_add,actual_first_left_cut;exact(pu_phase1 bit 0).
Qed.
Example actual_third_left_cut : forall bit,csteps(pu_tm bit)123 c0=Some(pu_main 0 pu_T3).
Proof. intro bit;replace 123 with(53+70)by reflexivity;rewrite csteps_add,actual_second_left_cut;exact(pu_phase2 bit 0). Qed.
Example actual_first_full_cycle : forall bit,csteps(pu_tm bit)229 c0=Some(pu_main 2[]).
Proof. intro bit;replace 229 with(1+228)by reflexivity;rewrite csteps_add,pu_entry_blank;exact(pu_cycle bit 0). Qed.
Example odd_block_count_cycle : forall bit,csteps(pu_tm bit)460(pu_main 1[])=Some(pu_main 3[]).
Proof. intro bit;exact(pu_cycle bit 1). Qed.
Example forward_nonblank_context : forall bit,
 csteps(pu_tm bit)41(pu_front StA[S3;S3;S2;S0](pu_P++[S3;S1]))=
 Some(pu_front StA(S3::S3::(pu_Q bit++[S2;S0]))[S3;S1]).
Proof. intro bit;apply pu_forward_one. Qed.
Example backward_nonblank_context : forall bit,
 csteps(pu_tm bit)17(StA,(S3::S1::(pu_Q bit++[S2;S0]),pu_X bit,[S3;S1]))=
 Some(StA,([S3;S1;S2;S0],pu_X bit,pu_R++[S3;S1])).
Proof. intro bit;apply pu_backward_one. Qed.
Example S004_backward_head : pu_X false=S0.
Proof. reflexivity. Qed.
Example S005_backward_head : pu_X true=S2.
Proof. reflexivity. Qed.
Example A_zero_and_two_same : forall bit,
 pu_tm bit StA S0=pu_tm bit StA S2.
Proof. reflexivity. Qed.
Example B_two_distinguishes_tables : pu_tm false StB S2<>pu_tm true StB S2.
Proof. discriminate. Qed.
Example broad_block_grammar_is_unsafe : forall bit,
 csteps(pu_tm bit)9(StB,([],S0,[S1;S2;S1]))=
 Some(StB,([S1;pu_X bit;S1],S0,[])).
Proof. intros[];reflexivity. Qed.
Example suffix_2121_alone_is_unsafe : forall bit,
 csteps(pu_tm bit)47(StB,([],S0,[S1;S2;S1;S2;S1;S2;S1]))=
 Some(StB,([S1;S3;S1;pu_X bit;S3;S1;S1],S0,[])).
Proof. intros[];reflexivity. Qed.
Example blank_B_tail_drifts : forall bit n l,
 csteps(pu_tm bit)n(StB,(l,S0,[]))=Some(StB,(repeat S3 n++l,S0,[])).
Proof.
 intros bit n;induction n;intro l;[reflexivity|].
 change(csteps(pu_tm bit)n(StB,(S3::l,S0,[]))=Some(StB,(S3::(repeat S3 n++l),S0,[]))).
 rewrite IHn.
 assert(E:forall m r,repeat S3 m++S3::r=S3::(repeat S3 m++r)).
 {intro m;induction m;intro r;cbn;[reflexivity|now rewrite IHm]. }
 now rewrite E.
Qed.
Example terminal0_does_not_add_one_block : forall bit,
 csteps(pu_tm bit)22(pu_main 0[])<>Some(pu_main 1[]).
Proof. intro bit;pose proof(pu_phase0 bit 0)as E;change(csteps(pu_tm bit)22(pu_main 0[])=Some(pu_main 0 pu_T1))in E;rewrite E;discriminate. Qed.
Print Assumptions pu_sound.
