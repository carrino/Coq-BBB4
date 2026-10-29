(** S071 machine definition and universal context programs.
    The checked FAR certificate closes state recurrence in ActualNoSpinout. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement CTape.
Import ListNotations.
Definition s71_tm:TM:=fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DR StA
 |StA,S2=>mkTrans S3 DL StA |StA,S3=>mkTrans S2 DR StB
 |StB,S0=>mkTrans S0 DR StB |StB,S1=>mkTrans S3 DL StB
 |StB,S2=>mkTrans S0 DL StA |StB,S3=>mkTrans S1 DR StA end).
Definition s71_front q l r:cconf:=(q,(l,chd r,ctl r)).
Definition s71_back q l r:cconf:=(q,(ctl l,chd l,r)).
Fixpoint s71_pairs n:list Sym:=match n with 0=>[]|S k=>S1::S2::s71_pairs k end.
Lemma s71_shift : forall(x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma s71_A_twos : forall n l r,csteps s71_tm n
 (s71_back StA(repeat S2 n++l)r)=Some(s71_back StA l(repeat S3 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app s71_back csteps cstep s71_tm ctape_move chd ctl].
 change(csteps s71_tm n(s71_back StA(repeat S2 n++l)(S3::r))=
 Some(s71_back StA l(S3::(repeat S3 n++r)))).
 rewrite IHn,s71_shift;reflexivity.
Qed.
Lemma s71_pairs_shift : forall n l,s71_pairs n++S1::S2::l=S1::S2::(s71_pairs n++l).
Proof. induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma s71_threes_even : forall n l r,csteps s71_tm(2*n)
 (s71_front StA l(repeat S3(2*n)++r))=
 Some(s71_front StA(s71_pairs n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(2*S n)with(S(S(2*n)))by lia.
 cbn[repeat app s71_front csteps cstep s71_tm ctape_move chd ctl s71_pairs].
 change(csteps s71_tm(2*n)(s71_front StA(S1::S2::l)(repeat S3(2*n)++r))=
 Some(s71_front StA(S1::S2::(s71_pairs n++l))r)).
 rewrite IHn,s71_pairs_shift;reflexivity.
Qed.
Lemma s71_threes_odd : forall n l r,csteps s71_tm(2*n+1)
 (s71_front StA l(repeat S3(2*n+1)++r))=
 Some(s71_front StB(S2::s71_pairs n++l)r).
Proof.
 intros n l r;rewrite csteps_add.
 replace(2*n+1)with(2*n+1)by lia.
 rewrite(repeat_app S3(2*n)1),<-app_assoc,s71_threes_even.
 reflexivity.
Qed.
Theorem s71_odd_prefix : forall n l r,csteps s71_tm(4*n+3)
 (StA,(repeat S2(2*n+1)++S1::l,S0,r))=
 Some(StA,(s71_pairs n++S2::l,S0,S1::r)).
Proof.
 intros n l r;replace(2*n+1)with(S(2*n))by lia.
 replace(4*n+3)with(2+(2*n+(1+2*n)))by lia;rewrite csteps_add.
 change(csteps s71_tm(2*n+(1+2*n))
 (s71_back StA(repeat S2(2*n)++S1::l)(S0::S1::r))=
 Some(StA,(s71_pairs n++S2::l,S0,S1::r))).
 rewrite csteps_add,s71_A_twos,csteps_add.
 change(csteps s71_tm(2*n)(s71_front StA(S2::l)(repeat S3(2*n)++S0::S1::r))=
 Some(StA,(s71_pairs n++S2::l,S0,S1::r))).
 rewrite s71_threes_even;reflexivity.
Qed.
Theorem s71_even_prefix : forall n l r,csteps s71_tm(4*n+9)
 (StA,(repeat S2(2*n+2)++S1::l,S0,r))=
 Some(s71_front StA(S1::S0::S2::s71_pairs n++S2::l)r).
Proof.
 intros n l r;replace(2*n+2)with(S(2*n+1))by lia.
 replace(4*n+9)with(2+((2*n+1)+(1+((2*n+1)+4))))by lia;rewrite csteps_add.
 change(csteps s71_tm((2*n+1)+(1+((2*n+1)+4)))
 (s71_back StA(repeat S2(2*n+1)++S1::l)(S0::S1::r))=
 Some(s71_front StA(S1::S0::S2::s71_pairs n++S2::l)r)).
 rewrite csteps_add,s71_A_twos,csteps_add.
 change(csteps s71_tm((2*n+1)+4)
 (s71_front StA(S2::l)(repeat S3(2*n+1)++S0::S1::r))=
 Some(s71_front StA(S1::S0::S2::s71_pairs n++S2::l)r)).
 rewrite csteps_add,s71_threes_odd;reflexivity.
Qed.
Print Assumptions s71_even_prefix.
Print Assumptions s71_odd_prefix.

(** Short exact dictionary rules retain arbitrary left and right contexts. *)
Theorem s71_rule21 : forall l r,csteps s71_tm 3(StA,(S2::S1::l,S0,r))=
 Some(StA,(S2::l,S0,S1::r)).
Proof. reflexivity. Qed.
Theorem s71_rule20 : forall l r,csteps s71_tm 2(StA,(S2::S0::l,S0,r))=
 Some(StA,(l,S0,S0::S1::r)).
Proof. reflexivity. Qed.
Theorem s71_rule120 : forall l r,csteps s71_tm 3(StA,(S1::S2::S0::l,S0,r))=
 Some(StA,(l,S0,S0::S3::S1::r)).
Proof. reflexivity. Qed.
Theorem s71_rule121 : forall l r,csteps s71_tm 4(StA,(S1::S2::S1::l,S0,r))=
 Some(StA,(S2::l,S0,S3::S1::r)).
Proof. reflexivity. Qed.
Theorem s71_rule2121 : forall l r,csteps s71_tm 13(StA,(S2::S1::S2::S1::l,S0,r))=
 Some(s71_front StA(S2::S1::S0::S2::S2::l)r).
Proof. reflexivity. Qed.
Theorem s71_rule1022 : forall l r,csteps s71_tm 5(StA,(S1::S0::S2::S2::l,S0,r))=
 Some(s71_front StA(S2::S1::S0::S2::S2::l)r).
Proof. reflexivity. Qed.
Theorem s71_rule210220 : forall l r,csteps s71_tm 8(StA,(S2::S1::S0::S2::S2::S0::l,S0,r))=
 Some(StA,(l,S0,S3::S0::S1::S0::S1::S1::r)).
Proof. reflexivity. Qed.
Theorem s71_twos_zero : forall n l r,csteps s71_tm(n+2)
 (StA,(repeat S2(S n)++S0::l,S0,r))=
 Some(StA,(l,S0,repeat S3 n++S0::S1::r)).
Proof.
 intros n l r;replace(n+2)with(2+n)by lia;rewrite csteps_add.
 change(csteps s71_tm n(s71_back StA(repeat S2 n++S0::l)(S0::S1::r))=
 Some(StA,(l,S0,repeat S3 n++S0::S1::r))).
 rewrite s71_A_twos;reflexivity.
Qed.
Theorem s71_two_ones_zero : forall n l r,csteps s71_tm(3*n+2)
 (StA,(S2::repeat S1 n++S0::l,S0,r))=
 Some(StA,(l,S0,S0::repeat S1(S n)++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(3*S n+2)with(3+(3*n+2))by lia;rewrite csteps_add.
 change(csteps s71_tm(3*n+2)(StA,(S2::repeat S1 n++S0::l,S0,S1::r))=
 Some(StA,(l,S0,S0::repeat S1(S(S n))++r))).
 rewrite IHn,s71_shift;reflexivity.
Qed.
Theorem s71_one_two_ones_zero : forall n l r,csteps s71_tm(3*n+3)
 (StA,(S1::S2::repeat S1 n++S0::l,S0,r))=
 Some(StA,(l,S0,S0::repeat S1 n++S3::S1::r)).
Proof.
 intros[|n]l r;[reflexivity|].
 replace(3*S n+3)with(4+(3*n+2))by lia;rewrite csteps_add.
 change(csteps s71_tm(3*n+2)(StA,(S2::repeat S1 n++S0::l,S0,S3::S1::r))=
 Some(StA,(l,S0,S0::repeat S1(S n)++S3::S1::r))).
 apply s71_two_ones_zero.
Qed.
Print Assumptions s71_twos_zero.
Print Assumptions s71_two_ones_zero.
Print Assumptions s71_one_two_ones_zero.
