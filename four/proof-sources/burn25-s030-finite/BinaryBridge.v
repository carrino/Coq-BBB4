From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn25S030Finite Require Import Counter.
Import ListNotations.
Definition sf_count(n:N):nat := N.to_nat n.
Lemma sf_count_add : forall a b,sf_count(a+b)=sf_count a+sf_count b.
Proof. intros a b;unfold sf_count;apply N2Nat.inj_add. Qed.
Lemma sf_count_le : forall a b,(a<=b)%N ->sf_count a<=sf_count b.
Proof. intros a b H;unfold sf_count;apply Nat.compare_le_iff;rewrite <-N2Nat.inj_compare;exact H. Qed.
Lemma sf_comp : forall a b c d e,csteps s30_tm(sf_count a)c=Some d ->csteps s30_tm(sf_count b)d=Some e ->csteps s30_tm(sf_count(a+b))c=Some e.
Proof. intros a b c d e H H';rewrite sf_count_add,csteps_add,H;exact H'. Qed.
Ltac sf_binary := unfold sf_count;repeat first[rewrite N2Nat.inj_add|rewrite N2Nat.inj_mul].
Theorem sf_N_zero : forall a r,csteps s30_tm(sf_count(a+5))(s30_Q(sf_count a)(S0::r))=
 Some(s30_Q(sf_count 1)(repeat S1(sf_count a)++S0::S1::r)).
Proof. intros a r;sf_binary;apply s30_zero. Qed.
Theorem sf_N_blank : forall a,csteps s30_tm(sf_count(a+5))(s30_Q(sf_count a)[])=
 Some(s30_Q(sf_count 1)(repeat S1(sf_count a)++[S0;S1])).
Proof. intro a;sf_binary;apply s30_blank. Qed.
Theorem sf_N_pair : forall a r,csteps s30_tm(sf_count(6*a+18))(s30_Q(sf_count a)(S1::S1::r))=
 Some(s30_Q(sf_count(a+5))r).
Proof. intros a r;sf_binary;apply s30_pair. Qed.
Theorem sf_N_101 : forall a r,csteps s30_tm(sf_count(6*a+19))(s30_Q(sf_count a)(S1::S0::S1::r))=
 Some(s30_Q(sf_count(a+6))r).
Proof. intros a r;sf_binary;apply s30_onezeroone. Qed.
Theorem sf_N_bulk : forall n a r,csteps s30_tm(sf_count(n*(6*a+3)+15*n*n))
 (s30_Q(sf_count a)(repeat S1(sf_count(2*n))++r))=Some(s30_Q(sf_count(a+5*n))r).
Proof. intros n a r;sf_binary;apply s30_bulk. Qed.
Theorem sf_N_before : forall a,csteps s30_tm(sf_count 1)(s30_Q(sf_count a)[S1])=
 Some(StA,(repeat S2(sf_count a),S3,[S2])).
Proof. intro a;unfold sf_count;apply s30_exposed_before. Qed.
Theorem sf_N_after : forall a,csteps s30_tm(sf_count 2)(s30_Q(sf_count a)[S1])=
 Some(s30_back StB(repeat S2(sf_count a))[S2;S2]).
Proof. intro a;unfold sf_count;apply s30_exposed_after. Qed.
Definition sf_word(m:N)(sentinel:bool)(c:N) := repeat S1(sf_count m)++
 if sentinel then S0::repeat S1(sf_count c)else[].
Lemma sf_radd : forall a b,repeat S1(sf_count(a+b))=repeat S1(sf_count a)++repeat S1(sf_count b).
Proof. intros a b;rewrite sf_count_add,repeat_app;reflexivity. Qed.
Lemma sf_small1 : sf_count 1=1. Proof. reflexivity. Qed.
Lemma sf_small3 : sf_count 3=3. Proof. reflexivity. Qed.
Lemma sf_score_count : score=sf_count scoreN.
Proof. unfold score,sf_count;reflexivity. Qed.
Lemma sf_bound_count : sf_count 2199023255552%N=N.to_nat 2199023255552%N.
Proof. reflexivity. Qed.
Lemma sf_r0 : repeat S1(sf_count 0%N)=[]. Proof. reflexivity. Qed.
Lemma sf_r1 : repeat S1(sf_count 1%N)=[S1]. Proof. reflexivity. Qed.
Lemma sf_r2 : repeat S1(sf_count 2%N)=[S1;S1]. Proof. reflexivity. Qed.
Lemma sf_r3 : repeat S1(sf_count 3%N)=[S1;S1;S1]. Proof. reflexivity. Qed.
Lemma sf_r4 : repeat S1(sf_count 4%N)=[S1;S1;S1;S1]. Proof. reflexivity. Qed.
Lemma sf_r5 : repeat S1(sf_count 5%N)=[S1;S1;S1;S1;S1]. Proof. reflexivity. Qed.
Lemma sf_r6 : repeat S1(sf_count 6%N)=[S1;S1;S1;S1;S1;S1]. Proof. reflexivity. Qed.
Lemma sf_r7 : repeat S1(sf_count 7%N)=[S1;S1;S1;S1;S1;S1;S1]. Proof. reflexivity. Qed.
