(** Binary-count transport for the universal cut rules. No large count is
    unfolded, and no long repeated word is constructed. *)
From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement CTape Spec Census TotalCompletion OneStateReach.
From BBB24Burn21S032Finite Require Import CutMacros.
Import ListNotations.
Definition sf_count(n:N):nat := N.to_nat n.
Lemma sf_count_add : forall a b,sf_count(a+b)=sf_count a+sf_count b.
Proof. intros a b;unfold sf_count;apply N2Nat.inj_add. Qed.
Lemma sf_count_le : forall a b,(a<=b)%N ->sf_count a<=sf_count b.
Proof. intros a b H;unfold sf_count;apply Nat.compare_le_iff;rewrite <-N2Nat.inj_compare;exact H. Qed.
Lemma sf_comp : forall a b c d e,
 csteps sc_tm(sf_count a)c=Some d ->csteps sc_tm(sf_count b)d=Some e ->
 csteps sc_tm(sf_count(a+b))c=Some e.
Proof. intros a b c d e H H';rewrite sf_count_add,csteps_add,H;exact H'. Qed.
Ltac sf_binary := unfold sf_count;
 repeat first[rewrite N2Nat.inj_add|rewrite N2Nat.inj_mul].
Theorem sf_N_bulk : forall n a r,
 csteps sc_tm(sf_count(n*(2*a+16)+5*n*n))
 (sc_cut(sf_count a)(repeat S3(sf_count(2*n))++r))=
 Some(sc_cut(sf_count(a+5*n))r).
Proof. intros n a r;sf_binary;apply sc_bulk. Qed.
Theorem sf_N_one : forall a r,csteps sc_tm(sf_count(2*a+17))
 (sc_cut(sf_count a)(S1::r))=Some(sc_cut(sf_count(a+4))r).
Proof. intros a r;sf_binary;apply sc_cut_one. Qed.
Theorem sf_N_zero : forall a r,csteps sc_tm(sf_count(2*a+22))
 (sc_cut(sf_count a)(S0::r))=Some(sc_cut(sf_count 2)(repeat S3(sf_count(a+2))++S1::r)).
Proof. intros a r;sf_binary;apply sc_cut_zero. Qed.
Theorem sf_N_blank : forall a,csteps sc_tm(sf_count(2*a+22))
 (sc_cut(sf_count a)[])=Some(sc_cut(sf_count 2)(repeat S3(sf_count(a+2))++[S1])).
Proof. intro a;sf_binary;apply sc_cut_blank. Qed.
Theorem sf_N_three_one : forall a r,csteps sc_tm(sf_count(2*a+24))
 (sc_cut(sf_count a)(S3::S1::r))=Some(sc_cut(sf_count 2)(repeat S3(sf_count(a+2))++S0::S3::r)).
Proof. intros a r;sf_binary;apply sc_cut_three_one. Qed.
Theorem sf_N_bridge : forall a r,csteps sc_tm(sf_count(a+22))
 (sc_cut(sf_count a)(S3::S0::S3::r))=Some(sc_Q(sf_count(a+6))r).
Proof. intros a r;sf_binary;apply sc_cut_three_zero_three. Qed.
Theorem sf_N_Qblank : forall n,csteps sc_tm(sf_count(n+7))
 (sc_Q(sf_count(n+1))[])=Some(sc_cut(sf_count 2)(repeat S3(sf_count n)++[S1])).
Proof. intro n;sf_binary;rewrite Nat.add_1_r.
 change(csteps sc_tm(N.to_nat n+7)(sc_Q(S(N.to_nat n))[S0])=
 Some(sc_cut 2(repeat S3(N.to_nat n)++[S1]))).
 exact(sc_Q_zero(N.to_nat n)[]). Qed.
Theorem sf_N_unprotected : forall a,csteps sc_tm(sf_count(a+14))
 (sc_cut(sf_count a)[S3])=Some(StB,(S2::repeat S1(sf_count(a+3)),S0,[])).
Proof. intro a;sf_binary;apply sc_unprotected_three. Qed.
Theorem sf_N_before_unprotected : forall a,csteps sc_tm(sf_count(a+13))
 (sc_cut(sf_count a)[S3])=Some(sc_Q(sf_count(a+3))[S3]).
Proof. intro a;sf_binary;apply sc_boot. Qed.
Definition sf_word(k:N)(b:option Sym)(j:N) := repeat S3(sf_count k)++
 match b with None=>[]|Some x=>x::repeat S3(sf_count j)end.
Lemma sf_radd : forall k h,repeat S3(sf_count(k+h))=repeat S3(sf_count k)++repeat S3(sf_count h).
Proof. intros k h;rewrite sf_count_add,repeat_app;reflexivity. Qed.
Lemma sf_small0 : sf_count 0=0. Proof. reflexivity. Qed.
Lemma sf_r0 : repeat S3(sf_count 0)=[] . Proof. reflexivity. Qed.
Lemma sf_r1 : repeat S3(sf_count 1)=[S3]. Proof. reflexivity. Qed.
Lemma sf_r2 : repeat S3(sf_count 2)=[S3;S3]. Proof. reflexivity. Qed.
Lemma sf_score_count : score=sf_count scoreN.
Proof. unfold score,sf_count;reflexivity. Qed.
Lemma sf_bound_count : sf_count 72057594037927936%N=N.to_nat 72057594037927936%N.
Proof. reflexivity. Qed.
Lemma sf_total : Total sc_tm.
Proof. intros q h;unfold sc_tm;eexists;reflexivity. Qed.
Theorem sf_nonhalt : NonHalt sc_tm.
Proof. apply ore_total_nonhalt;exact sf_total. Qed.
Theorem sf_B_forever_from_escape : forall d l,
 csteps sc_tm d c0=Some(StB,(l,S0,[])) ->
 forall k,d<=k ->VisitsAt sc_tm StB k.
Proof.
 intros d l E k Hk.
 exists(lift(StB,(repeat S2(k-d)++l,S0,[])));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift.
 replace k with(d+(k-d))at 1 by lia;rewrite csteps_add,E;apply sc_blank_B_drift.
Qed.
Theorem sf_bound_from_escape : forall d l,
 csteps sc_tm d c0=Some(StB,(l,S0,[])) ->QHBound d sc_tm.
Proof.
 intros d l E q s[Hv Hquiet];destruct(le_lt_dec d s);[|lia].
 destruct q.
 - destruct Hv as(c&Ec&Hs);destruct(sf_B_forever_from_escape d l E s l0)as(c'&Ec'&Hs').
   rewrite Ec in Ec';injection Ec' as <-;congruence.
 - exfalso;apply(Hquiet(S s));[lia|apply(sf_B_forever_from_escape d l E);lia].
Qed.
