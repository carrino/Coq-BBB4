(** Exact left-cut rewrites only. A reachable global guard is still needed
    before these local rules can classify the original blank orbit. *)
From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement CTape.
Import ListNotations.
Definition sc_tm:TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StA
 |StA,S2=>mkTrans S1 DR StA |StA,S3=>mkTrans S2 DR StB
 |StB,S0=>mkTrans S2 DR StB |StB,S1=>mkTrans S3 DL StB
 |StB,S2=>mkTrans S0 DL StB |StB,S3=>mkTrans S1 DL StA end).
Definition sc_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition sc_back q l r:cconf := (q,(ctl l,chd l,r)).
Definition sc_cut a r:cconf := (StA,([],S0,repeat S2 a++r)).
Definition sc_Q m r := sc_front StA(repeat S1 m)r.
Lemma sc_repeat_shift : forall(x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma sc_left_ones : forall n l r,
 csteps sc_tm n(sc_back StA(repeat S1 n++l)r)=Some(sc_back StA l(repeat S2 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app sc_back csteps cstep sc_tm ctape_move chd ctl].
 change(csteps sc_tm n(sc_back StA(repeat S1 n++l)(S2::r))=
 Some(sc_back StA l(S2::(repeat S2 n++r)))).
 rewrite IHn,sc_repeat_shift;reflexivity.
Qed.
Lemma sc_right_twos : forall n l r,
 csteps sc_tm n(sc_front StA l(repeat S2 n++r))=Some(sc_front StA(repeat S1 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app sc_front csteps cstep sc_tm ctape_move chd ctl].
 change(csteps sc_tm n(sc_front StA(S1::l)(repeat S2 n++r))=
 Some(sc_front StA(S1::(repeat S1 n++l))r)).
 rewrite IHn,sc_repeat_shift;reflexivity.
Qed.
Lemma sc_B_left_ones : forall n l r,
 csteps sc_tm n(sc_back StB(repeat S1 n++l)r)=Some(sc_back StB l(repeat S3 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app sc_back csteps cstep sc_tm ctape_move chd ctl].
 change(csteps sc_tm n(sc_back StB(repeat S1 n++l)(S3::r))=
 Some(sc_back StB l(S3::(repeat S3 n++r)))).
 rewrite IHn,sc_repeat_shift;reflexivity.
Qed.
Lemma sc_B_seed : forall r,csteps sc_tm 5(StB,([],S0,S3::r))=Some(sc_cut 2 r).
Proof. reflexivity. Qed.
Theorem sc_boot : forall a r,csteps sc_tm(a+13)(sc_cut a r)=Some(sc_Q(a+3)r).
Proof.
 intros a r;replace(a+13)with(12+S a)by lia;rewrite csteps_add.
 change(csteps sc_tm(S a)(sc_front StA[S1;S1](repeat S2(S a)++r))=Some(sc_Q(a+3)r)).
 rewrite sc_right_twos;unfold sc_Q.
 replace(a+3)with(S a+2)by lia;rewrite repeat_app;reflexivity.
Qed.
Lemma sc_Q_one : forall m r,csteps sc_tm(S m)(sc_Q m(S1::r))=Some(sc_cut(S m)r).
Proof.
 intros m r.
 change(csteps sc_tm(S m)(sc_back StA(repeat S1(S m))r)=Some(sc_back StA[](repeat S2(S m)++r))).
 rewrite <-(app_nil_r(repeat S1(S m)))at 1;apply sc_left_ones.
Qed.
Lemma sc_Q_zero : forall n r,csteps sc_tm(n+7)(sc_Q(S n)(S0::r))=
 Some(sc_cut 2(repeat S3 n++S1::r)).
Proof.
 intros n r;replace(n+7)with(1+(S n+5))by lia;rewrite csteps_add.
 change(csteps sc_tm(S n+5)(sc_back StB(repeat S1(S n))(S1::r))=
 Some(sc_cut 2(repeat S3 n++S1::r))).
 rewrite <-(app_nil_r(repeat S1(S n)))at 1.
 rewrite csteps_add,sc_B_left_ones;apply sc_B_seed.
Qed.
Theorem sc_cut_one : forall a r,csteps sc_tm(2*a+17)(sc_cut a(S1::r))=Some(sc_cut(a+4)r).
Proof.
 intros a r;replace(2*a+17)with((a+13)+S(a+3))by lia.
 rewrite csteps_add,sc_boot,sc_Q_one;replace(S(a+3))with(a+4)by lia;reflexivity.
Qed.
Theorem sc_cut_pair : forall a r,csteps sc_tm(2*a+21)(sc_cut a(S3::S3::r))=Some(sc_cut(a+5)r).
Proof.
 intros a r;replace(2*a+21)with((a+13)+(3+S(S(a+3))))by lia.
 rewrite csteps_add,sc_boot,csteps_add.
 change(csteps sc_tm(S(S(a+3)))(sc_Q(S(a+3))(S1::r))=Some(sc_cut(a+5)r)).
 rewrite sc_Q_one;replace(S(S(a+3)))with(a+5)by lia;reflexivity.
Qed.
Theorem sc_cut_zero : forall a r,csteps sc_tm(2*a+22)(sc_cut a(S0::r))=
 Some(sc_cut 2(repeat S3(a+2)++S1::r)).
Proof.
 intros a r;replace(2*a+22)with((a+13)+((a+2)+7))by lia.
 rewrite csteps_add,sc_boot;replace(a+3)with(S(a+2))by lia;apply sc_Q_zero.
Qed.
Theorem sc_cut_blank : forall a,csteps sc_tm(2*a+22)(sc_cut a[])=
 Some(sc_cut 2(repeat S3(a+2)++[S1])).
Proof.
 intro a;replace(2*a+22)with((a+13)+((a+2)+7))by lia.
 rewrite csteps_add,sc_boot;replace(a+3)with(S(a+2))by lia.
 change(csteps sc_tm(a+2+7)(sc_Q(S(a+2))[S0])=Some(sc_cut 2(repeat S3(a+2)++[S1]))).
 apply sc_Q_zero.
Qed.
Theorem sc_cut_three_one : forall a r,csteps sc_tm(2*a+24)(sc_cut a(S3::S1::r))=
 Some(sc_cut 2(repeat S3(a+2)++S0::S3::r)).
Proof.
 intros a r;replace(2*a+24)with((a+13)+(3+((a+3)+5)))by lia.
 rewrite csteps_add,sc_boot,csteps_add.
 change(csteps sc_tm((a+3)+5)(sc_back StB(repeat S1(a+3))(S0::S3::r))=
 Some(sc_cut 2(repeat S3(a+2)++S0::S3::r))).
 rewrite <-(app_nil_r(repeat S1(a+3)))at 1.
 rewrite csteps_add,sc_B_left_ones;replace(a+3)with(S(a+2))by lia;apply sc_B_seed.
Qed.
Theorem sc_cut_three_zero_three : forall a r,csteps sc_tm(a+22)(sc_cut a(S3::S0::S3::r))=
 Some(sc_Q(a+6)r).
Proof.
 intros a r;replace(a+22)with((a+13)+9)by lia;rewrite csteps_add,sc_boot.
 change(Some(sc_front StA(S1::S1::S1::repeat S1(a+3))r)=Some(sc_Q(a+6)r)).
 replace(a+6)with(S(S(S(a+3))))by lia;reflexivity.
Qed.
Definition sc_bulk_cost a n := n*(2*a+16)+5*n*n.
Theorem sc_bulk : forall n a r,csteps sc_tm(sc_bulk_cost a n)(sc_cut a(repeat S3(2*n)++r))=
 Some(sc_cut(a+5*n)r).
Proof.
 induction n;intros a r.
 - unfold sc_bulk_cost;cbn;now rewrite Nat.add_0_r.
 - replace(sc_bulk_cost a(S n))with((2*a+21)+sc_bulk_cost(a+5)n)by(unfold sc_bulk_cost;nia).
   replace(2*S n)with(S(S(2*n)))by lia;cbn[repeat app].
   rewrite csteps_add,sc_cut_pair,IHn.
   replace(a+5+5*n)with(a+5*S n)by lia;reflexivity.
Qed.
Theorem sc_blank_B_drift : forall n l,csteps sc_tm n(StB,(l,S0,[]))=
 Some(StB,(repeat S2 n++l,S0,[])).
Proof.
 induction n;intro l;[reflexivity|].
 change(csteps sc_tm n(StB,(S2::l,S0,[]))=Some(StB,(S2::(repeat S2 n++l),S0,[]))).
 rewrite IHn,sc_repeat_shift;reflexivity.
Qed.
Theorem sc_unprotected_three : forall a,csteps sc_tm(a+14)(sc_cut a[S3])=
 Some(StB,(S2::repeat S1(a+3),S0,[])).
Proof. intro a;replace(a+14)with((a+13)+1)by lia;rewrite csteps_add,sc_boot;reflexivity. Qed.
Lemma sc_entry22 : csteps sc_tm 22 c0=Some(sc_cut 2[S3;S3;S1]).
Proof. exact(sc_cut_blank 0). Qed.
Lemma sc_prefix47 : csteps sc_tm 47 c0=Some(sc_cut 7[S1]).
Proof. replace 47 with(22+25)by lia;rewrite csteps_add,sc_entry22;exact(sc_cut_pair 2[S1]). Qed.
Lemma sc_prefix78 : csteps sc_tm 78 c0=Some(sc_cut 11[]).
Proof. replace 78 with(47+31)by lia;rewrite csteps_add,sc_prefix47;exact(sc_cut_one 7[]). Qed.
Lemma sc_prefix122 : csteps sc_tm 122 c0=Some(sc_cut 2(repeat S3 13++[S1])).
Proof. replace 122 with(78+44)by lia;rewrite csteps_add,sc_prefix78;exact(sc_cut_blank 11). Qed.
Print Assumptions sc_bulk.
Print Assumptions sc_cut_three_one.
Print Assumptions sc_prefix122.
Print Assumptions sc_unprotected_three.
