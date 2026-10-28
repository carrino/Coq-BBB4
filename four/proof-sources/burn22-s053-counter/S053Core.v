(** Local sweeps and the even carry of the complete S053 table. *)
From Coq Require Import List Arith Lia Bool NArith.
From BBB24 Require Import Statement Spec CTape Census.
Import ListNotations.

Definition sc_tm:TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StB
 |StA,S2=>mkTrans S1 DR StA |StA,S3=>mkTrans S2 DL StA
 |StB,S0=>mkTrans S2 DR StB |StB,S1=>mkTrans S3 DL StB
 |StB,S2=>mkTrans S3 DR StB |StB,S3=>mkTrans S1 DR StA end).
Definition sc_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition sc_back q l r:cconf := (q,(ctl l,chd l,r)).
Definition sc_C a b := sc_back StB(repeat S3 b)(repeat S3 a++[S1]).
Definition sc_D a b := sc_back StB(repeat S3 b)(S2::S2::(repeat S3 a++[S1])).
Definition sc_main a b:cconf := (StA,(repeat S1 a++repeat S3 b,S0,[])).
Definition sc_main_two a:cconf := (StA,(repeat S1 a++[S2],S0,[])).

Lemma sc_repeat_shift : forall (x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma sc_repeat_end : forall (x:Sym)n,repeat x n++[x]=repeat x(n+1).
Proof. intros x n;rewrite sc_repeat_shift,app_nil_r;replace(n+1)with(S n)by lia;reflexivity. Qed.
Lemma sc_repeat_join : forall (x:Sym)n m l,
 repeat x n++repeat x m++l=repeat x(n+m)++l.
Proof. intros x n m l;rewrite repeat_app,app_assoc;reflexivity. Qed.
Lemma sc_B_right_twos : forall n l r,
 csteps sc_tm n(sc_front StB l(repeat S2 n++r))=
 Some(sc_front StB(repeat S3 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app sc_front csteps cstep sc_tm ctape_move chd ctl].
 change(csteps sc_tm n(sc_front StB(S3::l)(repeat S2 n++r))=
 Some(sc_front StB(S3::(repeat S3 n++l))r)).
 rewrite IHn,sc_repeat_shift;reflexivity.
Qed.
Lemma sc_A_right_twos : forall n l r,
 csteps sc_tm n(sc_front StA l(repeat S2 n++r))=
 Some(sc_front StA(repeat S1 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app sc_front csteps cstep sc_tm ctape_move chd ctl].
 change(csteps sc_tm n(sc_front StA(S1::l)(repeat S2 n++r))=
 Some(sc_front StA(S1::(repeat S1 n++l))r)).
 rewrite IHn,sc_repeat_shift;reflexivity.
Qed.
Lemma sc_B_left_ones : forall n l r,
 csteps sc_tm n(sc_back StB(repeat S1 n++l)r)=
 Some(sc_back StB l(repeat S3 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app sc_back csteps cstep sc_tm ctape_move chd ctl].
 change(csteps sc_tm n(sc_back StB(repeat S1 n++l)(S3::r))=
 Some(sc_back StB l(S3::(repeat S3 n++r)))).
 rewrite IHn,sc_repeat_shift;reflexivity.
Qed.
Lemma sc_A_left_threes : forall n l r,
 csteps sc_tm n(sc_back StA(repeat S3 n++l)r)=
 Some(sc_back StA l(repeat S2 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app sc_back csteps cstep sc_tm ctape_move chd ctl].
 change(csteps sc_tm n(sc_back StA(repeat S3 n++l)(S2::r))=
 Some(sc_back StA l(S2::(repeat S2 n++r)))).
 rewrite IHn,sc_repeat_shift;reflexivity.
Qed.
Lemma sc_pair : forall l r,
 csteps sc_tm 10(sc_back StB(S3::S3::l)(S3::S3::r))=
 Some(sc_back StB l(S3::S3::S2::S2::r)).
Proof. intros l r;reflexivity. Qed.
Lemma sc_pairs : forall n l r,
 csteps sc_tm(10*n)(sc_back StB(repeat S3(2*n)++l)(S3::S3::r))=
 Some(sc_back StB l(S3::S3::(repeat S2(2*n)++r))).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(10*S n)with(10+10*n)by lia.
 replace(2*S n)with(S(S(2*n)))by lia;cbn[repeat app].
 rewrite csteps_add,sc_pair,IHn,sc_repeat_shift,sc_repeat_shift;reflexivity.
Qed.
Lemma sc_blank_C : forall m r,
 csteps sc_tm(m+7)(sc_back StB[](S3::S3::(repeat S2 m++S3::r)))=
 Some(sc_back StB(repeat S3(m+4))r).
Proof.
 intros m r;replace(m+7)with(4+S(S(S m)))by lia;rewrite csteps_add.
 change(csteps sc_tm(S(S(S m)))(sc_front StB[](repeat S2(S(S(S m)))++S3::r))=
 Some(sc_back StB(repeat S3(m+4))r)).
 rewrite sc_B_right_twos,app_nil_r.
 replace(m+4)with(S(S(S(S m))))by lia;reflexivity.
Qed.
Theorem sc_even : forall n r,
 csteps sc_tm(12*n+7)(sc_back StB(repeat S3(2*n))(S3::S3::S3::r))=
 Some(sc_back StB(repeat S3(2*n+4))r).
Proof.
 intros n r;replace(12*n+7)with(10*n+(2*n+7))by lia.
 rewrite <-(app_nil_r(repeat S3(2*n)))at 1.
 rewrite csteps_add,sc_pairs,sc_blank_C;reflexivity.
Qed.
Lemma sc_odd_boundary : forall m r,
 csteps sc_tm(m+7)(sc_back StB[S3](S3::S3::(repeat S2 m++S3::r)))=
 Some(sc_front StA(repeat S1(S m)++[S3;S3;S2])(S3::r)).
Proof.
 intros m r;replace(m+7)with(7+m)by lia;rewrite csteps_add.
 change(csteps sc_tm m(sc_front StA[S1;S3;S3;S2](repeat S2 m++S3::r))=
 Some(sc_front StA(repeat S1(S m)++[S3;S3;S2])(S3::r))).
 rewrite sc_A_right_twos,sc_repeat_shift;reflexivity.
Qed.
Theorem sc_odd_prepare : forall n r,
 csteps sc_tm(12*n+7)
 (sc_back StB(repeat S3(2*n+1))(S3::S3::S3::r))=
 Some(sc_front StA(repeat S1(2*n+1)++[S3;S3;S2])(S3::r)).
Proof.
 intros n r;replace(12*n+7)with(10*n+(2*n+7))by lia.
 rewrite repeat_app.
 change(csteps sc_tm(10*n+(2*n+7))
 (sc_back StB(repeat S3(2*n)++[S3])(S3::S3::S3::r))=
 Some(sc_front StA(repeat S1(2*n+1)++[S3;S3;S2])(S3::r))).
 rewrite csteps_add,sc_pairs,sc_odd_boundary.
 replace(S(2*n))with(2*n+1)by lia;reflexivity.
Qed.
Lemma sc_start : forall a b,
 csteps sc_tm(a+1)(sc_main a b)=Some(sc_C a b).
Proof.
 intros a b;replace(a+1)with(1+a)by lia;rewrite csteps_add.
 change(csteps sc_tm a(sc_back StB(repeat S1 a++repeat S3 b)[S1])=Some(sc_C a b)).
 rewrite sc_B_left_ones;reflexivity.
Qed.
Lemma sc_C_three : forall a b,
 csteps sc_tm 3(sc_C(S a)(S b))=Some(sc_D a b).
Proof. intros a b;reflexivity. Qed.
Example sc_entry : csteps sc_tm 51 c0=Some(sc_main 3 3).
Proof. reflexivity. Qed.
