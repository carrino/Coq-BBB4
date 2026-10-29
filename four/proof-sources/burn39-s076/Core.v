(** Exact frozen S076: supported whole-word crossing programs. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census TotalCompletion OneStateReach.
Import ListNotations.
Definition s76_tm:TM:=fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DR StB
 |StA,S2=>mkTrans S1 DR StB |StA,S3=>mkTrans S2 DL StB
 |StB,S0=>mkTrans S2 DR StB |StB,S1=>mkTrans S3 DR StA
 |StB,S2=>mkTrans S1 DL StA |StB,S3=>mkTrans S0 DL StB end).
Definition s76_front q l r:cconf:=(q,(l,chd r,ctl r)).
Definition s76_back q l r:cconf:=(q,(ctl l,chd l,r)).
Definition s76_left r:cconf:=(StA,([],S0,r)).
Fixpoint s76_P n:list Sym:=match n with 0=>[]|S n=>S1::S1::S0::s76_P n end.
Fixpoint s76_Q n:list Sym:=match n with 0=>[]|S n=>S2::S2::S3::s76_Q n end.
Fixpoint s76_E n:list Sym:=match n with 0=>[]|S n=>S0::S1::S1::s76_E n end.
Fixpoint s76_T n:list Sym:=match n with 0=>[]|S n=>S2::S1::s76_T n end.
Fixpoint s76_V n:list Sym:=match n with 0=>[]|S n=>S1::S0::s76_V n end.
Fixpoint s76_L n:list Sym:=match n with 0=>[]|S n=>S3::S1::s76_L n end.
Fixpoint s76_Z n:list Sym:=match n with 0=>[]|S n=>S0::S1::s76_Z n end.
Definition s76_U:list Sym:=[S1;S0;S0;S1;S0;S1;S0].
Definition s76_G:list Sym:=[S2;S2;S3;S2;S3;S2;S2;S3;S1;S3;S2].
Definition s76_support n:=s76_Q n++s76_G.
Definition s76_main n w:=s76_left(s76_U++s76_P n++w).
Lemma s76_P_shift : forall n r,s76_P n++S1::S1::S0::r=S1::S1::S0::(s76_P n++r).
Proof. induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma s76_Q_shift : forall n r,s76_Q n++S2::S2::S3::r=S2::S2::S3::(s76_Q n++r).
Proof. induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma s76_E_shift : forall n r,s76_E n++S0::S1::S1::r=S0::S1::S1::(s76_E n++r).
Proof. induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma s76_L_shift : forall n r,s76_L n++S3::S1::r=S3::S1::(s76_L n++r).
Proof. induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma s76_Z_shift : forall n r,s76_Z n++S0::S1::r=S0::S1::(s76_Z n++r).
Proof. induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma s76_rotate_Z : forall n r,S1::(s76_Z n++r)=s76_V n++S1::r.
Proof. induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma s76_rotate_E : forall n r,S1::S1::(s76_E n++r)=s76_P n++S1::S1::r.
Proof. induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma s76_RP3 : forall l r,
 csteps s76_tm 3(s76_front StB l(S1::S1::S0::r))=Some(s76_front StB(S2::S2::S3::l)r).
Proof. reflexivity. Qed.
Lemma s76_RP : forall n l r,
 csteps s76_tm(3*n)(s76_front StB l(s76_P n++r))=Some(s76_front StB(s76_Q n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(3*S n)with(3+3*n)by lia;rewrite csteps_add.
 change(match csteps s76_tm 3(s76_front StB l(S1::S1::S0::(s76_P n++r)))with
 |Some cc=>csteps s76_tm(3*n)cc|None=>None end=Some(s76_front StB(S2::S2::S3::(s76_Q n++l))r)).
 rewrite s76_RP3,IHn,s76_Q_shift;reflexivity.
Qed.
Lemma s76_RT2 : forall l r,
 csteps s76_tm 2(s76_front StA l(S2::S1::r))=Some(s76_front StA(S3::S1::l)r).
Proof. reflexivity. Qed.
Lemma s76_RT : forall n l r,
 csteps s76_tm(2*n)(s76_front StA l(s76_T n++r))=Some(s76_front StA(s76_L n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(2*S n)with(2+2*n)by lia;rewrite csteps_add.
 change(match csteps s76_tm 2(s76_front StA l(S2::S1::(s76_T n++r)))with
 |Some cc=>csteps s76_tm(2*n)cc|None=>None end=Some(s76_front StA(S3::S1::(s76_L n++l))r)).
 rewrite s76_RT2,IHn,s76_L_shift;reflexivity.
Qed.
Lemma s76_LL4 : forall l r,
 csteps s76_tm 4(s76_back StB(S3::S1::l)r)=Some(s76_back StB l(S0::S1::r)).
Proof. reflexivity. Qed.
Lemma s76_LL : forall n l r,
 csteps s76_tm(4*n)(s76_back StB(s76_L n++l)r)=Some(s76_back StB l(s76_Z n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(4*S n)with(4+4*n)by lia;rewrite csteps_add.
 change(match csteps s76_tm 4(s76_back StB(S3::S1::(s76_L n++l))r)with
 |Some cc=>csteps s76_tm(4*n)cc|None=>None end=Some(s76_back StB l(S0::S1::(s76_Z n++r)))).
 rewrite s76_LL4,IHn,s76_Z_shift;reflexivity.
Qed.
Theorem s76_Q_train : forall a l r,
 csteps s76_tm(6*a+9)(s76_back StB(S2::S2::S3::l)(s76_T a++S0::r))=
 Some(s76_back StB l(S0::S0::(s76_V a++S1::S1::r))).
Proof.
 intros a l r;replace(6*a+9)with(3+(2*a+(1+(4*a+5))))by lia;rewrite csteps_add.
 change(csteps s76_tm(2*a+(1+(4*a+5)))(s76_front StA(S3::S1::S3::l)(s76_T a++S0::r))=
 Some(s76_back StB l(S0::S0::(s76_V a++S1::S1::r)))).
 rewrite csteps_add,s76_RT,csteps_add.
 change(csteps s76_tm(4*a+5)(s76_back StB(s76_L a++S3::S1::S3::l)(S1::r))=
 Some(s76_back StB l(S0::S0::(s76_V a++S1::S1::r)))).
 rewrite csteps_add,s76_LL.
 change(Some(s76_back StB l(S0::S0::S1::(s76_Z a++S1::r)))=
 Some(s76_back StB l(S0::S0::(s76_V a++S1::S1::r)))).
 rewrite s76_rotate_Z;reflexivity.
Qed.
Lemma s76_LQ9 : forall l r,
 csteps s76_tm 9(s76_back StB(S2::S2::S3::l)(S0::r))=Some(s76_back StB l(S0::S0::S1::S1::r)).
Proof. reflexivity. Qed.
Lemma s76_LQ : forall n l r,
 csteps s76_tm(9*n)(s76_back StB(s76_Q n++l)(S0::r))=
 Some(s76_back StB l(S0::(s76_E n++r))).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(9*S n)with(9+9*n)by lia;rewrite csteps_add.
 change(match csteps s76_tm 9(s76_back StB(S2::S2::S3::(s76_Q n++l))(S0::r))with
 |Some cc=>csteps s76_tm(9*n)cc|None=>None end=Some(s76_back StB l(S0::S0::S1::S1::(s76_E n++r)))).
 rewrite s76_LQ9,IHn,s76_E_shift;reflexivity.
Qed.
Lemma s76_wall31 : forall r,
 csteps s76_tm 31(s76_back StB s76_G(S0::r))=Some(s76_left(s76_U++S1::S1::S0::S1::S1::r)).
Proof. reflexivity. Qed.
Theorem s76_zero_gate : forall n r,
 csteps s76_tm(9*n+31)(s76_back StB(s76_support n)(S0::r))=
 Some(s76_main(S n)(S1::S1::r)).
Proof.
 intros n r;unfold s76_support;rewrite csteps_add,s76_LQ,s76_wall31.
 unfold s76_main,s76_left;cbn[s76_P];rewrite s76_rotate_E;reflexivity.
Qed.
Theorem s76_train_gate : forall n a r,
 csteps s76_tm(9*S n+6*a+31)(s76_back StB(s76_support(S n))(s76_T a++S0::r))=
 Some(s76_main(S(S n))(s76_V a++S1::S1::r)).
Proof.
 intros n a r;replace(9*S n+6*a+31)with((6*a+9)+(9*n+31))by lia;rewrite csteps_add.
 change(match csteps s76_tm(6*a+9)(s76_back StB(S2::S2::S3::s76_support n)(s76_T a++S0::r))with
 |Some cc=>csteps s76_tm(9*n+31)cc|None=>None end=Some(s76_main(S(S n))(s76_V a++S1::S1::r))).
 rewrite s76_Q_train,s76_zero_gate.
 unfold s76_main,s76_left;cbn[s76_P app].
 rewrite s76_P_shift;reflexivity.
Qed.
Lemma s76_start34 : forall r,
 csteps s76_tm 34(s76_left(s76_U++r))=Some(s76_front StB s76_G r).
Proof. reflexivity. Qed.
Theorem s76_read_gate : forall n w,
 csteps s76_tm(3*n+34)(s76_main n w)=Some(s76_front StB(s76_support n)w).
Proof.
 intros n w;replace(3*n+34)with(34+3*n)by lia;unfold s76_main.
 rewrite csteps_add,s76_start34,s76_RP;reflexivity.
Qed.
Theorem s76_main_from_normalizer : forall n w v a r c,
 (forall l,csteps s76_tm c(s76_front StB l w)=Some(s76_back StB l(s76_T a++S0::r)))->
 v=s76_V a++S1::S1::r ->
 csteps s76_tm(12*S n+65+c+6*a)(s76_main(S n)w)=Some(s76_main(S(S n))v).
Proof.
 intros n w v a r c H Hv;replace(12*S n+65+c+6*a)with((3*S n+34)+(c+(9*S n+6*a+31)))by lia.
 rewrite csteps_add,s76_read_gate,csteps_add,H,s76_train_gate,Hv;reflexivity.
Qed.
