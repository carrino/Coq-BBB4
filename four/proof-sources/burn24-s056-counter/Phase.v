(** S056: three exact block phases. The earlier local carry proof is imported
    unchanged; no unproved blank-orbit invariant is assumed. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census.
From BBB24Burn18CounterObligations Require Import CounterObligations.
Import ListNotations.
Fixpoint sf_P k:list Sym := match k with 0=>[]|S k=>S1::S1::S3::sf_P k end.
Fixpoint sf_Q k:list Sym := match k with 0=>[]|S k=>S3::S1::S1::sf_Q k end.
Fixpoint sf_R k:list Sym := match k with 0=>[]|S k=>S1::S3::S1::sf_R k end.
Fixpoint sf_p k:list bool := match k with 0=>[]|S k=>true::false::sf_p k end.
Fixpoint sf_q k:list bool := match k with 0=>[]|S k=>false::true::sf_q k end.
Lemma sf_p_in : forall k,s56_in(sf_p k)=sf_P k.
Proof. induction k;cbn;congruence. Qed.
Lemma sf_p_out : forall k,s56_out(sf_p k)=sf_Q k.
Proof. induction k;cbn;congruence. Qed.
Lemma sf_q_in : forall k,s56_in(sf_q k)=sf_Q k.
Proof. induction k;cbn;congruence. Qed.
Lemma sf_q_out : forall k,s56_out(sf_q k)=sf_R k.
Proof. induction k;cbn;congruence. Qed.
Lemma sf_P_length : forall k,length(sf_P k)=3*k.
Proof. induction k;cbn;lia. Qed.
Lemma sf_Q_length : forall k,length(sf_Q k)=3*k.
Proof. induction k;cbn;lia. Qed.
Lemma sf_in_app : forall a b,s56_in(a++b)=s56_in a++s56_in b.
Proof. induction a as[|x a IH];intro b;[reflexivity|destruct x;cbn;now rewrite IH]. Qed.
Lemma sf_out_app : forall a b,s56_out(a++b)=s56_out a++s56_out b.
Proof. induction a as[|x a IH];intro b;[reflexivity|destruct x;cbn;now rewrite IH]. Qed.
Lemma sf_Q_shift : forall k l,sf_Q k++S3::l=S3::(sf_P k++l).
Proof. induction k;intro l;cbn;[reflexivity|now rewrite IHk]. Qed.
Lemma sf_R_shift : forall k l,S1::(sf_R k++l)=sf_P k++S1::l.
Proof. induction k;intro l;cbn;[reflexivity|now rewrite IHk]. Qed.
Lemma sf_P_end : forall k l,sf_P k++S1::S1::S3::l=sf_P(S k)++l.
Proof. induction k;intro l;cbn;[reflexivity|now rewrite IHk]. Qed.
Lemma sf_carry_P : forall k x l r,x=S2 \/x=S3->
 csteps s56_tm(6*k+3)(co_back StB(sf_P k++S1::x::l)r)=
 Some(co_front StA(sf_Q k++S3::s56_stop x::l)r).
Proof.
 intros k x l r H;pose proof(s56_local_carry(sf_p k)x l r H)as E.
 rewrite sf_p_in,sf_p_out,sf_P_length in E;replace(2*(3*k)+3)with(6*k+3)in E by lia;exact E.
Qed.
Lemma sf_carry_Q : forall k x l r,x=S2 \/x=S3->
 csteps s56_tm(6*k+3)(co_back StB(sf_Q k++S1::x::l)r)=
 Some(co_front StA(sf_R k++S3::s56_stop x::l)r).
Proof.
 intros k x l r H;pose proof(s56_local_carry(sf_q k)x l r H)as E.
 rewrite sf_q_in,sf_q_out,sf_Q_length in E;replace(2*(3*k)+3)with(6*k+3)in E by lia;exact E.
Qed.
Lemma sf_double_carry : forall l l1 l2 t1 t2 r,
 csteps s56_tm t1(co_back StB l(S1::r))=Some(co_front StA l1(S1::r))->
 csteps s56_tm t2(co_back StB l1(S2::r))=Some(co_front StA l2(S2::r))->
 csteps s56_tm(t1+t2+3)(StA,(l,S0,r))=Some(co_front StA(S1::l2)r).
Proof.
 intros l l1 l2 t1 t2 r E1 E2.
 replace(t1+t2+3)with(1+(t1+(1+(t2+1))))by lia;rewrite csteps_add.
 change(csteps s56_tm(t1+(1+(t2+1)))(co_back StB l(S1::r))=Some(co_front StA(S1::l2)r)).
 rewrite csteps_add,E1,csteps_add.
 change(csteps s56_tm(t2+1)(co_back StB l1(S2::r))=Some(co_front StA(S1::l2)r)).
 rewrite csteps_add,E2;reflexivity.
Qed.
Definition sf_X k b l := sf_P k++S3::(sf_P k++S1::(repeat S2 b++l)).
Definition sf_Y k b l := sf_P k++S1::S3::S3::(sf_P k++S1::(repeat S2 b++l)).
Definition sf_Z k b l := sf_P k++S1::S1::S1::S1::S3::(sf_P k++S1::(repeat S2 b++l)).
Definition sf_G m:cconf := (StA,([S3;S1]++repeat S2 m++[S3],S0,[])).
Lemma sf_X_pass : forall k x l r,x=S2 \/x=S3->
 csteps s56_tm(18*k+11)(StA,(sf_P k++S3::(sf_P k++S1::x::l),S0,r))=
 Some(co_front StA(sf_P k++S1::S3::S3::(sf_P k++s56_stop x::l))r).
Proof.
 intros k x l r Hx.
 pose proof(s56_local_carry(sf_p k++false::sf_p k)x l(S1::r)Hx)as E1.
 rewrite sf_in_app,sf_out_app,sf_p_in,sf_p_out in E1;cbn[s56_in s56_out]in E1.
 rewrite sf_p_in,sf_p_out in E1.
 rewrite app_length,sf_P_length in E1;cbn[length]in E1;rewrite sf_P_length in E1.
 replace(2*(3*k+S(3*k))+3)with(12*k+5)in E1 by lia.
 repeat rewrite <-app_assoc in E1;cbn[app]in E1.
 rewrite sf_Q_shift in E1.
 pose proof(sf_carry_Q k S3(sf_P k++s56_stop x::l)(S2::r)(or_intror eq_refl))as E2.
 cbn[s56_stop]in E2.
 pose proof(sf_double_carry _ _ _ _ _ r E1 E2)as E.
 rewrite sf_R_shift in E;replace(12*k+5+(6*k+3)+3)with(18*k+11)in E by lia;exact E.
Qed.
Lemma sf_Y_pass : forall k x l r,x=S2 \/x=S3->
 csteps s56_tm(18*k+15)(StA,(sf_P k++S1::S3::S3::(sf_P k++S1::x::l),S0,r))=
 Some(co_front StA(sf_P k++S1::S1::S1::S1::S3::(sf_P k++s56_stop x::l))r).
Proof.
 intros k x l r Hx.
 pose proof(sf_carry_P k S3(S3::(sf_P k++S1::x::l))(S1::r)(or_intror eq_refl))as E1.
 cbn[s56_stop]in E1.
 pose proof(s56_local_carry(sf_q k++false::false::false::sf_p k)x l(S2::r)Hx)as E2.
 rewrite sf_in_app,sf_out_app,sf_q_in,sf_q_out in E2;cbn[s56_in s56_out]in E2.
 rewrite sf_p_in,sf_p_out in E2;repeat rewrite <-app_assoc in E2;cbn[app]in E2.
 rewrite app_length,sf_Q_length in E2;cbn[length]in E2;rewrite sf_P_length in E2.
 replace(2*(3*k+S(S(S(3*k))))+3)with(12*k+9)in E2 by lia.
 pose proof(sf_double_carry _ _ _ _ _ r E1 E2)as E.
 rewrite sf_R_shift,sf_Q_shift in E.
 replace(6*k+3+(12*k+9)+3)with(18*k+15)in E by lia;exact E.
Qed.
Lemma sf_Z_pass : forall k x l r,x=S2 \/x=S3->
 csteps s56_tm(18*k+21)(StA,(sf_P k++S1::S1::S1::S1::S3::(sf_P k++S1::x::l),S0,r))=
 Some(co_front StA(sf_P(S k)++S3::(sf_P(S k)++s56_stop x::l))r).
Proof.
 intros k x l r Hx.
 pose proof(s56_local_carry(sf_p k++true::true::false::sf_p k)x l(S1::r)Hx)as E1.
 rewrite sf_in_app,sf_out_app,sf_p_in,sf_p_out in E1;cbn[s56_in s56_out]in E1.
 rewrite sf_p_in,sf_p_out in E1;repeat rewrite <-app_assoc in E1;cbn[app]in E1.
 rewrite app_length,sf_P_length in E1;cbn[length]in E1;rewrite sf_P_length in E1.
 replace(2*(3*k+S(S(S(S(S(3*k))))))+3)with(12*k+13)in E1 by lia.
 pose proof(s56_local_carry(sf_q k++[false])S3(S1::S1::(sf_Q k++S3::s56_stop x::l))(S2::r)(or_intror eq_refl))as E2.
 rewrite sf_in_app,sf_out_app,sf_q_in,sf_q_out in E2;cbn[s56_in s56_out s56_stop]in E2.
 rewrite app_length,sf_Q_length in E2;cbn[length]in E2.
 replace(2*(3*k+1)+3)with(6*k+5)in E2 by lia.
 repeat rewrite <-app_assoc in E2;cbn[app]in E2.
 pose proof(sf_double_carry _ _ _ _ _ r E1 E2)as E.
 rewrite sf_R_shift,sf_Q_shift in E.
 rewrite sf_P_end in E.
 replace(12*k+13+(6*k+5)+3)with(18*k+21)in E by lia;exact E.
Qed.
