(** S062: finite sweeps and the protected 23 crossing marker. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census.
Import ListNotations.
Definition s62_tm:TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StB
 |StA,S2=>mkTrans S3 DR StA |StA,S3=>mkTrans S1 DR StA
 |StB,S0=>mkTrans S3 DR StB |StB,S1=>mkTrans S3 DL StA
 |StB,S2=>mkTrans S0 DR StB |StB,S3=>mkTrans S2 DL StB end).
Definition s62_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition s62_back q l r:cconf := (q,(ctl l,chd l,r)).
Definition s62_13 h := h=S1 \/h=S3.
Definition s62_03 h := h=S0 \/h=S3.
Definition s62_23 h := h=S2 \/h=S3.
Definition s62_emit h := match h with S2=>S3|_=>S1 end.
Definition s62_decode w := rev(map s62_emit w).
Definition s62_guard w a := w++[S2;S3]++repeat S2 a++[S1].
Definition s62_main a u v:cconf :=
 (StA,(repeat S3 a++S1::S1::(u++v),S0,[])).
Definition s62_dead l r:cconf := (StA,(l,S0,r)).
Definition s62_guarded r := (exists n,r=repeat S3 n) \/
 exists w a,r=s62_guard w a /\Forall s62_23 w.
Definition s62_safe cc :=
 (exists a u v,Forall s62_13 u /\Forall s62_03 v /\cc=s62_main a u v) \/
 (exists l r,Forall s62_03 l /\s62_guarded r /\cc=s62_dead l r).
Lemma s62_shift : forall(x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma s62_repeat_append : forall(x:Sym)n m l,
 repeat x n++repeat x m++l=repeat x(n+m)++l.
Proof. intros;rewrite repeat_app,app_assoc;reflexivity. Qed.
Lemma s62_decode_app : forall u v,s62_decode(u++v)=s62_decode v++s62_decode u.
Proof. intros;unfold s62_decode;rewrite map_app,rev_app_distr;reflexivity. Qed.
Lemma s62_decode_twos : forall n,s62_decode(repeat S2 n)=repeat S3 n.
Proof. intro n;unfold s62_decode;rewrite map_repeat,rev_repeat;reflexivity. Qed.
Lemma s62_decode_13 : forall w,Forall s62_23 w->Forall s62_13(s62_decode w).
Proof.
 intros w H;unfold s62_decode;apply Forall_rev;apply Forall_map.
 eapply Forall_impl;[|exact H];intros h Hh;destruct Hh as[Hh|Hh];subst h;unfold s62_emit,s62_13;auto.
Qed.
Lemma s62_B_left_threes : forall n l r,
 csteps s62_tm n(s62_back StB(repeat S3 n++l)r)=
 Some(s62_back StB l(repeat S2 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app s62_back csteps cstep s62_tm ctape_move chd ctl].
 change(csteps s62_tm n(s62_back StB(repeat S3 n++l)(S2::r))=
 Some(s62_back StB l(S2::(repeat S2 n++r)))).
 rewrite IHn,s62_shift;reflexivity.
Qed.
Lemma s62_B_right_twos : forall n l r,
 csteps s62_tm n(s62_front StB l(repeat S2 n++r))=
 Some(s62_front StB(repeat S0 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app s62_front csteps cstep s62_tm ctape_move chd ctl].
 change(csteps s62_tm n(s62_front StB(S0::l)(repeat S2 n++r))=
 Some(s62_front StB(S0::(repeat S0 n++l))r)).
 rewrite IHn,s62_shift;reflexivity.
Qed.
Lemma s62_A_right_word : forall w l r,Forall s62_23 w->
 csteps s62_tm(length w)(s62_front StA l(w++r))=
 Some(s62_front StA(s62_decode w++l)r).
Proof.
 induction w as[|h w IH];intros l r H;[reflexivity|].
 inversion H as[|? ? Hh Hw];subst;destruct Hh as[Hh|Hh];subst h;
 cbn[length app s62_front csteps cstep s62_tm ctape_move chd ctl].
 - change(csteps s62_tm(length w)(s62_front StA(S3::l)(w++r))=
   Some(s62_front StA(s62_decode(S2::w)++l)r)).
   rewrite IH by exact Hw;unfold s62_decode;cbn[map rev s62_emit];
   rewrite <-app_assoc;reflexivity.
 - change(csteps s62_tm(length w)(s62_front StA(S1::l)(w++r))=
   Some(s62_front StA(s62_decode(S3::w)++l)r)).
   rewrite IH by exact Hw;unfold s62_decode;cbn[map rev s62_emit];
   rewrite <-app_assoc;reflexivity.
Qed.
Lemma s62_pair : forall l r,
 csteps s62_tm 2(s62_back StB(S1::S1::l)r)=
 Some(s62_back StB l(S2::S3::r)).
Proof. intros;reflexivity. Qed.
Lemma s62_launch : forall l r,
 csteps s62_tm 3(s62_back StB(S1::S3::l)r)=
 Some(s62_front StA(S1::S1::l)r).
Proof. intros;reflexivity. Qed.
Lemma s62_A_launch : forall l r,
 csteps s62_tm 2(s62_back StA(S3::l)(S3::r))=
 Some(s62_front StA(S1::S1::l)r).
Proof. intros;reflexivity. Qed.
Lemma s62_launch_word : forall w l r,Forall s62_23 w->
 csteps s62_tm(3+length w)(s62_back StB(S1::S3::l)(w++r))=
 Some(s62_front StA(s62_decode w++S1::S1::l)r).
Proof. intros;rewrite csteps_add,s62_launch,s62_A_right_word by assumption;reflexivity. Qed.
Lemma s62_main_start : forall a u v,
 csteps s62_tm(a+3)(s62_main a u v)=
 Some(s62_back StB(u++v)(s62_guard [] a)).
Proof.
 intros;replace(a+3)with(1+(a+2))by lia;rewrite csteps_add.
 change(csteps s62_tm(a+2)(s62_back StB(repeat S3 a++S1::S1::(u++v))[S1])=Some(s62_back StB(u++v)(s62_guard [] a))).
 rewrite csteps_add,s62_B_left_threes,s62_pair.
 unfold s62_guard;reflexivity.
Qed.
Lemma s62_forall_repeat : forall(P:Sym->Prop)x n,P x->Forall P(repeat x n).
Proof. intros P x n H;induction n;constructor;assumption. Qed.
Lemma s62_guard_prefix : forall w a,
 Forall s62_23 w->Forall s62_23(w++[S2;S3]++repeat S2 a).
Proof.
 intros w a Hw;apply Forall_app;split;[exact Hw|].
 apply Forall_app;split.
 - constructor;[unfold s62_23;auto|constructor;[unfold s62_23;auto|constructor]].
 - apply s62_forall_repeat;unfold s62_23;auto.
Qed.
Lemma s62_guard_decode : forall w a,
 s62_decode(w++[S2;S3]++repeat S2 a)=
 repeat S3 a++S1::S3::s62_decode w.
Proof.
 intros;rewrite !s62_decode_app,s62_decode_twos;cbn[s62_decode map rev s62_emit].
 rewrite <-app_assoc;reflexivity.
Qed.
Lemma s62_double_launch : forall a w u v,Forall s62_23 w->
 csteps s62_tm(length w+3*a+10)
 (s62_back StB(S1::S3::(u++v))(s62_guard w a))=
 Some(s62_main(a+1)(s62_decode w++S1::S1::u)v).
Proof.
 intros a w u v Hw.
 replace(length w+3*a+10)with
 ((3+length(w++[S2;S3]++repeat S2 a))+(1+(a+(3+length(repeat S2 a++[S2])))))
 by(rewrite !app_length,repeat_length;cbn;lia).
 rewrite csteps_add.
 replace(s62_guard w a)with((w++[S2;S3]++repeat S2 a)++[S1])
 by(unfold s62_guard;rewrite !app_assoc;reflexivity).
 rewrite s62_launch_word by(apply s62_guard_prefix;exact Hw).
 rewrite s62_guard_decode,csteps_add;repeat rewrite <-app_assoc.
 change(csteps s62_tm(a+(3+length(repeat S2 a++[S2])))
 (s62_back StB(repeat S3 a++S1::S3::(s62_decode w++S1::S1::(u++v)))[S2])=Some(s62_main(a+1)(s62_decode w++S1::S1::u)v)).
 rewrite csteps_add,s62_B_left_threes.
 assert(Htwos:Forall s62_23(repeat S2 a++[S2])).
 {apply Forall_app;split;[apply s62_forall_repeat;unfold s62_23;auto|constructor;[unfold s62_23;auto|constructor]]. }
 pose proof(s62_launch_word(repeat S2 a++[S2])(s62_decode w++S1::S1::(u++v))[] Htwos)as E.
 rewrite app_nil_r in E;rewrite E.
 rewrite s62_decode_app,s62_decode_twos.
 cbn[s62_decode map rev s62_emit].
 unfold s62_main,s62_front;cbn[app chd ctl].
 replace(a+1)with(S a)by lia;cbn[repeat].
 repeat rewrite <-app_assoc;reflexivity.
Qed.

Lemma s62_decode_threes : forall n,s62_decode(repeat S3 n)=repeat S1 n.
Proof. intro n;unfold s62_decode;rewrite map_repeat,rev_repeat;reflexivity. Qed.
Lemma s62_A_plain_launch : forall n l,
 csteps s62_tm(2+n)(s62_back StA(S3::l)(S3::repeat S3 n))=
 Some(s62_main 0(repeat S1 n)l).
Proof.
 intros;rewrite csteps_add,s62_A_launch.
 pose proof(s62_A_right_word(repeat S3 n)(S1::S1::l)[]
 (s62_forall_repeat s62_23 S3 n(or_intror eq_refl)))as E.
 rewrite app_nil_r,repeat_length,s62_decode_threes in E;rewrite E.
 unfold s62_main,s62_front;rewrite !s62_shift;reflexivity.
Qed.
Lemma s62_A_guard_launch : forall a w u v,Forall s62_23 w->
 csteps s62_tm(length w+3*a+9)
 (s62_back StA(S3::(u++v))(S3::s62_guard w a))=
 Some(s62_main(a+1)(s62_decode w++S1::S1::u)v).
Proof.
 intros a w u v Hw;pose proof(s62_double_launch a w u v Hw)as E.
 replace(length w+3*a+10)with(1+(length w+3*a+9))in E by lia.
 rewrite csteps_add in E;exact E.
Qed.
