(** S074 finite parser and left-wall programs. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement CTape.
Import ListNotations.
Definition s74_tm:TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DR StB
 |StA,S2=>mkTrans S0 DL StA |StA,S3=>mkTrans S1 DR StB
 |StB,S0=>mkTrans S2 DR StB |StB,S1=>mkTrans S3 DR StA
 |StB,S2=>mkTrans S1 DL StA |StB,S3=>mkTrans S0 DL StB end).
Definition s74_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition s74_back q l r:cconf := (q,(ctl l,chd l,r)).
Definition s74_cut w:cconf := (StA,([],S0,w)).
Lemma s74_repeat_shift : forall(x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma s74_repeat_more : forall(x:Sym)n l,repeat x n++x::l=repeat x(n+1)++l.
Proof. intros x n l;rewrite repeat_app;cbn;now rewrite <-app_assoc. Qed.
Lemma s74_A_twos : forall n l r,csteps s74_tm n(s74_back StA(repeat S2 n++l)r)=
 Some(s74_back StA l(repeat S0 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app s74_back csteps cstep s74_tm ctape_move chd ctl].
 change(csteps s74_tm n(s74_back StA(repeat S2 n++l)(S0::r))=
 Some(s74_back StA l(S0::(repeat S0 n++r)))).
 rewrite IHn,s74_repeat_shift;reflexivity.
Qed.
Lemma s74_B_zeros : forall n l r,csteps s74_tm n(s74_front StB l(repeat S0 n++r))=
 Some(s74_front StB(repeat S2 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app s74_front csteps cstep s74_tm ctape_move chd ctl].
 change(csteps s74_tm n(s74_front StB(S2::l)(repeat S0 n++r))=
 Some(s74_front StB(S2::(repeat S2 n++l))r)).
 rewrite IHn,s74_repeat_shift;reflexivity.
Qed.
Theorem s74_drop1 : forall a l r,csteps s74_tm(2*a+3)
 (StA,(S3::repeat S2 a++S1::l,S0,r))=
 Some(StA,(S3::repeat S2 a++l,S0,S1::r)).
Proof.
 intros a l r;destruct a as[|a];[reflexivity|].
 replace(2*S a+3)with(3+(a+(1+(a+1))))by lia;rewrite csteps_add.
 change(csteps s74_tm(a+(1+(a+1)))(s74_back StA(repeat S2 a++S1::l)(S1::S0::S1::r))=
 Some(StA,(S3::repeat S2(S a)++l,S0,S1::r))).
 rewrite csteps_add,s74_A_twos,csteps_add.
 change(csteps s74_tm(a+1)(s74_front StB(S2::l)(repeat S0 a++S1::S0::S1::r))=
 Some(StA,(S3::repeat S2(S a)++l,S0,S1::r))).
 rewrite csteps_add,s74_B_zeros,s74_repeat_more;replace(a+1)with(S a)by lia;reflexivity.
Qed.
Theorem s74_merge : forall a l r,csteps s74_tm(4*a+8)
 (StA,(S3::repeat S2(S a)++S3::S2::l,S0,r))=
 Some(StA,(S3::repeat S2(S a)++l,S0,S1::S1::r)).
Proof.
 intros a l r;replace(4*a+8)with(3+(a+(1+(a+(1+(2*a+3))))))by lia;rewrite csteps_add.
 change(csteps s74_tm(a+(1+(a+(1+(2*a+3)))))
 (s74_back StA(repeat S2 a++S3::S2::l)(S1::S0::S1::r))=
 Some(StA,(S3::repeat S2(S a)++l,S0,S1::S1::r))).
 rewrite csteps_add,s74_A_twos,csteps_add.
 change(csteps s74_tm(a+(1+(2*a+3)))
 (s74_front StB(S1::S2::l)(repeat S0 a++S1::S0::S1::r))=
 Some(StA,(S3::repeat S2(S a)++l,S0,S1::S1::r))).
 rewrite csteps_add,s74_B_zeros,csteps_add.
 change(csteps s74_tm(2*a+3)(StA,(S3::repeat S2 a++S1::S2::l,S0,S1::r))=
 Some(StA,(S3::repeat S2(S a)++l,S0,S1::S1::r))).
 rewrite s74_drop1,s74_repeat_more;replace(a+1)with(S a)by lia;reflexivity.
Qed.
Theorem s74_wall_base : forall a r,csteps s74_tm(a+3)
 (StA,(S3::repeat S2(S a),S0,r))=
 Some(s74_cut(repeat S0 a++S1::S0::S1::r)).
Proof.
 intros a r;replace(a+3)with(3+a)by lia;rewrite csteps_add.
 change(csteps s74_tm a(s74_back StA(repeat S2 a)(S1::S0::S1::r))=
 Some(s74_cut(repeat S0 a++S1::S0::S1::r))).
 rewrite <-(app_nil_r(repeat S2 a))at 1;rewrite s74_A_twos;reflexivity.
Qed.
Fixpoint s74_wall ns := match ns with []=>[]|a::ns=>S3::repeat S2(S a)++s74_wall ns end.
Fixpoint s74_weight ns := match ns with []=>0|a::ns=>a+s74_weight ns end.
Fixpoint s74_cost a ns := match ns with []=>a+3|b::ns=>4*a+8+s74_cost(a+b)ns end.
Definition s74_output a ns r := repeat S0(a+s74_weight ns)++S1::S0::S1::(repeat S1(2*length ns)++r).
Lemma s74_cost_pos : forall ns a,0<s74_cost a ns.
Proof. induction ns as[|b ns IH];intro a;cbn;[lia|pose proof(IH(a+b));lia]. Qed.
Theorem s74_unwind : forall ns a r,csteps s74_tm(s74_cost a ns)
 (StA,(s74_wall(a::ns),S0,r))=Some(s74_cut(s74_output a ns r)).
Proof.
 induction ns as[|b ns IH];intros a r.
 - cbn[s74_wall s74_cost];unfold s74_output;cbn[s74_weight length];rewrite Nat.add_0_r,app_nil_r;apply s74_wall_base.
 - cbn[s74_cost s74_wall];rewrite csteps_add.
   change(match csteps s74_tm(4*a+8)
    (StA,(S3::repeat S2(S a)++S3::S2::(repeat S2 b++s74_wall ns),S0,r))with
    |Some c=>csteps s74_tm(s74_cost(a+b)ns)c|None=>None end=
    Some(s74_cut(s74_output a(b::ns)r))).
   rewrite s74_merge.
   rewrite app_assoc,<-repeat_app.
   replace(S a+b)with(S(a+b))by lia;rewrite IH.
   unfold s74_output;cbn[s74_weight length].
   replace(a+(b+s74_weight ns))with(a+b+s74_weight ns)by lia.
   replace(2*S(length ns))with(2*length ns+2)by lia.
   rewrite(repeat_app S1(2*length ns)2);cbn[repeat];repeat rewrite <-app_assoc;reflexivity.
Qed.
Theorem s74_boot : forall w,csteps s74_tm 3(s74_cut w)=Some(s74_front StA(s74_wall[0])w).
Proof. intro w;reflexivity. Qed.
Theorem s74_forward : forall n a ns r,csteps s74_tm(n+2)
 (s74_front StA(s74_wall(a::ns))(S1::repeat S0 n++S1::r))=
 Some(s74_front StA(s74_wall(n::a::ns))r).
Proof.
 intros n a ns r;replace(n+2)with(1+(n+1))by lia;rewrite csteps_add.
 change(csteps s74_tm(n+1)(s74_front StB(S2::s74_wall(a::ns))(repeat S0 n++S1::r))=
 Some(s74_front StA(s74_wall(n::a::ns))r)).
 rewrite csteps_add,s74_B_zeros,s74_repeat_more;replace(n+1)with(S n)by lia;reflexivity.
Qed.
Print Assumptions s74_merge.
Print Assumptions s74_unwind.
Theorem s74_B_drift : forall n l,csteps s74_tm n(StB,(l,S0,[]))=
 Some(StB,(repeat S2 n++l,S0,[])).
Proof.
 induction n;intro l;[reflexivity|].
 change(csteps s74_tm n(StB,(S2::l,S0,[]))=Some(StB,(S2::(repeat S2 n++l),S0,[]))).
 rewrite IHn,s74_repeat_shift;reflexivity.
Qed.
