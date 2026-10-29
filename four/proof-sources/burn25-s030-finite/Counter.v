(** Universal S030 phase programs. The left3 marker, the full binary right
    word, and its final boundary are explicit. *)
From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement CTape Spec Census TotalCompletion OneStateReach.
Import ListNotations.
Definition s30_tm:TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StA
 |StA,S2=>mkTrans S1 DL StA |StA,S3=>mkTrans S2 DL StB
 |StB,S0=>mkTrans S2 DR StB |StB,S1=>mkTrans S3 DR StA
 |StB,S2=>mkTrans S0 DL StB |StB,S3=>mkTrans S0 DL StA end).
Definition s30_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition s30_back q l r:cconf := (q,(ctl l,chd l,r)).
Definition s30_Q a w := s30_front StA(S3::repeat S2 a)w.
Lemma s30_repeat_shift : forall(x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma s30_repeat_more : forall(x:Sym)n l,repeat x n++x::l=repeat x(n+1)++l.
Proof. intros x n l;rewrite repeat_app;cbn;now rewrite <-app_assoc. Qed.
Lemma s30_A_twos : forall n l r,csteps s30_tm n(s30_back StA(repeat S2 n++l)r)=
 Some(s30_back StA l(repeat S1 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app s30_back csteps cstep s30_tm ctape_move chd ctl].
 change(csteps s30_tm n(s30_back StA(repeat S2 n++l)(S1::r))=
 Some(s30_back StA l(S1::(repeat S1 n++r)))).
 rewrite IHn,s30_repeat_shift;reflexivity.
Qed.
Lemma s30_B_twos : forall n l r,csteps s30_tm n(s30_back StB(repeat S2 n++l)r)=
 Some(s30_back StB l(repeat S0 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app s30_back csteps cstep s30_tm ctape_move chd ctl].
 change(csteps s30_tm n(s30_back StB(repeat S2 n++l)(S0::r))=
 Some(s30_back StB l(S0::(repeat S0 n++r)))).
 rewrite IHn,s30_repeat_shift;reflexivity.
Qed.
Lemma s30_B_zeros : forall n l r,csteps s30_tm n(s30_front StB l(repeat S0 n++r))=
 Some(s30_front StB(repeat S2 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app s30_front csteps cstep s30_tm ctape_move chd ctl].
 change(csteps s30_tm n(s30_front StB(S2::l)(repeat S0 n++r))=
 Some(s30_front StB(S2::(repeat S2 n++l))r)).
 rewrite IHn,s30_repeat_shift;reflexivity.
Qed.
Theorem s30_zero : forall a r,csteps s30_tm(a+5)(s30_Q a(S0::r))=
 Some(s30_Q 1(repeat S1 a++S0::S1::r)).
Proof.
 intros a r;replace(a+5)with(2+(a+3))by lia;rewrite csteps_add.
 change(csteps s30_tm(a+3)(s30_back StA(repeat S2 a)(S0::S1::r))=
 Some(s30_Q 1(repeat S1 a++S0::S1::r))).
 rewrite <-(app_nil_r(repeat S2 a))at 1;rewrite csteps_add,s30_A_twos;reflexivity.
Qed.
Theorem s30_blank : forall a,csteps s30_tm(a+5)(s30_Q a[])=
 Some(s30_Q 1(repeat S1 a++[S0;S1])).
Proof. intro a;exact(s30_zero a[]). Qed.
Lemma s30_B_bounce : forall n l r,csteps s30_tm(2*n+3)
 (StB,(l,S0,repeat S0 n++S2::r))=Some(s30_back StB l(repeat S0(n+2)++r)).
Proof.
 intros n l r;replace(2*n+3)with(1+(n+(1+S n)))by lia;rewrite csteps_add.
 change(csteps s30_tm(n+(1+S n))(s30_front StB(S2::l)(repeat S0 n++S2::r))=
 Some(s30_back StB l(repeat S0(n+2)++r))).
 rewrite csteps_add,s30_B_zeros,s30_repeat_more.
 replace(n+1)with(S n)by lia;rewrite csteps_add.
 change(csteps s30_tm(S n)(s30_back StB(repeat S2(S n)++l)(S0::r))=
 Some(s30_back StB l(repeat S0(n+2)++r))).
 rewrite s30_B_twos,s30_repeat_more;replace(S n+1)with(n+2)by lia;reflexivity.
Qed.
Lemma s30_B_finish : forall n r,csteps s30_tm(n+2)(StB,([],S0,repeat S0 n++S1::r))=
 Some(s30_Q(n+1)r).
Proof.
 intros n r;replace(n+2)with(1+(n+1))by lia;rewrite csteps_add.
 change(csteps s30_tm(n+1)(s30_front StB[S2](repeat S0 n++S1::r))=Some(s30_Q(n+1)r)).
 rewrite csteps_add,s30_B_zeros,s30_repeat_more,app_nil_r.
 change(Some(s30_Q(n+1)r)=Some(s30_Q(n+1)r));reflexivity.
Qed.
Theorem s30_pair : forall a r,csteps s30_tm(6*a+18)(s30_Q a(S1::S1::r))=
 Some(s30_Q(a+5)r).
Proof.
 intros a r;replace(6*a+18)with(2+(a+((2*a+3)+((2*(a+2)+3)+((a+4)+2)))))by lia.
 rewrite csteps_add.
 change(csteps s30_tm(a+((2*a+3)+((2*(a+2)+3)+((a+4)+2))))
 (s30_back StB(repeat S2 a)(S2::S2::S1::r))=Some(s30_Q(a+5)r)).
 rewrite <-(app_nil_r(repeat S2 a))at 1.
 rewrite csteps_add,s30_B_twos,csteps_add;unfold s30_back;cbn[chd ctl].
 rewrite s30_B_bounce,csteps_add;unfold s30_back;cbn[chd ctl].
 rewrite s30_B_bounce;unfold s30_back;cbn[chd ctl].
 replace(a+2+2)with(a+4)by lia;rewrite s30_B_finish.
 replace(a+4+1)with(a+5)by lia;reflexivity.
Qed.
Theorem s30_onezeroone : forall a r,csteps s30_tm(6*a+19)(s30_Q a(S1::S0::S1::r))=
 Some(s30_Q(a+6)r).
Proof.
 intros a r;replace(6*a+19)with(2+(a+((2*a+3)+((2*(a+2)+3)+((a+5)+2)))))by lia.
 rewrite csteps_add.
 change(csteps s30_tm(a+((2*a+3)+((2*(a+2)+3)+((a+5)+2))))
 (s30_back StB(repeat S2 a)(S2::S2::S0::S1::r))=Some(s30_Q(a+6)r)).
 rewrite <-(app_nil_r(repeat S2 a))at 1.
 rewrite csteps_add,s30_B_twos,csteps_add;unfold s30_back;cbn[chd ctl].
 rewrite s30_B_bounce,csteps_add;unfold s30_back;cbn[chd ctl].
 rewrite s30_B_bounce;unfold s30_back;cbn[chd ctl].
 replace(a+2+2)with(a+4)by lia;rewrite s30_repeat_more.
 replace(a+4+1)with(a+5)by lia;rewrite s30_B_finish.
 replace(a+5+1)with(a+6)by lia;reflexivity.
Qed.
Definition s30_bulk_cost a n := n*(6*a+3)+15*n*n.
Theorem s30_bulk : forall n a r,csteps s30_tm(s30_bulk_cost a n)
 (s30_Q a(repeat S1(2*n)++r))=Some(s30_Q(a+5*n)r).
Proof.
 induction n;intros a r.
 - unfold s30_bulk_cost;cbn;now rewrite Nat.add_0_r.
 - replace(s30_bulk_cost a(S n))with((6*a+18)+s30_bulk_cost(a+5)n)by(unfold s30_bulk_cost;nia).
   replace(2*S n)with(S(S(2*n)))by lia;cbn[repeat app].
   rewrite csteps_add,s30_pair,IHn;replace(a+5+5*n)with(a+5*S n)by lia;reflexivity.
Qed.
Theorem s30_entry : csteps s30_tm 3 c0=Some(s30_Q 1[]).
Proof. reflexivity. Qed.
Theorem s30_exposed_before : forall a,csteps s30_tm 1(s30_Q a[S1])=
 Some(StA,(repeat S2 a,S3,[S2])).
Proof. intro a;reflexivity. Qed.
Theorem s30_exposed_after : forall a,csteps s30_tm 2(s30_Q a[S1])=
 Some(s30_back StB(repeat S2 a)[S2;S2]).
Proof. intro a;destruct a;reflexivity. Qed.
Definition s30_bin h := h=S0 \/ h=S2.
Definition s30_binary l h r := Forall s30_bin l /\ s30_bin h /\ Forall s30_bin r.
Lemma s30_bin_pop : forall l,Forall s30_bin l ->s30_bin(chd l)/\Forall s30_bin(ctl l).
Proof. intros[|x l]H;cbn;[split;[left;reflexivity|constructor]|inversion H;auto]. Qed.
Theorem s30_B_binary : forall n l h r,s30_binary l h r ->
 exists l' h' r',csteps s30_tm n(StB,(l,h,r))=Some(StB,(l',h',r')) /\s30_binary l' h' r'.
Proof.
 induction n;intros l h r H.
 - exists l,h,r;auto.
 - destruct H as[Hl[Hh Hr]];destruct Hh as[H0|H2];subst h.
   + destruct(s30_bin_pop r Hr)as[Hh Ht].
     change(exists l' h' r',csteps s30_tm n(StB,(S2::l,chd r,ctl r))=Some(StB,(l',h',r'))/\s30_binary l' h' r').
     apply IHn;unfold s30_binary;repeat split;auto;constructor;[right;reflexivity|exact Hl].
   + destruct(s30_bin_pop l Hl)as[Hh Ht].
     change(exists l' h' r',csteps s30_tm n(StB,(ctl l,chd l,S0::r))=Some(StB,(l',h',r'))/\s30_binary l' h' r').
     apply IHn;unfold s30_binary;repeat split;auto;constructor;[left;reflexivity|exact Hr].
Qed.
Lemma s30_binary_exposed : forall a,s30_binary(ctl(repeat S2 a))(chd(repeat S2 a))[S2;S2].
Proof.
 intro a;assert(H:Forall s30_bin(repeat S2 a)).
 {apply Forall_forall;intros x Hin;apply repeat_spec in Hin;subst;right;reflexivity. }
 destruct(s30_bin_pop _ H)as[Hh Hl];unfold s30_binary;repeat split;auto;repeat constructor;right;reflexivity.
Qed.
Lemma s30_total : Total s30_tm.
Proof. intros q h;unfold s30_tm;eexists;reflexivity. Qed.
Theorem s30_nonhalt : NonHalt s30_tm.
Proof. apply ore_total_nonhalt;exact s30_total. Qed.
Theorem s30_B_forever_from_binary : forall d l h r,s30_binary l h r ->
 csteps s30_tm d c0=Some(StB,(l,h,r)) ->forall k,d<=k ->VisitsAt s30_tm StB k.
Proof.
 intros d l h r Hz E k Hk;destruct(s30_B_binary(k-d)l h r Hz)as(l'&h'&r'&Ek&_).
 exists(lift(StB,(l',h',r')));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;replace k with(d+(k-d))at 1 by lia;rewrite csteps_add,E;exact Ek.
Qed.
Print Assumptions s30_bulk.
