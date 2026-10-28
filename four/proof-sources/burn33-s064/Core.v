(** S064: universal finite-word sweeps and descending-three phase macros. *)
From Coq Require Import List Arith Lia Bool NArith.
From BBB24 Require Import Statement Spec CTape Census.
Import ListNotations.
Definition sk_tm:TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StB
 |StA,S2=>mkTrans S3 DR StA |StA,S3=>mkTrans S2 DL StA
 |StB,S0=>mkTrans S2 DR StB |StB,S1=>mkTrans S1 DR StA
 |StB,S2=>mkTrans S1 DR StB |StB,S3=>mkTrans S3 DL StB end).
Definition sk_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition sk_back q l r:cconf := (q,(ctl l,chd l,r)).
Definition sk_tail(e:bool):list Sym := if e then [S2] else [].
Definition sk_main a b e:cconf := (StA,(repeat S3 a++repeat S1 b++sk_tail e,S0,[])).
Definition sk_P b c d e t:cconf := sk_back StB(repeat S1 b++sk_tail e)(repeat S2 c++repeat S3 d++[t]).
Definition sk_drift l:cconf := (StB,(l,S0,[])).
Definition sk_bit(e:bool):nat := if e then 1 else 0.
Lemma sk_shift : forall (x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma sk_end_repeat : forall (x:Sym)n,repeat x n++[x]=repeat x(S n).
Proof. intros x n;rewrite sk_shift,app_nil_r;reflexivity. Qed.
Lemma sk_repeats : forall (x:Sym)n m l,
 repeat x n++repeat x m++l=repeat x(n+m)++l.
Proof. intros x n m l;rewrite repeat_app,app_assoc;reflexivity. Qed.
Lemma sk_A_left : forall n l r,
 csteps sk_tm n(sk_back StA(repeat S3 n++l)r)=Some(sk_back StA l(repeat S2 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app sk_back csteps cstep sk_tm ctape_move chd ctl].
 change(csteps sk_tm n(sk_back StA(repeat S3 n++l)(S2::r))=
 Some(sk_back StA l(S2::(repeat S2 n++r)))).
 rewrite IHn,sk_shift;reflexivity.
Qed.
Lemma sk_A_right : forall n l r,
 csteps sk_tm n(sk_front StA l(repeat S2 n++r))=Some(sk_front StA(repeat S3 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app sk_front csteps cstep sk_tm ctape_move chd ctl].
 change(csteps sk_tm n(sk_front StA(S3::l)(repeat S2 n++r))=
 Some(sk_front StA(S3::(repeat S3 n++l))r)).
 rewrite IHn,sk_shift;reflexivity.
Qed.
Lemma sk_B_left : forall n l r,
 csteps sk_tm n(sk_back StB(repeat S3 n++l)r)=Some(sk_back StB l(repeat S3 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app sk_back csteps cstep sk_tm ctape_move chd ctl].
 change(csteps sk_tm n(sk_back StB(repeat S3 n++l)(S3::r))=
 Some(sk_back StB l(S3::(repeat S3 n++r)))).
 rewrite IHn,sk_shift;reflexivity.
Qed.
Lemma sk_B_right : forall n l r,
 csteps sk_tm n(sk_front StB l(repeat S2 n++r))=Some(sk_front StB(repeat S1 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app sk_front csteps cstep sk_tm ctape_move chd ctl].
 change(csteps sk_tm n(sk_front StB(S1::l)(repeat S2 n++r))=
 Some(sk_front StB(S1::(repeat S1 n++l))r)).
 rewrite IHn,sk_shift;reflexivity.
Qed.
Lemma sk_pair : forall c l r,
 csteps sk_tm(2*c+3)(sk_back StB(S1::l)(repeat S2 c++S3::r))=
 Some(sk_back StB l(repeat S2(c+2)++r)).
Proof.
 intros c l r;replace(2*c+3)with(1+(c+(1+(c+1))))by lia.
 rewrite csteps_add.
 change(csteps sk_tm(c+(1+(c+1)))(sk_front StA(S1::l)(repeat S2 c++S3::r))=
 Some(sk_back StB l(repeat S2(c+2)++r))).
 rewrite csteps_add,sk_A_right,csteps_add.
 change(csteps sk_tm(c+1)(sk_back StA(repeat S3 c++S1::l)(S2::r))=
 Some(sk_back StB l(repeat S2(c+2)++r))).
 rewrite csteps_add,sk_A_left,sk_shift.
 replace(c+2)with(S(S c))by lia;reflexivity.
Qed.
Definition sk_batch_cost c z := 2*z*z+(2*c+1)*z.
Lemma sk_batch : forall z b c d e t,
 csteps sk_tm(sk_batch_cost c z)(sk_P(b+z)c(d+z)e t)=
 Some(sk_P b(c+2*z)d e t).
Proof.
 induction z;intros b c d e t.
 - unfold sk_batch_cost;rewrite !Nat.mul_0_r,!Nat.add_0_r;reflexivity.
 - replace(sk_batch_cost c(S z))with((2*c+3)+sk_batch_cost(c+2)z)by(unfold sk_batch_cost;nia).
   replace(b+S z)with(S(b+z))by lia;replace(d+S z)with(S(d+z))by lia.
   unfold sk_P at 1;cbn[repeat app];rewrite csteps_add,sk_pair.
   change(csteps sk_tm(sk_batch_cost(c+2)z)(sk_P(b+z)(c+2)(d+z)e t)=
    Some(sk_P b(c+2*S z)d e t)).
   rewrite IHz;replace(c+2+2*z)with(c+2*S z)by lia;reflexivity.
Qed.
Lemma sk_reset_false : forall c d t,
 csteps sk_tm(c+6)(sk_P 0(S c)(S d)false t)=Some(sk_P c 2 d true t).
Proof.
 intros c d t;replace(c+6)with(1+(S c+4))by lia.
 rewrite csteps_add.
 change(csteps sk_tm(S c+4)(sk_front StB[S2](repeat S2(S c)++S3::(repeat S3 d++[t])))=
 Some(sk_P c 2 d true t)).
 rewrite csteps_add,sk_B_right.
 cbn[repeat app].
 unfold sk_P,sk_tail;cbn[repeat app].
 reflexivity.
Qed.
Lemma sk_reset_true : forall c d t,
 csteps sk_tm(c+6)(sk_P 0(S c)(S d)true t)=Some(sk_P(S c)2 d false t).
Proof.
 intros c d t;replace(c+6)with(1+(S c+4))by lia.
 rewrite csteps_add.
 change(csteps sk_tm(S c+4)(sk_front StB[S1](repeat S2(S c)++S3::(repeat S3 d++[t])))=
 Some(sk_P(S c)2 d false t)).
 rewrite csteps_add,sk_B_right.
 cbn[repeat app].
 unfold sk_P,sk_tail;cbn[repeat app].
 rewrite sk_shift,app_nil_r;reflexivity.
Qed.
Lemma sk_start : forall a b e,
 csteps sk_tm(1+a)(sk_main a b e)=Some(sk_P b 0 a e S1).
Proof.
 intros a b e;rewrite csteps_add.
 change(csteps sk_tm a(sk_back StB(repeat S3 a++repeat S1 b++sk_tail e)[S1])=
 Some(sk_P b 0 a e S1)).
 rewrite sk_B_left;reflexivity.
Qed.
Lemma sk_end1_empty : forall c e,
 csteps sk_tm(c+2)(sk_P 0 c 0 e S1)=
 Some(sk_main 0(c+1+sk_bit e)(negb e)).
Proof.
 intros c [];replace(c+2)with(1+(c+1))by lia;rewrite csteps_add.
 - change(csteps sk_tm(c+1)(sk_front StB[S1](repeat S2 c++[S1]))=
   Some(sk_main 0(c+1+1)false)).
   rewrite csteps_add,sk_B_right;unfold sk_main,sk_tail;cbn[repeat app].
   rewrite sk_shift;replace(c+1+1)with(S(S c))by lia;reflexivity.
 - change(csteps sk_tm(c+1)(sk_front StB[S2](repeat S2 c++[S1]))=
   Some(sk_main 0(c+1+0)true)).
   rewrite csteps_add,sk_B_right;unfold sk_main,sk_tail;cbn[repeat app].
   replace(c+1+0)with(S c)by lia;reflexivity.
Qed.
Lemma sk_end1_zero : forall b e,
 csteps sk_tm 4(sk_P(S b)0 0 e S1)=Some(sk_main 1(S b)e).
Proof. intros b e;reflexivity. Qed.
Lemma sk_end1_turn : forall b c e,
 csteps sk_tm(2*c+7)(sk_P(S b)(S c)0 e S1)=Some(sk_P b 2 c e S2).
Proof.
 intros b c e;replace(2*c+7)with(1+(S c+(2+(c+3))))by lia.
 rewrite csteps_add.
 change(csteps sk_tm(S c+(2+(c+3)))
 (sk_front StA(S1::(repeat S1 b++sk_tail e))(repeat S2(S c)++[S1]))=
 Some(sk_P b 2 c e S2)).
 rewrite csteps_add,sk_A_right,csteps_add.
 change(csteps sk_tm(c+3)(sk_back StB(repeat S3 c++S1::(repeat S1 b++sk_tail e))[S3;S2])=
 Some(sk_P b 2 c e S2)).
 rewrite csteps_add,sk_B_left.
 unfold sk_P;cbn[repeat app];rewrite !sk_shift;reflexivity.
Qed.
Lemma sk_end2_nonempty : forall b c e,
 csteps sk_tm(c+2)(sk_P(S b)c 0 e S2)=Some(sk_main(S c)(S b)e).
Proof.
 intros b c e;replace(c+2)with(1+(c+1))by lia;rewrite csteps_add.
 change(csteps sk_tm(c+1)(sk_front StA(S1::(repeat S1 b++sk_tail e))(repeat S2 c++[S2]))=
 Some(sk_main(S c)(S b)e)).
 replace(c+1)with(S c)by lia;rewrite sk_end_repeat.
 rewrite <-(app_nil_r(repeat S2(S c)))at 1;rewrite sk_A_right;reflexivity.
Qed.
Lemma sk_end2_empty : forall c e,
 csteps sk_tm(c+2)(sk_P 0 c 0 e S2)=
 Some(sk_drift(repeat S1(c+1+sk_bit e)++sk_tail(negb e))).
Proof.
 intros c [];replace(c+2)with(1+S c)by lia;rewrite csteps_add.
 - change(csteps sk_tm(S c)(sk_front StB[S1](repeat S2 c++[S2]))=
   Some(sk_drift(repeat S1(c+1+1)++[]))).
   rewrite sk_end_repeat;rewrite <-(app_nil_r(repeat S2(S c)))at 1.
   rewrite sk_B_right,app_nil_r,sk_shift,app_nil_r;unfold sk_drift.
   replace(c+1+1)with(S(S c))by lia;reflexivity.
 - change(csteps sk_tm(S c)(sk_front StB[S2](repeat S2 c++[S2]))=
   Some(sk_drift(repeat S1(c+1+0)++[S2]))).
   rewrite sk_end_repeat;rewrite <-(app_nil_r(repeat S2(S c)))at 1.
   rewrite sk_B_right;unfold sk_drift.
   replace(c+1+0)with(S c)by lia;reflexivity.
Qed.
