(** Exact frozen S022. Two unary blocks implement a Fibonacci return map;
    parity makes every finite drain finish in the nonescaping boundary case. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census OneStateReach.
Import ListNotations.
Definition fc_tm:TM:=fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S1 DR StA
 |StA,S2=>mkTrans S1 DL StB |StA,S3=>mkTrans S2 DR StB
 |StB,S0=>mkTrans S3 DR StB |StB,S1=>mkTrans S3 DL StA
 |StB,S2=>mkTrans S3 DL StB |StB,S3=>mkTrans S2 DR StA end).
Definition fc_front q l r:cconf:=(q,(l,chd r,ctl r)).
Definition fc_back q l r:cconf:=(q,(ctl l,chd l,r)).
Definition fc_main m n:cconf:=(StA,(repeat S2(2*m)++S1::(repeat S2(S(2*n))++[S3]),S0,[])).
Definition fc_Q m n k:cconf:=fc_front StA(repeat S2(2*m)++S1::repeat S2(S(2*n)))
 (S2::repeat S3(S(2*k))).
Definition fc_cost m n:=8*m*n+12*n*n+20*m+44*n+37.
Definition fc_drain_cost m n:=8*m*n+12*n*n+22*n.
Lemma fc_repeat_shift : forall (x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma fc_left_twos : forall n l r,
 csteps fc_tm n(fc_back StB(repeat S2 n++l)r)=Some(fc_back StB l(repeat S3 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app fc_back csteps cstep fc_tm ctape_move chd ctl].
 change(csteps fc_tm n(fc_back StB(repeat S2 n++l)(S3::r))=
 Some(fc_back StB l(S3::(repeat S3 n++r)))).
 rewrite IHn,fc_repeat_shift;reflexivity.
Qed.
Lemma fc_right_pairs : forall n l r,
 csteps fc_tm(2*n)(fc_front StA l(repeat S3(2*n)++r))=
 Some(fc_front StA(repeat S2(2*n)++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(2*S n)with(2+2*n)by lia;rewrite csteps_add.
 change(csteps fc_tm(2*n)(fc_front StA(S2::S2::l)(repeat S3(2*n)++r))=
 Some(fc_front StA(S2::S2::(repeat S2(2*n)++l))r)).
 rewrite IHn,!fc_repeat_shift;reflexivity.
Qed.
Lemma fc_A_one_even : forall n l r,
 csteps fc_tm(2*n+1)(fc_front StA l(S1::repeat S3(2*n)++r))=
 Some(fc_front StA(repeat S2(2*n)++S1::l)r).
Proof.
 intros n l r;replace(2*n+1)with(1+2*n)by lia;rewrite csteps_add.
 change(csteps fc_tm(2*n)(fc_front StA(S1::l)(repeat S3(2*n)++r))=
 Some(fc_front StA(repeat S2(2*n)++S1::l)r));apply fc_right_pairs.
Qed.
Lemma fc_A_one_odd : forall n l r,
 csteps fc_tm(2*n+3)(fc_front StA l(S1::repeat S3(S(2*n))++S1::r))=
 Some(fc_front StA(repeat S2(2*n)++S1::l)(S2::S3::r)).
Proof.
 intros n l r;replace(2*n+3)with(1+(2*n+2))by lia;rewrite csteps_add.
 change(csteps fc_tm(2*n+2)(fc_front StA(S1::l)(repeat S3(S(2*n))++S1::r))=
 Some(fc_front StA(repeat S2(2*n)++S1::l)(S2::S3::r))).
 cbn[repeat app];rewrite <-fc_repeat_shift,csteps_add,fc_right_pairs;reflexivity.
Qed.
Lemma fc_to_left : forall n l r h,h=S0 \/h=S2 ->
 csteps fc_tm(n+2)(StA,(repeat S2 n++S1::l,h,r))=
 Some(fc_back StA l(repeat S3(S n)++S1::r)).
Proof.
 intros n l r h Hh;replace(n+2)with(1+(n+1))by lia;rewrite csteps_add.
 destruct Hh as[->|Hh];[|subst h];
 change(csteps fc_tm(n+1)(fc_back StB(repeat S2 n++S1::l)(S1::r))=
 Some(fc_back StA l(repeat S3(S n)++S1::r)));
 rewrite csteps_add,fc_left_twos;reflexivity.
Qed.
Lemma fc_wall_even : forall n l r,
 csteps fc_tm(4*n+2)(fc_front StA(repeat S2(2*n)++S3::l)(S2::r))=
 Some(fc_front StA(repeat S2(S(2*n))++l)(S1::r)).
Proof.
 intros n l r;replace(4*n+2)with(1+(2*n+(1+2*n)))by lia;rewrite csteps_add.
 change(csteps fc_tm(2*n+(1+2*n))(fc_back StB(repeat S2(2*n)++S3::l)(S1::r))=
 Some(fc_front StA(repeat S2(S(2*n))++l)(S1::r))).
 rewrite csteps_add,fc_left_twos,csteps_add.
 change(csteps fc_tm(2*n)(fc_front StA(S2::l)(repeat S3(2*n)++S1::r))=
 Some(fc_front StA(repeat S2(S(2*n))++l)(S1::r))).
 rewrite fc_right_pairs,fc_repeat_shift;reflexivity.
Qed.
Lemma fc_wall_odd : forall n l r,
 csteps fc_tm(4*n+5)(fc_front StA(repeat S2(S(2*n))++S3::l)(S2::r))=
 Some(fc_front StA(repeat S2(S(2*n))++l)(S2::S3::r)).
Proof.
 intros n l r;replace(4*n+5)with(1+(S(2*n)+(1+(2*n+2))))by lia;rewrite csteps_add.
 change(csteps fc_tm(S(2*n)+(1+(2*n+2)))(fc_back StB(repeat S2(S(2*n))++S3::l)(S1::r))=
 Some(fc_front StA(repeat S2(S(2*n))++l)(S2::S3::r))).
 rewrite csteps_add,fc_left_twos,csteps_add.
 change(csteps fc_tm(2*n+2)(fc_front StA(S2::l)(repeat S3(S(2*n))++S1::r))=
 Some(fc_front StA(repeat S2(S(2*n))++l)(S2::S3::r))).
 cbn[repeat app];rewrite <-fc_repeat_shift,csteps_add,fc_right_pairs,fc_repeat_shift;reflexivity.
Qed.
Lemma fc_open_zero : forall r,
 csteps fc_tm 3(fc_front StA[](S2::r))=Some(fc_front StA[](S3::S3::r)).
Proof. reflexivity. Qed.
Lemma fc_open_odd : forall n r,
 csteps fc_tm(4*n+4)(fc_front StA(repeat S2(S(2*n)))(S2::r))=
 Some(fc_front StA(repeat S2(S(2*n))++[S3])(S1::r)).
Proof.
 intros n r;replace(4*n+4)with(1+(S(2*n)+(2+2*n)))by lia;rewrite csteps_add.
 change(csteps fc_tm(S(2*n)+(2+2*n))(fc_back StB(repeat S2(S(2*n)))(S1::r))=
 Some(fc_front StA(repeat S2(S(2*n))++[S3])(S1::r))).
 rewrite <-(app_nil_r(repeat S2(S(2*n))))at 1.
 rewrite csteps_add,fc_left_twos,csteps_add.
 change(csteps fc_tm(2*n)(fc_front StA[S2;S3](repeat S3(2*n)++S1::r))=
 Some(fc_front StA(repeat S2(S(2*n))++[S3])(S1::r))).
 rewrite fc_right_pairs,fc_repeat_shift;reflexivity.
Qed.
Lemma fc_open_even_step : forall n r,
 csteps fc_tm(4*n+7)(fc_front StA(repeat S2(S(S(2*n))))(S2::r))=
 Some(fc_front StA(repeat S2(S(2*n))++[S3])(S2::S3::r)).
Proof.
 intros n r;replace(4*n+7)with(1+(S(S(2*n))+(2+(2*n+2))))by lia;rewrite csteps_add.
 change(csteps fc_tm(S(S(2*n))+(2+(2*n+2)))(fc_back StB(repeat S2(S(S(2*n))))(S1::r))=
 Some(fc_front StA(repeat S2(S(2*n))++[S3])(S2::S3::r))).
 rewrite <-(app_nil_r(repeat S2(S(S(2*n)))))at 1.
 rewrite csteps_add,fc_left_twos,csteps_add.
 change(csteps fc_tm(2*n+2)(fc_front StA[S2;S3](repeat S3(S(2*n))++S1::r))=
 Some(fc_front StA(repeat S2(S(2*n))++[S3])(S2::S3::r))).
 cbn[repeat app];rewrite <-fc_repeat_shift,csteps_add,fc_right_pairs,fc_repeat_shift;reflexivity.
Qed.
Lemma fc_open_even : forall n r,
 csteps fc_tm(12*n+16)(fc_front StA(repeat S2(S(S(2*n))))(S2::r))=
 Some(fc_front StA(repeat S2(S(2*n))++[S3])(S1::S3::S3::r)).
Proof.
 intros n r;replace(12*n+16)with((4*n+7)+((4*n+5)+(4*n+4)))by lia.
 rewrite csteps_add,fc_open_even_step,csteps_add,fc_wall_odd,app_nil_r,fc_open_odd;reflexivity.
Qed.
Lemma fc_wall_round : forall m n r h,h=S0 \/h=S2 ->
 csteps fc_tm(4*m+4*n+7)
 (StA,(repeat S2(2*m)++S1::(repeat S2(S(2*n))++[S3]),h,r))=
 Some(fc_front StA(repeat S2(2*m)++S1::repeat S2(S(2*n)))(S2::S3::r)).
Proof.
 intros m n r h Hh;replace(4*m+4*n+7)with((2*m+2)+((4*n+2)+(2*m+3)))by lia.
 rewrite csteps_add,fc_to_left by exact Hh.
 change(csteps fc_tm((4*n+2)+(2*m+3))
 (fc_front StA(repeat S2(2*n)++[S3])(S2::repeat S3(S(2*m))++S1::r))=
 Some(fc_front StA(repeat S2(2*m)++S1::repeat S2(S(2*n)))(S2::S3::r))).
 rewrite csteps_add,fc_wall_even,app_nil_r,fc_A_one_odd;reflexivity.
Qed.
Lemma fc_open_round : forall m n r,
 csteps fc_tm(4*m+12*n+23)
 (fc_front StA(repeat S2(2*m)++S1::repeat S2(S(S(S(2*n)))))(S2::r))=
 Some(fc_front StA(repeat S2(2*S m)++S1::(repeat S2(S(2*n))++[S3]))(S2::S3::r)).
Proof.
 intros m n r;replace(4*m+12*n+23)with((2*m+2)+((12*n+16)+(2*S m+3)))by lia.
 rewrite csteps_add.
 change(match csteps fc_tm(2*m+2)(StA,(repeat S2(2*m)++S1::repeat S2(S(S(S(2*n)))),S2,r))with
 |Some cc=>csteps fc_tm((12*n+16)+(2*S m+3))cc|None=>None end=
 Some(fc_front StA(repeat S2(2*S m)++S1::(repeat S2(S(2*n))++[S3]))(S2::S3::r))).
 rewrite fc_to_left by(right;reflexivity).
 change(csteps fc_tm((12*n+16)+(2*S m+3))
 (fc_front StA(repeat S2(S(S(2*n))))(S2::repeat S3(S(2*m))++S1::r))=
 Some(fc_front StA(repeat S2(2*S m)++S1::(repeat S2(S(2*n))++[S3]))(S2::S3::r))).
 rewrite csteps_add,fc_open_even.
 change(csteps fc_tm(2*S m+3)
 (fc_front StA(repeat S2(S(2*n))++[S3])(S1::repeat S3(S(S(S(2*m))))++S1::r))=
 Some(fc_front StA(repeat S2(2*S m)++S1::(repeat S2(S(2*n))++[S3]))(S2::S3::r))).
 replace(S(S(S(2*m))))with(S(2*S m))by lia;apply fc_A_one_odd.
Qed.
Lemma fc_Q_pair : forall m n k,
 csteps fc_tm(8*m+16*n+34)(fc_Q m(S n)k)=Some(fc_Q(S m)n(S k)).
Proof.
 intros m n k;replace(8*m+16*n+34)with((4*m+12*n+23)+(4*S m+4*n+7))by lia.
 unfold fc_Q;replace(S(2*S n))with(S(S(S(2*n))))by lia.
 rewrite csteps_add,fc_open_round.
 change(csteps fc_tm(4*S m+4*n+7)
 (StA,(repeat S2(2*S m)++S1::(repeat S2(S(2*n))++[S3]),S2,S3::repeat S3(S(2*k))))=
 Some(fc_front StA(repeat S2(2*S m)++S1::repeat S2(S(2*n)))(S2::repeat S3(S(2*S k))))).
 rewrite fc_wall_round by(right;reflexivity).
 replace(S(2*S k))with(S(S(S(2*k))))by lia;reflexivity.
Qed.
Theorem fc_drain : forall n m k,
 csteps fc_tm(fc_drain_cost m n)(fc_Q m n k)=Some(fc_Q(m+n)0(k+n)).
Proof.
 induction n;intros m k.
 - replace(fc_drain_cost m 0)with 0 by(unfold fc_drain_cost;lia).
   rewrite !Nat.add_0_r;reflexivity.
 - replace(fc_drain_cost m(S n))with((8*m+16*n+34)+fc_drain_cost(S m)n)by(unfold fc_drain_cost;nia).
   rewrite csteps_add,fc_Q_pair,IHn.
   replace(S m+n)with(m+S n)by lia;replace(S k+n)with(k+S n)by lia;reflexivity.
Qed.
Lemma fc_open_zero_odd : forall m r,
 csteps fc_tm(2*m+7)(fc_front StA[](S2::repeat S3(S(2*m))++S1::r))=
 Some(fc_front StA(repeat S2(2*S m))(S2::S3::r)).
Proof.
 intros m r;replace(2*m+7)with(3+(2*S m+2))by lia.
 rewrite csteps_add,fc_open_zero.
 assert(Er:S3::S3::(repeat S3(S(2*m))++S1::r)=repeat S3(2*S m)++S3::S1::r).
 {replace(2*S m)with(S(S(2*m)))by lia;cbn[repeat app];rewrite fc_repeat_shift;reflexivity. }
 rewrite Er.
 change(csteps fc_tm(2*S m+2)(fc_front StA[](repeat S3(2*S m)++S3::S1::r))=
 Some(fc_front StA(repeat S2(2*S m))(S2::S3::r))).
 rewrite csteps_add,fc_right_pairs,app_nil_r;reflexivity.
Qed.
Theorem fc_Q_finish : forall m k,
 csteps fc_tm(16*m+2*k+30)(fc_Q m 0 k)=Some(fc_main(k+2)m).
Proof.
 intros m k;replace(16*m+2*k+30)with((2*m+2)+((2*m+7)+((12*m+16)+(2*S(S k)+1))))by lia.
 unfold fc_Q;rewrite csteps_add.
 change(match csteps fc_tm(2*m+2)(StA,(repeat S2(2*m)++S1::[S2],S2,repeat S3(S(2*k))))with
 |Some cc=>csteps fc_tm((2*m+7)+((12*m+16)+(2*S(S k)+1)))cc|None=>None end=Some(fc_main(k+2)m)).
 rewrite fc_to_left by(right;reflexivity).
 change(csteps fc_tm((2*m+7)+((12*m+16)+(2*S(S k)+1)))
 (fc_front StA[](S2::repeat S3(S(2*m))++S1::repeat S3(S(2*k))))=Some(fc_main(k+2)m)).
 rewrite csteps_add,fc_open_zero_odd,csteps_add.
 replace(2*S m)with(S(S(2*m)))by lia;rewrite fc_open_even.
 assert(Ek:S3::S3::S3::repeat S3(S(2*k))=repeat S3(2*S(S k))).
 {replace(2*S(S k))with(S(S(S(S(2*k)))))by lia;reflexivity. }
 rewrite Ek.
 pose proof(fc_A_one_even(S(S k))(repeat S2(S(2*m))++[S3])[])as Ee.
 rewrite app_nil_r in Ee;rewrite Ee;unfold fc_main.
 replace(2*S(S k))with(2*(k+2))by lia;reflexivity.
Qed.
Theorem fc_main_next : forall m n,
 csteps fc_tm(fc_cost m n)(fc_main m n)=Some(fc_main(n+2)(m+n)).
Proof.
 intros m n;replace(fc_cost m n)with((4*m+4*n+7)+(fc_drain_cost m n+(16*(m+n)+2*n+30)))by(unfold fc_cost,fc_drain_cost;nia).
 unfold fc_main at 1;rewrite csteps_add,fc_wall_round by(left;reflexivity).
 change(csteps fc_tm(fc_drain_cost m n+(16*(m+n)+2*n+30))(fc_Q m n 0)=Some(fc_main(n+2)(m+n))).
 rewrite csteps_add,fc_drain.
 change(csteps fc_tm(16*(m+n)+2*n+30)(fc_Q(m+n)0 n)=Some(fc_main(n+2)(m+n))).
 apply fc_Q_finish.
Qed.
Example fc_entry : csteps fc_tm 24 c0=Some(fc_main 1 0).
Proof. reflexivity. Qed.
Lemma fc_returns : forall N,exists t m n,N<=t /\csteps fc_tm t c0=Some(fc_main m n).
Proof.
 induction N as[|N IH].
 - exists 24,1,0;split;[lia|exact fc_entry].
 - destruct IH as(t&m&n&Ht&E);exists(t+fc_cost m n),(n+2),(m+n);split.
   + unfold fc_cost;nia.
   + rewrite csteps_add,E;apply fc_main_next.
Qed.
Theorem fc_nonhalt : NonHalt fc_tm.
Proof. apply ore_total_nonhalt;intros q h;destruct q,h;eexists;reflexivity. Qed.
Theorem fc_A_recurrent : forall N,exists t,N<=t /\VisitsAt fc_tm StA t.
Proof.
 intro N;destruct(fc_returns N)as(t&m&n&Ht&E).
 exists t;split;[exact Ht|];exists(lift(fc_main m n));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem fc_B_recurrent : forall N,exists t,N<=t /\VisitsAt fc_tm StB t.
Proof.
 intro N;destruct(fc_returns N)as(t&m&n&Ht&E).
 exists(t+1);split;[lia|].
 exists(lift(fc_back StB(repeat S2(2*m)++S1::(repeat S2(S(2*n))++[S3]))[S1]));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem fc_state_zero : QHBound 0 fc_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(fc_A_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(fc_B_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem fc_sound : NonHalt fc_tm /\QHBound 0 fc_tm.
Proof. split;[exact fc_nonhalt|exact fc_state_zero]. Qed.
Print Assumptions fc_sound.
