(** Base returns and the decreasing outer parameter for S053. *)
From Coq Require Import List Arith Lia Bool NArith.
From BBB24 Require Import Statement Spec CTape Census.
From BBB24Burn22S053Counter Require Import S053Core Odd.
Import ListNotations.

Lemma so_finish_one : forall l r,
 csteps sc_tm 7(sc_front StB(S3::S3::l)(S1::r))=
 Some(sc_front StA(S1::S1::S1::l)r).
Proof. intros l r;reflexivity. Qed.
Lemma so_finish_three : forall l r,
 csteps sc_tm 10(sc_back StB(S3::S3::S3::l)(S1::r))=
 Some(sc_front StA(S1::S1::S1::S1::l)r).
Proof. intros l r;reflexivity. Qed.
Lemma so_emit_twos : forall l r,
 csteps sc_tm 3(sc_back StB(S3::l)(S2::S2::r))=
 Some(sc_front StA(S1::S1::S1::l)r).
Proof. intros l r;reflexivity. Qed.
Lemma so_enter_ones : forall l r,
 csteps sc_tm 4(sc_front StA(S1::S1::S1::l)(S1::r))=
 Some(sc_back StB l(S3::S3::S3::S2::r)).
Proof. intros l r;reflexivity. Qed.
Lemma so_emit_two : forall l r,
 csteps sc_tm 2(sc_back StB(S3::l)(S2::r))=
 Some(sc_front StA(S1::S1::l)r).
Proof. intros l r;reflexivity. Qed.
Lemma so_blank_one : forall m r,
 csteps sc_tm(m+14)(sc_back StB[](S3::S3::(repeat S2 m++S1::r)))=
 Some(sc_front StA(S1::S1::S1::repeat S3(m+1))r).
Proof.
 intros m r;replace(m+14)with(4+(S(S(S m))+7))by lia;rewrite csteps_add.
 change(csteps sc_tm(S(S(S m))+7)
 (sc_front StB[](repeat S2(S(S(S m)))++S1::r))=
 Some(sc_front StA(S1::S1::S1::repeat S3(m+1))r)).
 rewrite csteps_add,sc_B_right_twos,app_nil_r;cbn[repeat].
 rewrite so_finish_one.
 replace(m+1)with(S m)by lia;reflexivity.
Qed.
Theorem so_even_two : forall n,
 csteps sc_tm(12*n+14)(sc_C 2(2*n))=Some(sc_main 3(2*n+1)).
Proof.
 intro n;replace(12*n+14)with(10*n+(2*n+14))by lia.
 unfold sc_C;rewrite <-(app_nil_r(repeat S3(2*n)))at 1.
 change(csteps sc_tm(10*n+(2*n+14))
 (sc_back StB(repeat S3(2*n)++[])(S3::S3::S1::[]))=
 Some(sc_main 3(2*n+1))).
 rewrite csteps_add,sc_pairs,so_blank_one;unfold sc_main;reflexivity.
Qed.
Theorem so_even_three : forall n,
 csteps sc_tm(12*n+17)(sc_C 3(2*n))=Some(sc_main 4(2*n+1)).
Proof.
 intro n;replace(12*n+17)with((12*n+7)+10)by lia.
 unfold sc_C;cbn[repeat app];rewrite csteps_add,sc_even.
 replace(2*n+4)with(S(S(S(2*n+1))))by lia.
 cbn[repeat].
 rewrite so_finish_three;reflexivity.
Qed.
Theorem so_even_four : forall n,
 csteps sc_tm(24*n+38)(sc_C 4(2*n))=Some(sc_main 2(2*n+5)).
Proof.
 intro n;replace(24*n+38)with((12*n+7)+(3+(3+(4+(10*S n+((2*n+2+7)+2))))))by lia.
 unfold sc_C;cbn[repeat app];rewrite csteps_add,sc_even,csteps_add.
 replace(2*n+4)with(S(2*n+3))by lia.
 change(csteps sc_tm(3+(3+(4+(10*S n+((2*n+2+7)+2)))))
  (sc_C 1(S(2*n+3)))=Some(sc_main 2(2*n+5))).
 rewrite csteps_add,sc_C_three,csteps_add;unfold sc_D;cbn[repeat app].
 replace(2*n+3)with(S(2*n+2))by lia;cbn[repeat].
 rewrite so_emit_twos,csteps_add,so_enter_ones,csteps_add.
 replace(2*n+2)with(2*S n)by lia.
 rewrite <-(app_nil_r(repeat S3(2*S n)))at 1;rewrite sc_pairs.
 replace(2*S n)with(2*n+2)by lia;rewrite csteps_add,sc_blank_C.
 replace(2*n+2+4)with(S(2*n+5))by lia;cbn[repeat].
 rewrite so_emit_two;reflexivity.
Qed.

Example so_odd_one_two : csteps sc_tm 16(sc_C 2 1)=Some(sc_main_two 4).
Proof. reflexivity. Qed.
Example so_odd_one_three : csteps sc_tm 29(sc_C 3 1)=Some(sc_main 4 2).
Proof. reflexivity. Qed.
Example so_odd_one_four : csteps sc_tm 74(sc_C 4 1)=Some(sc_main 8 0).
Proof. reflexivity. Qed.
Example so_two_four : csteps sc_tm 35(sc_main_two 4)=Some(sc_main 4 3).
Proof. reflexivity. Qed.
Example so_two_five : csteps sc_tm 69(sc_main_two 5)=Some(sc_main 2 7).
Proof. reflexivity. Qed.
Example so_two_six : csteps sc_tm 77(sc_main_two 6)=Some(sc_main 3 7).
Proof. reflexivity. Qed.

Lemma so_bottom_two : forall r,
 csteps sc_tm 7(sc_back StB[S2](S3::S3::r))=
 Some(sc_front StA[S1;S1;S1]r).
Proof. intro r;reflexivity. Qed.
Lemma so_four_twos : forall l r,
 csteps sc_tm 4(sc_back StB(S3::l)(S2::S2::S2::r))=
 Some(sc_front StA(S1::S1::S1::S1::l)r).
Proof. intros l r;reflexivity. Qed.
Lemma so_clear_three : forall l r,
 csteps sc_tm 3(sc_back StB(S3::l)(S3::r))=
 Some(sc_back StB l(S2::S2::r)).
Proof. intros l r;reflexivity. Qed.
Lemma so_odd_boundary_any : forall m r,
 csteps sc_tm(m+7)(sc_back StB[S3](S3::S3::(repeat S2 m++r)))=
 Some(sc_front StA(repeat S1(S m)++[S3;S3;S2])r).
Proof.
 intros m r;replace(m+7)with(7+m)by lia;rewrite csteps_add.
 change(csteps sc_tm m(sc_front StA[S1;S3;S3;S2](repeat S2 m++r))=
 Some(sc_front StA(repeat S1(S m)++[S3;S3;S2])r)).
 rewrite sc_A_right_twos,sc_repeat_shift;reflexivity.
Qed.
Lemma so_odd_prepare_any : forall n r,
 csteps sc_tm(12*n+7)(sc_back StB(repeat S3(2*n+1))(S3::S3::r))=
 Some(sc_front StA(repeat S1(2*n+1)++[S3;S3;S2])r).
Proof.
 intros n r;replace(12*n+7)with(10*n+(2*n+7))by lia.
 rewrite(repeat_app S3(2*n)1).
 change(csteps sc_tm(10*n+(2*n+7))
 (sc_back StB(repeat S3(2*n)++[S3])(S3::S3::r))=
 Some(sc_front StA(repeat S1(2*n+1)++[S3;S3;S2])r)).
 rewrite csteps_add,sc_pairs,so_odd_boundary_any.
 replace(S(2*n))with(2*n+1)by lia;reflexivity.
Qed.
Lemma so_prepare_any : forall n r,
 csteps sc_tm(2*S n+21)
 (sc_front StA(repeat S1(2*S n+1)++[S3;S3;S2])(S3::r))=
 Some(sc_front StA(repeat S1 5)(repeat S3(2*n)++S2::S2::r)).
Proof.
 intros n r;replace(2*S n+21)with((2*S n+3)+(5+13))by lia.
 replace(2*S n+1)with(S(2*S n))by lia.
 rewrite csteps_add,so_launch.
 replace(2*S n)with(S(S(2*n)))by lia;cbn[repeat app].
 rewrite csteps_add,so_small_one,so_small_two;reflexivity.
Qed.
Lemma so_prepare_one : forall n r,
 csteps sc_tm(2*S n+21)
 (sc_front StA(repeat S1(2*S n+1)++[S3;S3;S2])(S1::r))=
 Some(sc_front StA(repeat S1 5)(repeat S3(2*n+1)++S2::r)).
Proof.
 intros n r;replace(2*S n+21)with(1+((2*S n+1)+(10+(7+2))))by lia.
 rewrite csteps_add.
 change(csteps sc_tm((2*S n+1)+(10+(7+2)))
 (sc_back StB(repeat S1(2*S n+1)++[S3;S3;S2])(S2::r))=
 Some(sc_front StA(repeat S1 5)(repeat S3(2*n+1)++S2::r))).
 rewrite csteps_add,sc_B_left_ones,csteps_add.
 replace(2*S n+1)with(S(S(2*n+1)))by lia;cbn[repeat app].
 rewrite sc_pair,csteps_add,so_bottom_two.
 change(csteps sc_tm 2(sc_front StA[S1;S1;S1](repeat S2 2++(repeat S3(2*n+1)++S2::r)))=
 Some(sc_front StA(repeat S1 5)(repeat S3(2*n+1)++S2::r))).
 rewrite sc_A_right_twos;reflexivity.
Qed.
Lemma so_seven_one_finish : forall j,
 csteps sc_tm(24*j+53)(sc_front StA(repeat S1 7++repeat S3(2*j))[S1])=
 Some(sc_main 4(2*j+6)).
Proof.
 intro j;replace(24*j+53)with(8+(10*j+((2*j+7)+((12*(j+2)+7)+(3+4)))))by lia.
 rewrite csteps_add.
 change(csteps sc_tm(10*j+((2*j+7)+((12*(j+2)+7)+(3+4))))
 (sc_back StB(repeat S3(2*j))(S3::S3::S3::S3::S3::S3::S3::S2::[]))=
 Some(sc_main 4(2*j+6))).
 rewrite <-(app_nil_r(repeat S3(2*j)))at 1.
 rewrite csteps_add,sc_pairs,csteps_add,sc_blank_C,csteps_add.
 replace(2*j+4)with(2*(j+2))by lia;rewrite sc_even.
 replace(2*(j+2)+4)with(S(S(2*j+6)))by lia.
 cbn[repeat];rewrite csteps_add,so_clear_three.
 rewrite so_four_twos;reflexivity.
Qed.

Theorem so_odd_two : forall n,
 csteps sc_tm(24*n*n+68*n+64)(sc_C 2(2*n+3))=Some(sc_main 6(4*n+2)).
Proof.
 intro n;replace(24*n*n+68*n+64)with
 ((12*S n+7)+((2*S n+21)+(so_drain_cost(2*n+1)0+1)))by(unfold so_drain_cost;nia).
 unfold sc_C;replace(2*n+3)with(2*S n+1)by lia;cbn[repeat app].
 rewrite csteps_add,so_odd_prepare_any,csteps_add,so_prepare_one,csteps_add.
 change(match csteps sc_tm(so_drain_cost(2*n+1)0)
 (sc_front StA(repeat S1 5++repeat S3(2*0))(repeat S3(2*n+1)++[S2]))with
 |Some c=>csteps sc_tm 1 c|None=>None end=Some(sc_main 6(4*n+2))).
 rewrite so_five_iter;unfold sc_main;replace(2*(0+(2*n+1)))with(4*n+2)by lia;reflexivity.
Qed.
Theorem so_odd_three : forall n,
 csteps sc_tm(24*n*n+44*n+29)(sc_C 3(2*n+1))=Some(sc_main 4(4*n+2)).
Proof.
 intro n;destruct n as[|n];[exact so_odd_one_three|].
 replace(24*S n*S n+44*S n+29)with
 ((12*S n+7)+((2*S n+21)+(so_drain_cost(2*n)0+(2+(24*(2*n)+53)))))
 by(unfold so_drain_cost;nia).
 unfold sc_C;cbn[repeat app];rewrite csteps_add,so_odd_prepare_any,csteps_add,so_prepare_any,csteps_add.
 change(match csteps sc_tm(so_drain_cost(2*n)0)
 (sc_front StA(repeat S1 5++repeat S3(2*0))(repeat S3(2*n)++[S2;S2;S1]))with
 |Some c=>csteps sc_tm(2+(24*(2*n)+53))c|None=>None end=Some(sc_main 4(4*S n+2))).
 rewrite so_five_iter,csteps_add.
 change(csteps sc_tm(24*(2*n)+53)
 (sc_front StA(repeat S1 7++repeat S3(2*(2*n)))[S1])=Some(sc_main 4(4*S n+2))).
 replace(4*S n+2)with(2*(2*n)+6)by lia;apply so_seven_one_finish.
Qed.
Lemma so_D_one_finish : forall k,
 csteps sc_tm(24*k*k+44*k+52)(sc_back StB(repeat S3(2*k+4))[S2;S2;S1])=
 Some(sc_main 8(4*k)).
Proof.
 intro k;replace(24*k*k+44*k+52)with
 (3+(4+((12*S k+7)+((2*S k+21)+(so_drain_cost(2*k)0+3)))))
 by(unfold so_drain_cost;nia).
 rewrite csteps_add.
 replace(2*k+4)with(S(2*k+3))by lia;cbn[repeat].
 rewrite so_emit_twos,csteps_add,so_enter_ones,csteps_add.
 replace(2*k+3)with(2*S k+1)by lia;rewrite so_odd_prepare_any,csteps_add,so_prepare_any,csteps_add.
 change(match csteps sc_tm(so_drain_cost(2*k)0)
 (sc_front StA(repeat S1 5++repeat S3(2*0))(repeat S3(2*k)++[S2;S2;S2]))with
 |Some c=>csteps sc_tm 3 c|None=>None end=Some(sc_main 8(4*k))).
 rewrite so_five_iter;unfold sc_main;replace(2*(0+2*k))with(4*k)by lia;reflexivity.
Qed.
Theorem so_odd_four : forall n,
 csteps sc_tm(120*n*n+132*n+74)(sc_C 4(2*n+1))=Some(sc_main 8(8*n)).
Proof.
 intro n;replace(120*n*n+132*n+74)with
 ((12*n+7)+((24*n*n+32*n+15)+(24*(2*n)*(2*n)+44*(2*n)+52)))by nia.
 unfold sc_C;cbn[repeat app];rewrite csteps_add,so_odd_prepare_any,csteps_add,so_odd_normalizer.
 replace(4*n+4)with(2*(2*n)+4)by lia.
 replace(8*n)with(4*(2*n))by lia;apply so_D_one_finish.
Qed.

Lemma so_even_C : forall a n,
 csteps sc_tm(12*n+7)(sc_C(a+3)(2*n))=Some(sc_C a(2*n+4)).
Proof.
 intros a n;unfold sc_C;replace(a+3)with(3+a)by lia;rewrite repeat_app;cbn[repeat app].
 apply sc_even.
Qed.
Lemma so_odd_C_from_normalizer :
 (forall n r,csteps sc_tm(24*n*n+32*n+15)
  (sc_front StA(repeat S1(2*n+1)++[S3;S3;S2])(S3::S3::r))=
  Some(sc_back StB(repeat S3(4*n+4))(S2::S2::r))) ->
 forall a n,2<=a ->
 csteps sc_tm(24*n*n+44*n+22)(sc_C(a+3)(2*n+1))=
 Some(sc_D(a-1)(4*n+4)).
Proof.
 intros Hnorm a n Ha;replace(24*n*n+44*n+22)with((12*n+7)+(24*n*n+32*n+15))by nia.
 unfold sc_C;replace(a+3)with(5+(a-2))by lia.
 rewrite(repeat_app S3 5(a-2));cbn[repeat app].
 rewrite csteps_add,sc_odd_prepare,Hnorm.
 unfold sc_D;replace(a-1)with(S(a-2))by lia;reflexivity.
Qed.
Lemma so_parity : forall b,(exists n,b=2*n)\/(exists n,b=2*n+1).
Proof.
 intro b;pose proof(Nat.div_mod b 2 ltac:(lia))as E.
 pose proof(Nat.mod_upper_bound b 2 ltac:(lia))as H.
 destruct(b mod 2)as[|[|r]]eqn:Er.
 - left;exists(b/2);lia.
 - right;exists(b/2);lia.
 - lia.
Qed.

(** The outer induction is independent of the interior normalizer proof.
    Its four explicit premises are discharged by Odd.v and the capped cases. *)
Theorem so_C_returns_from_rules :
 (forall a n,2<=a ->csteps sc_tm(24*n*n+44*n+22)(sc_C(a+3)(2*n+1))=
   Some(sc_D(a-1)(4*n+4))) ->
 (forall n,csteps sc_tm(24*n*n+68*n+64)(sc_C 2(2*n+3))=Some(sc_main 6(4*n+2))) ->
 (forall n,csteps sc_tm(24*n*n+44*n+29)(sc_C 3(2*n+1))=Some(sc_main 4(4*n+2))) ->
 (forall n,csteps sc_tm(120*n*n+132*n+74)(sc_C 4(2*n+1))=Some(sc_main 8(8*n))) ->
 forall a b,2<=a ->exists t A B,3<=t /\ 2<=A /\
 csteps sc_tm t(sc_C a b)=Some(sc_main A B).
Proof.
 intros Hodd Htwo Hthree Hfour a;induction a using lt_wf_ind;intros b Ha.
 destruct(so_parity b)as[(n&Eb)|(n&Eb)];subst b.
 - destruct a as[|[|[|[|a]]]];try lia.
   + exists(12*n+14),3,(2*n+1);repeat split;try lia;apply so_even_two.
   + exists(12*n+17),4,(2*n+1);repeat split;try lia;apply so_even_three.
   + destruct a as[|a].
     * exists(24*n+38),2,(2*n+5);repeat split;try lia;apply so_even_four.
     * pose(a':=S(S a)).
       assert(Ea:S(S(S(S(S a))))=a'+3)by(unfold a';lia).
       destruct(H a' ltac:(unfold a';lia)(2*n+4)ltac:(unfold a';lia))as(t&A&B&Ht&HA&E).
       exists(12*n+7+t),A,B;repeat split;try lia.
       rewrite Ea,csteps_add,so_even_C;exact E.
 - destruct a as[|[|[|[|a]]]];try lia.
   + destruct n as[|n].
     * exists(16+35),4,3;repeat split;try lia.
     * exists(24*n*n+68*n+64),6,(4*n+2);repeat split;try lia.
       replace(2*S n+1)with(2*n+3)by lia;apply Htwo.
   + exists(24*n*n+44*n+29),4,(4*n+2);repeat split;try lia;apply Hthree.
   + destruct a as[|a].
     * exists(120*n*n+132*n+74),8,(8*n);repeat split;try lia;apply Hfour.
     * pose(a':=S(S a)).
       assert(Ea:S(S(S(S(S a))))=a'+3)by(unfold a';lia).
       destruct(H a' ltac:(unfold a';lia)(4*n+5)ltac:(unfold a';lia))as(t&A&B&Ht&HA&E).
       assert(E3:csteps sc_tm 3(sc_C a'(4*n+5))=Some(sc_D(a'-1)(4*n+4))).
       {replace a' with(S(a'-1))by(unfold a';lia).
        replace(4*n+5)with(S(4*n+4))by lia;apply sc_C_three. }
       replace t with(3+(t-3))in E by lia;rewrite csteps_add,E3 in E.
       exists(24*n*n+44*n+22+(t-3)),A,B;repeat split;try nia.
       rewrite Ea,csteps_add,Hodd by(unfold a';lia);exact E.
Qed.

Theorem so_sound_from_returns :
 (forall a b,2<=a ->exists t A B,3<=t /\ 2<=A /\
  csteps sc_tm t(sc_C a b)=Some(sc_main A B)) ->NonHalt sc_tm /\ QHBound 0 sc_tm.
Proof.
 intro HC.
 assert(Hnext:forall a b,2<=a ->exists t A B,0<t /\ 2<=A /\
  csteps sc_tm t(sc_main a b)=Some(sc_main A B)).
 {intros a b Ha;destruct(HC a b Ha)as(t&A&B&Ht&HA&E).
  exists(a+1+t),A,B;repeat split;try lia;rewrite csteps_add,sc_start;exact E. }
 assert(Hreturn:forall N,exists t a b,N<=t /\ 2<=a /\
  csteps sc_tm t c0=Some(sc_main a b)).
 {intro N;induction N as[|N IH].
  - exists 51,3,3;repeat split;try lia;exact sc_entry.
  - destruct IH as(t&a&b&Ht&Ha&E);destruct(Hnext a b Ha)as(j&A&B&Hj&HA&E').
    exists(t+j),A,B;repeat split;try lia;rewrite csteps_add,E;exact E'. }
 assert(Hnh:NonHalt sc_tm).
 {intros n Hnone;destruct(Hreturn n)as(t&a&b&Ht&Ha&E).
  pose proof(csteps_lift sc_tm t c0(sc_main a b)E)as Er;rewrite lift_c0 in Er.
  destruct(stepn_prefix sc_tm n t InitES(lift(sc_main a b))Ht Er)as(c&Ec&_);congruence. }
 assert(HA:forall N,exists t,N<=t /\ VisitsAt sc_tm StA t).
 {intro N;destruct(Hreturn N)as(t&a&b&Ht&Ha&E);exists t;split;[exact Ht|].
  exists(lift(sc_main a b));split;[|reflexivity];rewrite <-lift_c0;apply csteps_lift;exact E. }
 assert(HB:forall N,exists t,N<=t /\ VisitsAt sc_tm StB t).
 {intro N;destruct(Hreturn N)as(t&a&b&Ht&Ha&E);exists(t+1);split;[lia|].
  exists(lift(sc_back StB(repeat S1 a++repeat S3 b)[S1]));split;[|reflexivity].
  rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity. }
 split;[exact Hnh|].
 intros q s[_ Hquiet];destruct q.
 - destruct(HA(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(HB(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.

Theorem so_C_returns : forall a b,2<=a ->exists t A B,3<=t /\ 2<=A /\
 csteps sc_tm t(sc_C a b)=Some(sc_main A B).
Proof.
 apply so_C_returns_from_rules.
 - apply so_odd_C_from_normalizer;exact so_odd_normalizer.
 - exact so_odd_two.
 - exact so_odd_three.
 - exact so_odd_four.
Qed.
Lemma so_main_next : forall a b,2<=a ->exists t A B,0<t /\ 2<=A /\
 csteps sc_tm t(sc_main a b)=Some(sc_main A B).
Proof.
 intros a b Ha;destruct(so_C_returns a b Ha)as(t&A&B&Ht&HA&E).
 exists(a+1+t),A,B;repeat split;try lia;rewrite csteps_add,sc_start;exact E.
Qed.
Lemma so_returns : forall N,exists t a b,N<=t /\ 2<=a /\
 csteps sc_tm t c0=Some(sc_main a b).
Proof.
 intro N;induction N as[|N IH].
 - exists 51,3,3;repeat split;try lia;exact sc_entry.
 - destruct IH as(t&a&b&Ht&Ha&E);destruct(so_main_next a b Ha)as(j&A&B&Hj&HA&E').
   exists(t+j),A,B;repeat split;try lia;rewrite csteps_add,E;exact E'.
Qed.
Theorem so_A_recurrent : forall N,exists t,N<=t /\ VisitsAt sc_tm StA t.
Proof.
 intro N;destruct(so_returns N)as(t&a&b&Ht&Ha&E);exists t;split;[exact Ht|].
 exists(lift(sc_main a b));split;[|reflexivity];rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem so_B_recurrent : forall N,exists t,N<=t /\ VisitsAt sc_tm StB t.
Proof.
 intro N;destruct(so_returns N)as(t&a&b&Ht&Ha&E);exists(t+1);split;[lia|].
 exists(lift(sc_back StB(repeat S1 a++repeat S3 b)[S1]));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem so_sound : NonHalt sc_tm /\ QHBound 0 sc_tm.
Proof. apply so_sound_from_returns;exact so_C_returns. Qed.
Print Assumptions so_sound.
