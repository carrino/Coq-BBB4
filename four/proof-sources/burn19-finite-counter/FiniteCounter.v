(** A finite block computation ending in permanent state B. All long counts
    are subsequently transported through binary N, never unary unrolled. *)
From Coq Require Import List Arith Lia Bool NArith.
From BBB24 Require Import Statement Spec CTape Census.
Import ListNotations.

Definition fc_tm:TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StB
 |StA,S2=>mkTrans S3 DR StA |StA,S3=>mkTrans S2 DL StA
 |StB,S0=>mkTrans S2 DR StB |StB,S1=>mkTrans S1 DR StA
 |StB,S2=>mkTrans S0 DL StB |StB,S3=>mkTrans S3 DL StA end).
Definition fc_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition fc_back q l r:cconf := (q,(ctl l,chd l,r)).
Definition fc_X a b:cconf := (StA,(repeat S3 a++repeat S2 b,S0,[])).
Definition fc_L b:cconf := (StA,(S1::repeat S2 b,S0,[])).
Definition fc_M a b:cconf := (StA,(repeat S3 a++S1::repeat S2 b,S0,[])).
Definition fc_phase a r:cconf := (StB,([],S0,repeat S0 a++r)).
Definition fc_flat_cost a b := 2*b*b+(2*a+1)*b.

Lemma fc_repeat_shift : forall (x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma fc_repeats : forall (x:Sym)n m l,
 repeat x n++repeat x m++l=repeat x(n+m)++l.
Proof. intros x n m l;rewrite repeat_app,app_assoc;reflexivity. Qed.
Lemma fc_repeat_end : forall (x:Sym)n,repeat x n++[x]=repeat x(n+1).
Proof. intros x n;rewrite fc_repeat_shift,app_nil_r;replace(n+1)with(S n)by lia;reflexivity. Qed.
Lemma fc_A_left : forall n l r,
 csteps fc_tm n(fc_back StA(repeat S3 n++l)r)=
 Some(fc_back StA l(repeat S2 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app fc_back csteps cstep fc_tm ctape_move chd ctl].
 change(csteps fc_tm n(fc_back StA(repeat S3 n++l)(S2::r))=
 Some(fc_back StA l(S2::(repeat S2 n++r)))).
 rewrite IHn,fc_repeat_shift;reflexivity.
Qed.
Lemma fc_A_right : forall n l r,
 csteps fc_tm n(fc_front StA l(repeat S2 n++r))=
 Some(fc_front StA(repeat S3 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app fc_front csteps cstep fc_tm ctape_move chd ctl].
 change(csteps fc_tm n(fc_front StA(S3::l)(repeat S2 n++r))=
 Some(fc_front StA(S3::(repeat S3 n++l))r)).
 rewrite IHn,fc_repeat_shift;reflexivity.
Qed.
Lemma fc_B_left : forall n l r,
 csteps fc_tm n(fc_back StB(repeat S2 n++l)r)=
 Some(fc_back StB l(repeat S0 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app fc_back csteps cstep fc_tm ctape_move chd ctl].
 change(csteps fc_tm n(fc_back StB(repeat S2 n++l)(S0::r))=
 Some(fc_back StB l(S0::(repeat S0 n++r)))).
 rewrite IHn,fc_repeat_shift;reflexivity.
Qed.
Lemma fc_B_right : forall n l r,
 csteps fc_tm n(fc_front StB l(repeat S0 n++r))=
 Some(fc_front StB(repeat S2 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app fc_front csteps cstep fc_tm ctape_move chd ctl].
 change(csteps fc_tm n(fc_front StB(S2::l)(repeat S0 n++r))=
 Some(fc_front StB(S2::(repeat S2 n++l))r)).
 rewrite IHn,fc_repeat_shift;reflexivity.
Qed.
Lemma fc_eat_three : forall n l r,
 csteps fc_tm(2*n+3)(fc_back StA(S2::l)(repeat S2 n++S3::r))=
 Some(fc_back StA l(repeat S2(n+2)++r)).
Proof.
 intros n l r;replace(2*n+3)with(1+(n+(1+S n)))by lia.
 rewrite csteps_add.
 change(csteps fc_tm(n+(1+S n))
  (fc_front StA(S3::l)(repeat S2 n++S3::r))=
 Some(fc_back StA l(repeat S2(n+2)++r))).
 rewrite csteps_add,fc_A_right,csteps_add.
 rewrite fc_repeat_shift.
 change(csteps fc_tm(S n)(fc_back StA(repeat S3(S n)++l)(S2::r))=
 Some(fc_back StA l(repeat S2(n+2)++r))).
 rewrite fc_A_left,fc_repeat_shift.
 replace(n+2)with(S(S n))by lia;reflexivity.
Qed.
Lemma fc_eat_one : forall n l r,
 csteps fc_tm(2*n+3)(fc_back StA(S2::l)(repeat S2 n++S1::r))=
 Some(fc_back StA l(repeat S2 n++S3::S2::r)).
Proof.
 intros n l r;replace(2*n+3)with(1+(n+(2+n)))by lia.
 rewrite csteps_add.
 change(csteps fc_tm(n+(2+n))
  (fc_front StA(S3::l)(repeat S2 n++S1::r))=
 Some(fc_back StA l(repeat S2 n++S3::S2::r))).
 rewrite csteps_add,fc_A_right,csteps_add,fc_repeat_shift.
 change(csteps fc_tm n(fc_back StA(repeat S3 n++l)(S3::S2::r))=
 Some(fc_back StA l(repeat S2 n++S3::S2::r))).
 apply fc_A_left.
Qed.
Lemma fc_blank_A : forall r,
 csteps fc_tm 3(fc_back StA[]r)=Some(fc_front StA[S1;S2]r).
Proof. intro r;reflexivity. Qed.
Lemma fc_start : forall n b,
 csteps fc_tm(n+2)(fc_X(S n)b)=
 Some(fc_back StA(repeat S2 b)(repeat S2 n++[S3;S1])).
Proof.
 intros n b;replace(n+2)with(2+n)by lia;rewrite csteps_add.
 change(csteps fc_tm n(fc_back StA(repeat S3 n++repeat S2 b)[S3;S1])=
 Some(fc_back StA(repeat S2 b)(repeat S2 n++[S3;S1]))).
 apply fc_A_left.
Qed.
Lemma fc_blank_three : forall n r,
 csteps fc_tm(2*n+5)(fc_back StA[](repeat S2 n++S3::r))=
 Some(fc_back StB[S2](repeat S2(n+2)++r)).
Proof.
 intros n r;replace(2*n+5)with(3+(n+(1+(n+1))))by lia.
 rewrite csteps_add,fc_blank_A,csteps_add,fc_A_right,csteps_add.
 change(csteps fc_tm(n+1)(fc_back StA(repeat S3 n++[S1;S2])(S2::r))=
 Some(fc_back StB[S2](repeat S2(n+2)++r))).
 rewrite csteps_add,fc_A_left.
 change(Some(fc_back StB[S2](S2::(repeat S2 n++S2::r)))=
 Some(fc_back StB[S2](repeat S2(n+2)++r))).
 rewrite fc_repeat_shift;replace(n+2)with(S(S n))by lia;reflexivity.
Qed.
Lemma fc_blank_one : forall n r,
 csteps fc_tm(2*S n+5)(fc_back StA[](repeat S2(S n)++S1::r))=
 Some(fc_back StB[S2](repeat S2(S n)++S3::S2::r)).
Proof.
 intros n r;replace(2*S n+5)with(3+(S n+(2+(n+1))))by lia.
 rewrite csteps_add,fc_blank_A,csteps_add,fc_A_right,csteps_add.
 change(csteps fc_tm(n+1)(fc_back StA(repeat S3 n++[S1;S2])(S3::S2::r))=
 Some(fc_back StB[S2](repeat S2(S n)++S3::S2::r))).
 rewrite csteps_add,fc_A_left;reflexivity.
Qed.
Lemma fc_seed_B : forall r,
 csteps fc_tm 1(fc_back StB[S2]r)=Some(fc_phase 1 r).
Proof. intro r;reflexivity. Qed.
Lemma fc_turn_B : forall a r,
 csteps fc_tm(2*a+3)(fc_phase a(S2::r))=Some(fc_phase(a+2)r).
Proof.
 intros a r;replace(2*a+3)with(S a+(1+S a))by lia;rewrite csteps_add.
 change(match csteps fc_tm(S a)(fc_front StB[](repeat S0(S a)++S2::r))with
 |Some c=>csteps fc_tm(1+S a)c|None=>None end=Some(fc_phase(a+2)r)).
 rewrite fc_B_right,csteps_add.
 change(csteps fc_tm(S a)(fc_back StB(repeat S2(S a)++[])(S0::r))=
 Some(fc_phase(a+2)r)).
 rewrite fc_B_left,fc_repeat_shift.
 replace(a+2)with(S(S a))by lia;reflexivity.
Qed.
Theorem fc_flat_B : forall b a r,
 csteps fc_tm(fc_flat_cost a b)(fc_phase a(repeat S2 b++r))=
 Some(fc_phase(a+2*b)r).
Proof.
 induction b;intros a r.
 - unfold fc_flat_cost;rewrite !Nat.mul_0_r,!Nat.add_0_r;reflexivity.
 - replace(fc_flat_cost a(S b))with((2*a+3)+fc_flat_cost(a+2)b)by(unfold fc_flat_cost;nia).
   rewrite csteps_add;cbn[repeat app];rewrite fc_turn_B,IHb.
   replace(a+2+2*b)with(a+2*S b)by lia;reflexivity.
Qed.
Lemma fc_exit_one : forall a r,
 csteps fc_tm(a+2)(fc_phase a(S1::r))=
 Some(fc_front StA(S1::repeat S2(S a))r).
Proof.
 intros a r;replace(a+2)with(S a+1)by lia;rewrite csteps_add.
 change(match csteps fc_tm(S a)(fc_front StB[](repeat S0(S a)++S1::r))with
 |Some c=>csteps fc_tm 1 c|None=>None end=Some(fc_front StA(S1::repeat S2(S a))r)).
 rewrite fc_B_right,app_nil_r;reflexivity.
Qed.
Lemma fc_exit_three : forall a r,
 csteps fc_tm(a+2)(fc_phase a(S3::r))=
 Some(fc_back StA(repeat S2(S a))(S3::r)).
Proof.
 intros a r;replace(a+2)with(S a+1)by lia;rewrite csteps_add.
 change(match csteps fc_tm(S a)(fc_front StB[](repeat S0(S a)++S3::r))with
 |Some c=>csteps fc_tm 1 c|None=>None end=Some(fc_back StA(repeat S2(S a))(S3::r))).
 rewrite fc_B_right,app_nil_r;reflexivity.
Qed.

Theorem fc_step4 : forall a b,1<=a ->
 csteps fc_tm(8*a+17)(fc_X a(b+4))=Some(fc_X(a+5)b).
Proof.
 intros a b Ha;destruct a as[|n];[lia|].
 replace(8*S n+17)with((n+2)+((2*n+3)+((2*(n+2)+3)+((2*(n+2)+3)+S(n+5)))))by lia.
 rewrite csteps_add,fc_start,csteps_add.
 replace(b+4)with(S(S(S(S b))))by lia;cbn[repeat].
 rewrite fc_eat_three,csteps_add,fc_eat_one,csteps_add,fc_eat_three.
 replace(n+2+2)with(n+4)by lia;rewrite fc_repeat_end.
 replace(n+4+1)with(n+5)by lia.
 change(csteps fc_tm(S(n+5))(fc_back StA(S2::repeat S2 b)(repeat S2(n+5)))=
 Some(fc_X(S n+5)b)).
 rewrite <-(app_nil_r(repeat S2(n+5)))at 1.
 replace(S(n+5))with(1+(n+5))by lia.
 rewrite csteps_add.
 change(csteps fc_tm(n+5)(fc_front StA(S3::repeat S2 b)(repeat S2(n+5)++[]))=
 Some(fc_X(S n+5)b)).
 rewrite fc_A_right,fc_repeat_shift;unfold fc_X;replace(S n+5)with(S(n+5))by lia;reflexivity.
Qed.
Theorem fc_step3 : forall a,1<=a ->
 csteps fc_tm(8*a+19)(fc_X a 3)=Some(fc_M(a+4)1).
Proof.
 intros a Ha;destruct a as[|n];[lia|].
 replace(8*S n+19)with((n+2)+((2*n+3)+((2*(n+2)+3)+((2*(n+2)+3)+(3+(n+5))))))by lia.
 rewrite csteps_add,fc_start,csteps_add;cbn[repeat].
 rewrite fc_eat_three,csteps_add,fc_eat_one,csteps_add,fc_eat_three.
 replace(n+2+2)with(n+4)by lia;rewrite fc_repeat_end.
 replace(n+4+1)with(n+5)by lia.
 change(csteps fc_tm(3+(n+5))(fc_back StA[](repeat S2(n+5)))=
 Some(fc_M(S n+4)1)).
 rewrite csteps_add,fc_blank_A.
 rewrite <-(app_nil_r(repeat S2(n+5)))at 1;rewrite fc_A_right.
 unfold fc_M;replace(S n+4)with(n+5)by lia;reflexivity.
Qed.

Lemma fc_finish_one : forall n,
 csteps fc_tm 23(fc_back StA(repeat S2(S(S(S(S n)))))[S3;S1])=
 Some(fc_X 6 n).
Proof.
 intro n;replace 23 with(3+(7+(7+6)))by lia;rewrite csteps_add.
 change(match csteps fc_tm(2*0+3)
  (fc_back StA(S2::repeat S2(S(S(S n))))(repeat S2 0++[S3;S1]))with
 |Some c=>csteps fc_tm(7+(7+6))c|None=>None end=Some(fc_X 6 n)).
 rewrite fc_eat_three,csteps_add.
 change(match csteps fc_tm(2*2+3)
  (fc_back StA(S2::repeat S2(S(S n)))(repeat S2 2++[S1]))with
 |Some c=>csteps fc_tm(7+6)c|None=>None end=Some(fc_X 6 n)).
 rewrite fc_eat_one,csteps_add.
 change(match csteps fc_tm(2*2+3)
  (fc_back StA(S2::repeat S2(S n))(repeat S2 2++[S3;S2]))with
 |Some c=>csteps fc_tm 6 c|None=>None end=Some(fc_X 6 n)).
 rewrite fc_eat_three.
 change(csteps fc_tm(1+5)(fc_back StA(S2::repeat S2 n)(repeat S2 5++[]))=
 Some(fc_X 6 n)).
 rewrite csteps_add.
 change(csteps fc_tm 5(fc_front StA(S3::repeat S2 n)(repeat S2 5++[]))=
 Some(fc_X 6 n)).
 rewrite fc_A_right;reflexivity.
Qed.
Lemma fc_finish_two : forall n,
 csteps fc_tm 7(fc_back StA(repeat S2(S(S n)))[S3;S2])=Some(fc_X 4 n).
Proof.
 intro n;replace 7 with(3+4)by lia;rewrite csteps_add.
 change(match csteps fc_tm(2*0+3)
  (fc_back StA(S2::repeat S2(S n))(repeat S2 0++[S3;S2]))with
 |Some c=>csteps fc_tm 4 c|None=>None end=Some(fc_X 4 n)).
 rewrite fc_eat_three.
 change(csteps fc_tm(1+3)(fc_back StA(S2::repeat S2 n)(repeat S2 3++[]))=
 Some(fc_X 4 n)).
 rewrite csteps_add.
 change(csteps fc_tm 3(fc_front StA(S3::repeat S2 n)(repeat S2 3++[]))=
 Some(fc_X 4 n)).
 rewrite fc_A_right;reflexivity.
Qed.

Theorem fc_step0 : forall a,1<=a ->
 csteps fc_tm(2*a*a+12*a+15)(fc_X a 0)=Some(fc_L(2*a+4)).
Proof.
 intros a Ha;destruct a as[|n];[lia|].
 replace(2*S n*S n+12*S n+15)with
 ((n+2)+((2*n+5)+(1+(fc_flat_cost 1(n+2)+(1+2*(n+2)+2)))))by(unfold fc_flat_cost;nia).
 rewrite csteps_add,fc_start,csteps_add,fc_blank_three,csteps_add,fc_seed_B.
 rewrite csteps_add,fc_flat_B,fc_exit_one.
 unfold fc_L;replace(S(1+2*(n+2)))with(2*S n+4)by lia;reflexivity.
Qed.
Theorem fc_step1 : forall a,1<=a ->
 csteps fc_tm(2*a*a+14*a+27)(fc_X a 1)=Some(fc_X 4(2*a+2)).
Proof.
 intros a Ha;destruct a as[|n];[lia|].
 replace(2*S n*S n+14*S n+27)with
 ((n+2)+((2*n+3)+((2*(n+2)+5)+(1+
 (fc_flat_cost 1(n+2)+((1+2*(n+2)+2)+7))))))by(unfold fc_flat_cost;nia).
 rewrite csteps_add,fc_start,csteps_add;cbn[repeat];rewrite fc_eat_three,csteps_add.
 replace(n+2)with(S(n+1))by lia;rewrite fc_blank_one,csteps_add,fc_seed_B.
 rewrite csteps_add,fc_flat_B,csteps_add,fc_exit_three.
 replace(S(1+2*S(n+1)))with(S(S(2*S n+2)))by lia.
 apply fc_finish_two.
Qed.
Theorem fc_step2 : forall a,1<=a ->
 csteps fc_tm(2*a*a+26*a+59)(fc_X a 2)=Some(fc_phase(2*a+9)[]).
Proof.
 intros a Ha;destruct a as[|n];[lia|].
 replace(2*S n*S n+26*S n+59)with
 ((n+2)+((2*n+3)+((2*(n+2)+3)+((2*(n+2)+5)+(1+fc_flat_cost 1(n+5))))))
 by(unfold fc_flat_cost;nia).
 rewrite csteps_add,fc_start,csteps_add;cbn[repeat].
 rewrite fc_eat_three,csteps_add,fc_eat_one,csteps_add,fc_blank_three.
 rewrite fc_repeat_end;replace(n+2+2+1)with(n+5)by lia.
 rewrite csteps_add,fc_seed_B.
 rewrite <-(app_nil_r(repeat S2(n+5)))at 1;rewrite fc_flat_B.
 replace(1+2*(n+5))with(2*S n+9)by lia;reflexivity.
Qed.
Theorem fc_L_step : forall b,
 csteps fc_tm 5(fc_L b)=Some(fc_M 1 b).
Proof. intro b;reflexivity. Qed.
Theorem fc_M_one : forall b,1<=b ->
 csteps fc_tm(4*b+33)(fc_M 1 b)=Some(fc_X 6(b-1)).
Proof.
 intros b Hb;destruct b as[|n];[lia|].
 replace(4*S n+33)with(3+(S n+(fc_flat_cost(S n)1+((S n+2+2)+23))))
 by(unfold fc_flat_cost;nia).
 rewrite csteps_add.
 change(csteps fc_tm(S n+(fc_flat_cost(S n)1+((S n+2+2)+23)))
 (fc_back StB(repeat S2(S n))[S2;S3;S1])=Some(fc_X 6(S n-1))).
 rewrite <-(app_nil_r(repeat S2(S n)))at 1.
 rewrite csteps_add,fc_B_left.
 change(csteps fc_tm(fc_flat_cost(S n)1+((S n+2+2)+23))
 (fc_phase(S n)(repeat S2 1++[S3;S1]))=Some(fc_X 6(S n-1))).
 rewrite csteps_add,fc_flat_B,csteps_add,fc_exit_three.
 replace(S(S n+2*1))with(S(S(S(S n))))by lia.
 replace(S n-1)with n by lia;apply fc_finish_one.
Qed.
Theorem fc_M_step : forall a,1<=a ->
 csteps fc_tm(2*a*a+6*a+29)(fc_M a 1)=Some(fc_X 6(2*a-2)).
Proof.
 intros a Ha;destruct a as[|n];[lia|].
 replace(2*S n*S n+6*S n+29)with
 ((n+3)+(1+(fc_flat_cost 1(S n)+((1+2*S n+2)+23))))by(unfold fc_flat_cost;nia).
 rewrite csteps_add.
 assert(E:csteps fc_tm(n+3)(fc_M(S n)1)=
 Some(fc_back StB[S2](repeat S2(S n)++[S3;S1]))).
 {replace(n+3)with(2+(n+1))by lia;rewrite csteps_add.
  change(csteps fc_tm(n+1)(fc_back StA(repeat S3 n++[S1;S2])[S3;S1])=
  Some(fc_back StB[S2](repeat S2(S n)++[S3;S1]))).
  rewrite csteps_add,fc_A_left;reflexivity. }
 rewrite E,csteps_add,fc_seed_B,csteps_add,fc_flat_B,csteps_add,fc_exit_three.
 replace(S(1+2*S n))with(S(S(S(S(2*n)))))by lia.
 replace(2*S n-2)with(2*n)by lia;apply fc_finish_one.
Qed.

Definition fc_bulk_cost q a := q*(8*a+17)+20*q*(q-1).
Lemma fc_bulk_cost_next : forall q a,
 fc_bulk_cost(S q)a=(8*a+17)+fc_bulk_cost q(a+5).
Proof.
 intros q a;destruct q as[|q];unfold fc_bulk_cost.
 - cbn;nia.
 - replace(S q-1)with q by lia;replace(S(S q)-1)with(S q)by lia;nia.
Qed.
Theorem fc_bulk : forall q a b,1<=a ->
 csteps fc_tm(fc_bulk_cost q a)(fc_X a(4*q+b))=Some(fc_X(a+5*q)b).
Proof.
 induction q;intros a b Ha.
 - unfold fc_bulk_cost;cbn;rewrite Nat.add_0_r;reflexivity.
 - rewrite fc_bulk_cost_next,csteps_add.
   replace(4*S q+b)with((4*q+b)+4)by lia.
   rewrite fc_step4 by exact Ha;rewrite IHq by lia.
   replace(a+5+5*q)with(a+5*S q)by lia;reflexivity.
Qed.

Definition fc_count(n:N):nat := N.to_nat n.
Lemma fc_count_add : forall a b,fc_count(a+b)=fc_count a+fc_count b.
Proof. intros a b;unfold fc_count;apply N2Nat.inj_add. Qed.
Lemma fc_compN : forall a b c d e,
 csteps fc_tm(fc_count a)c=Some d ->csteps fc_tm(fc_count b)d=Some e ->
 csteps fc_tm(fc_count(a+b))c=Some e.
Proof. intros a b c d e H H';rewrite fc_count_add,csteps_add,H;exact H'. Qed.
Lemma fc_count_le : forall a b,(a<=b)%N ->fc_count a<=fc_count b.
Proof. intros a b H;unfold fc_count;apply Nat.compare_le_iff;rewrite <-N2Nat.inj_compare;exact H. Qed.
Ltac fc_binary := unfold fc_count;
 repeat first[rewrite N2Nat.inj_add|rewrite N2Nat.inj_mul|rewrite N2Nat.inj_sub].
Theorem fc_N_bulk : forall q a b,(1<=a)%N ->
 csteps fc_tm(fc_count(q*(8*a+17)+20*q*(q-1)))
 (fc_X(fc_count a)(fc_count(4*q+b)))=
 Some(fc_X(fc_count(a+5*q))(fc_count b)).
Proof.
 intros q a b Ha;fc_binary;apply fc_bulk.
 exact(fc_count_le 1 a Ha).
Qed.
Theorem fc_N_step0 : forall a,(1<=a)%N ->
 csteps fc_tm(fc_count(2*a*a+12*a+15))(fc_X(fc_count a)0)=
 Some(fc_L(fc_count(2*a+4))).
Proof. intros a Ha;fc_binary;apply fc_step0;exact(fc_count_le 1 a Ha). Qed.
Theorem fc_N_step1 : forall a,(1<=a)%N ->
 csteps fc_tm(fc_count(2*a*a+14*a+27))(fc_X(fc_count a)1)=
 Some(fc_X 4(fc_count(2*a+2))).
Proof. intros a Ha;fc_binary;apply fc_step1;exact(fc_count_le 1 a Ha). Qed.
Theorem fc_N_step2 : forall a,(1<=a)%N ->
 csteps fc_tm(fc_count(2*a*a+26*a+59))(fc_X(fc_count a)2)=
 Some(fc_phase(fc_count(2*a+9))[]).
Proof. intros a Ha;fc_binary;apply fc_step2;exact(fc_count_le 1 a Ha). Qed.
Theorem fc_N_step3 : forall a,(1<=a)%N ->
 csteps fc_tm(fc_count(8*a+19))(fc_X(fc_count a)3)=
 Some(fc_M(fc_count(a+4))1).
Proof. intros a Ha;fc_binary;apply fc_step3;exact(fc_count_le 1 a Ha). Qed.
Theorem fc_N_M_one : forall b,(1<=b)%N ->
 csteps fc_tm(fc_count(4*b+33))(fc_M 1(fc_count b))=
 Some(fc_X 6(fc_count(b-1))).
Proof. intros b Hb;fc_binary;apply fc_M_one;exact(fc_count_le 1 b Hb). Qed.
Theorem fc_N_M_step : forall a,(1<=a)%N ->
 csteps fc_tm(fc_count(2*a*a+6*a+29))(fc_M(fc_count a)1)=
 Some(fc_X 6(fc_count(2*a-2))).
Proof. intros a Ha;fc_binary;apply fc_M_step;exact(fc_count_le 1 a Ha). Qed.

Lemma fc_B_drift : forall t l n,exists l' n',
 csteps fc_tm t(StB,(l,S0,repeat S0 n))=Some(StB,(l',S0,repeat S0 n')).
Proof.
 induction t;intros l n.
 - exists l,n;reflexivity.
 - destruct n;cbn[repeat csteps cstep fc_tm ctape_move chd ctl t_next t_dir t_write].
   + exact(IHt(S2::l)0).
   + exact(IHt(S2::l)n).
Qed.
Lemma fc_after_run : forall d m,
 csteps fc_tm d c0=Some(fc_phase m[]) ->
 forall t,exists l n,csteps fc_tm(d+t)c0=Some(StB,(l,S0,repeat S0 n)).
Proof.
 intros d m E t;rewrite csteps_add,E;unfold fc_phase;rewrite app_nil_r.
 apply fc_B_drift.
Qed.
Theorem fc_eventual_B_bound : forall d m,
 csteps fc_tm d c0=Some(fc_phase m[]) -> NonHalt fc_tm /\ QHBound d fc_tm.
Proof.
 intros d m E.
 assert(HB:forall n,d<=n ->VisitsAt fc_tm StB n).
 {intros n Hn;destruct(fc_after_run d m E(n-d))as(l&k&Ek).
  replace(d+(n-d))with n in Ek by lia.
  exists(lift(StB,(l,S0,repeat S0 k)));split;[|reflexivity].
  rewrite <-lift_c0;apply csteps_lift;exact Ek. }
 assert(Hnh:NonHalt fc_tm).
 {intros n Hnone;destruct(le_lt_dec d n).
  - destruct(HB n l)as(c&Ec&_);congruence.
  - pose proof(csteps_lift fc_tm d c0(fc_phase m[])E)as E';rewrite lift_c0 in E'.
    destruct(stepn_prefix fc_tm n d InitES(lift(fc_phase m[]))ltac:(lia)E')as(c&Ec&_);congruence. }
 split;[exact Hnh|].
 intros q s[Hv Hquiet];destruct(le_lt_dec d s);[|lia].
 destruct q.
 - destruct Hv as(c&Ec&Hs);destruct(HB s l)as(c'&Ec'&Hs');rewrite Ec in Ec'.
   injection Ec' as <-;congruence.
 - exfalso;apply(Hquiet(S s));[lia|apply HB;lia].
Qed.
