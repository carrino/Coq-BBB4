(** S043: leftward growth, an odd two-run reset, and a stable 01 tail. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census.
Import ListNotations.
Definition sg_tm:TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StA
 |StA,S2=>mkTrans S3 DR StB |StA,S3=>mkTrans S2 DL StA
 |StB,S0=>mkTrans S2 DR StB |StB,S1=>mkTrans S2 DL StA
 |StB,S2=>mkTrans S3 DR StA |StB,S3=>mkTrans S0 DL StB end).
Definition sg_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition sg_back q l r:cconf := (q,(ctl l,chd l,r)).
Definition sg_left a r:cconf := (StA,([],S0,repeat S2 a++r)).
Definition sg_C a b := sg_left a(repeat S1 b++[S0;S1]).
Definition sg_M n := sg_C 5(2*n).
Lemma sg_shift : forall(x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma sg_repeats : forall(x:Sym)n m l,
 repeat x n++repeat x m++l=repeat x(n+m)++l.
Proof. intros;rewrite repeat_app,app_assoc;reflexivity. Qed.
Lemma sg_start_left : forall r,csteps sg_tm 5(StA,([],S0,r))=
 Some(sg_front StA[S3;S3]r).
Proof. intros;reflexivity. Qed.
Lemma sg_A_left_threes : forall n l r,
 csteps sg_tm n(sg_back StA(repeat S3 n++l)r)=
 Some(sg_back StA l(repeat S2 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app sg_back csteps cstep sg_tm ctape_move chd ctl].
 change(csteps sg_tm n(sg_back StA(repeat S3 n++l)(S2::r))=
 Some(sg_back StA l(S2::(repeat S2 n++r)))).
 rewrite IHn,sg_shift;reflexivity.
Qed.
Lemma sg_B_left_threes : forall n l r,
 csteps sg_tm n(sg_back StB(repeat S3 n++l)r)=
 Some(sg_back StB l(repeat S0 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app sg_back csteps cstep sg_tm ctape_move chd ctl].
 change(csteps sg_tm n(sg_back StB(repeat S3 n++l)(S0::r))=
 Some(sg_back StB l(S0::(repeat S0 n++r)))).
 rewrite IHn,sg_shift;reflexivity.
Qed.
Lemma sg_B_right_zeros : forall n l r,
 csteps sg_tm n(sg_front StB l(repeat S0 n++r))=
 Some(sg_front StB(repeat S2 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app sg_front csteps cstep sg_tm ctape_move chd ctl].
 change(csteps sg_tm n(sg_front StB(S2::l)(repeat S0 n++r))=
 Some(sg_front StB(S2::(repeat S2 n++l))r)).
 rewrite IHn,sg_shift;reflexivity.
Qed.
Lemma sg_twos_one : forall n q l r,
 csteps sg_tm(n+1)(sg_front q l(repeat S2 n++S1::r))=
 Some(sg_back StA(repeat S3 n++l)(S2::r)).
Proof.
 induction n;intros q l r;[destruct q;reflexivity|].
 replace(S n+1)with(1+(n+1))by lia;rewrite csteps_add;destruct q.
 - change(csteps sg_tm(n+1)(sg_front StB(S3::l)(repeat S2 n++S1::r))=Some(sg_back StA(S3::(repeat S3 n++l))(S2::r)));rewrite IHn,sg_shift;reflexivity.
 - change(csteps sg_tm(n+1)(sg_front StA(S3::l)(repeat S2 n++S1::r))=Some(sg_back StA(S3::(repeat S3 n++l))(S2::r)));rewrite IHn,sg_shift;reflexivity.
Qed.
Lemma sg_twos_pair : forall n q l r,
 csteps sg_tm(2*n)(sg_front q l(repeat S2(2*n)++r))=
 Some(sg_front q(repeat S3(2*n)++l)r).
Proof.
 induction n;intros q l r;[reflexivity|].
 replace(2*S n)with(2+2*n)by lia;cbn[repeat app];rewrite csteps_add;destruct q.
 - change(csteps sg_tm(2*n)(sg_front StA(S3::S3::l)(repeat S2(2*n)++r))=Some(sg_front StA(S3::S3::(repeat S3(2*n)++l))r));rewrite IHn,!sg_shift;reflexivity.
 - change(csteps sg_tm(2*n)(sg_front StB(S3::S3::l)(repeat S2(2*n)++r))=Some(sg_front StB(S3::S3::(repeat S3(2*n)++l))r));rewrite IHn,!sg_shift;reflexivity.
Qed.
Lemma sg_twos_odd : forall n l r,
 csteps sg_tm(2*n+1)(sg_front StA l(repeat S2(2*n+1)++r))=
 Some(sg_front StB(repeat S3(2*n+1)++l)r).
Proof.
 intros;replace(2*n+1)with(1+2*n)by lia;cbn[repeat app];rewrite csteps_add.
 change(csteps sg_tm(2*n)(sg_front StB(S3::l)(repeat S2(2*n)++r))=
 Some(sg_front StB(S3::(repeat S3(2*n)++l))r)).
 rewrite sg_twos_pair,sg_shift;reflexivity.
Qed.
Theorem sg_consume_one : forall a r,
 csteps sg_tm(2*a+8)(sg_left a(S1::r))=Some(sg_left(a+3)r).
Proof.
 intros;replace(2*a+8)with(5+((a+1)+(a+2)))by lia.
 unfold sg_left;rewrite csteps_add,sg_start_left,csteps_add,sg_twos_one.
 replace(repeat S3 a++[S3;S3])with(repeat S3(a+2))by(rewrite repeat_app;cbn;reflexivity).
 pose proof(sg_A_left_threes(a+2)[](S2::r))as E;rewrite app_nil_r in E;rewrite E.
 unfold sg_left,sg_back;rewrite sg_shift.
 replace(a+3)with(S(a+2))by lia;reflexivity.
Qed.
Theorem sg_three_first : forall m,
 csteps sg_tm(2*m+5)(StA,(repeat S3 m,S0,[]))=
 Some(StA,(S3::S3::repeat S2 m,S0,[])).
Proof.
 intro m;replace(2*m+5)with(1+(m+(1+(m+3))))by lia;rewrite csteps_add.
 change(csteps sg_tm(m+(1+(m+3)))(sg_back StB(repeat S3 m)[S1])=
 Some(StA,(S3::S3::repeat S2 m,S0,[]))).
 pose proof(sg_B_left_threes m[][S1])as E;rewrite app_nil_r in E;rewrite csteps_add,E,csteps_add.
 change(csteps sg_tm(m+3)(sg_front StB[S2](repeat S0 m++[S1]))=
 Some(StA,(S3::S3::repeat S2 m,S0,[]))).
 rewrite csteps_add,sg_B_right_zeros,sg_shift;rewrite app_nil_r.
 reflexivity.
Qed.
Lemma sg_B_two_defect : forall n l r,
 csteps sg_tm(3*n)(sg_back StB(repeat S2 n++l)(S0::r))=
 Some(sg_back StB l(S0::(repeat S1 n++r))).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(3*S n)with(3+3*n)by lia;rewrite csteps_add.
 change(csteps sg_tm(3*n)(sg_back StB(repeat S2 n++l)(S0::S1::r))=
 Some(sg_back StB l(S0::S1::(repeat S1 n++r)))).
 rewrite IHn,sg_shift;reflexivity.
Qed.
Lemma sg_defect_finish : forall r,
 csteps sg_tm 17(sg_back StB[](S0::S1::S1::S1::r))=
 Some(sg_left 5 r).
Proof. intros;reflexivity. Qed.
Theorem sg_three_final : forall n,
 csteps sg_tm(5*n+40)(StA,(repeat S3(n+3),S0,[]))=Some(sg_C 5 n).
Proof.
 intro n;replace(5*n+40)with((2*(n+3)+5)+(3+(3*(n+3)+17)))by lia.
 rewrite csteps_add,sg_three_first,csteps_add.
 change(csteps sg_tm(3*(n+3)+17)(sg_back StB(repeat S2(n+3))[S0;S0;S1])=Some(sg_C 5 n)).
 pose proof(sg_B_two_defect(n+3)[][S0;S1])as E;rewrite app_nil_r in E;rewrite csteps_add,E.
 replace(n+3)with(3+n)by lia;cbn[repeat app].
 apply sg_defect_finish.
Qed.
Theorem sg_odd_reset : forall n,
 csteps sg_tm(12*n+60)(sg_C(2*n+1)0)=Some(sg_C 5(2*n+2)).
Proof.
 intro n;replace(12*n+60)with((5+((2*n+1)+4))+(5*(2*n+2)+40))by lia.
 unfold sg_C at 1;unfold sg_left;cbn[repeat app];rewrite csteps_add,csteps_add,sg_start_left,csteps_add,sg_twos_odd.
 change(csteps sg_tm(5*(2*n+2)+40)
 (StA,(S3::S3::(repeat S3(2*n+1)++[S3;S3]),S0,[]))=Some(sg_C 5(2*n+2))).
 replace(S3::S3::(repeat S3(2*n+1)++[S3;S3]))with(repeat S3((2*n+2)+3)).
 - apply sg_three_final.
 - replace((2*n+2)+3)with(4+(2*n+1))by lia;cbn[repeat app];rewrite !sg_shift,app_nil_r;reflexivity.
Qed.
