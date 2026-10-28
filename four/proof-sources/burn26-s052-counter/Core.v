(** Local sweeps and the even carry of the complete S052 table. *)
From Coq Require Import List Arith Lia Bool NArith.
From BBB24 Require Import Statement Spec CTape Census.
Import ListNotations.

Definition sh_tm:TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StB
 |StA,S2=>mkTrans S1 DR StA |StA,S3=>mkTrans S2 DL StA
 |StB,S0=>mkTrans S0 DR StB |StB,S1=>mkTrans S3 DL StB
 |StB,S2=>mkTrans S3 DR StB |StB,S3=>mkTrans S1 DR StA end).
Definition sh_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition sh_back q l r:cconf := (q,(ctl l,chd l,r)).
Definition sh_C a b := sh_back StB(repeat S3 b++[S0])(repeat S3 a++[S1]).
Definition sh_D a b := sh_back StB(repeat S3 b++[S0])(S2::S2::(repeat S3 a++[S1])).
Definition sh_main a b:cconf := (StA,(repeat S1 a++repeat S3 b++[S0],S0,[])).
Definition sh_main_two a:cconf := (StA,(repeat S1 a++[S2;S0],S0,[])).

Lemma sh_repeat_shift : forall (x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma sh_repeat_end : forall (x:Sym)n,repeat x n++[x]=repeat x(n+1).
Proof. intros x n;rewrite sh_repeat_shift,app_nil_r;replace(n+1)with(S n)by lia;reflexivity. Qed.
Lemma sh_repeat_join : forall (x:Sym)n m l,
 repeat x n++repeat x m++l=repeat x(n+m)++l.
Proof. intros x n m l;rewrite repeat_app,app_assoc;reflexivity. Qed.
Lemma sh_B_right_twos : forall n l r,
 csteps sh_tm n(sh_front StB l(repeat S2 n++r))=
 Some(sh_front StB(repeat S3 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app sh_front csteps cstep sh_tm ctape_move chd ctl].
 change(csteps sh_tm n(sh_front StB(S3::l)(repeat S2 n++r))=
 Some(sh_front StB(S3::(repeat S3 n++l))r)).
 rewrite IHn,sh_repeat_shift;reflexivity.
Qed.
Lemma sh_A_right_twos : forall n l r,
 csteps sh_tm n(sh_front StA l(repeat S2 n++r))=
 Some(sh_front StA(repeat S1 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app sh_front csteps cstep sh_tm ctape_move chd ctl].
 change(csteps sh_tm n(sh_front StA(S1::l)(repeat S2 n++r))=
 Some(sh_front StA(S1::(repeat S1 n++l))r)).
 rewrite IHn,sh_repeat_shift;reflexivity.
Qed.
Lemma sh_B_left_ones : forall n l r,
 csteps sh_tm n(sh_back StB(repeat S1 n++l)r)=
 Some(sh_back StB l(repeat S3 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app sh_back csteps cstep sh_tm ctape_move chd ctl].
 change(csteps sh_tm n(sh_back StB(repeat S1 n++l)(S3::r))=
 Some(sh_back StB l(S3::(repeat S3 n++r)))).
 rewrite IHn,sh_repeat_shift;reflexivity.
Qed.
Lemma sh_A_left_threes : forall n l r,
 csteps sh_tm n(sh_back StA(repeat S3 n++l)r)=
 Some(sh_back StA l(repeat S2 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app sh_back csteps cstep sh_tm ctape_move chd ctl].
 change(csteps sh_tm n(sh_back StA(repeat S3 n++l)(S2::r))=
 Some(sh_back StA l(S2::(repeat S2 n++r)))).
 rewrite IHn,sh_repeat_shift;reflexivity.
Qed.
Lemma sh_pair : forall l r,
 csteps sh_tm 10(sh_back StB(S3::S3::l)(S3::S3::r))=
 Some(sh_back StB l(S3::S3::S2::S2::r)).
Proof. intros l r;reflexivity. Qed.
Lemma sh_pairs : forall n l r,
 csteps sh_tm(10*n)(sh_back StB(repeat S3(2*n)++l)(S3::S3::r))=
 Some(sh_back StB l(S3::S3::(repeat S2(2*n)++r))).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(10*S n)with(10+10*n)by lia.
 replace(2*S n)with(S(S(2*n)))by lia;cbn[repeat app].
 rewrite csteps_add,sh_pair,IHn,sh_repeat_shift,sh_repeat_shift;reflexivity.
Qed.
Definition sh_H n r := sh_front StA(repeat S1(2*n+1)++[S3;S3;S0])(S3::r).
Lemma sh_blank_C : forall m r,
 csteps sh_tm(m+8)(sh_back StB[S0](S3::S3::(repeat S2 m++S3::r)))=
 Some(sh_front StA(S1::(repeat S3(m+2)++[S0]))r).
Proof.
 intros;replace(m+8)with(5+((m+2)+1))by lia;rewrite csteps_add.
 change(csteps sh_tm((m+2)+1)(sh_front StB[S0](S2::S2::(repeat S2 m++S3::r)))=
 Some(sh_front StA(S1::(repeat S3(m+2)++[S0]))r)).
 replace(m+2)with(S(S m))by lia;pose proof(sh_B_right_twos(S(S m))[S0](S3::r))as E;cbn[repeat app]in E;rewrite csteps_add,E;reflexivity.
Qed.
Lemma sh_even : forall n r,
 csteps sh_tm(12*n+8)(sh_back StB(repeat S3(2*n)++[S0])(S3::S3::S3::r))=
 Some(sh_front StA(S1::(repeat S3(2*n+2)++[S0]))r).
Proof.
 intros;replace(12*n+8)with(10*n+(2*n+8))by lia.
 rewrite csteps_add,sh_pairs,sh_blank_C;reflexivity.
Qed.
Lemma sh_odd_boundary : forall m r,
 csteps sh_tm(m+7)(sh_back StB[S3;S0](S3::S3::(repeat S2 m++S3::r)))=
 Some(sh_front StA(repeat S1(S m)++[S3;S3;S0])(S3::r)).
Proof.
 intros;replace(m+7)with(7+m)by lia;rewrite csteps_add.
 change(csteps sh_tm m(sh_front StA[S1;S3;S3;S0](repeat S2 m++S3::r))=
 Some(sh_front StA(repeat S1(S m)++[S3;S3;S0])(S3::r))).
 rewrite sh_A_right_twos,sh_repeat_shift;reflexivity.
Qed.
Lemma sh_odd_prepare : forall n r,
 csteps sh_tm(12*n+7)(sh_back StB(repeat S3(2*n+1)++[S0])(S3::S3::S3::r))=
 Some(sh_H n r).
Proof.
 intros;replace(12*n+7)with(10*n+(2*n+7))by lia.
 rewrite repeat_app,<-app_assoc;cbn[repeat app].
 change(csteps sh_tm(10*n+(2*n+7))
 (sh_back StB(repeat S3(2*n)++[S3;S0])(S3::S3::S3::r))=Some(sh_H n r)).
 rewrite csteps_add,sh_pairs,sh_odd_boundary.
 unfold sh_H;replace(S(2*n))with(2*n+1)by lia;reflexivity.
Qed.
Lemma sh_launch : forall m l r,
 csteps sh_tm(m+3)(sh_front StA(repeat S1(S m)++S3::l)(S3::r))=
 Some(sh_front StA(S1::l)(repeat S3 m++S2::S2::r)).
Proof.
 intros;replace(m+3)with(2+(m+1))by lia;rewrite csteps_add.
 change(csteps sh_tm(m+1)(sh_back StB(repeat S1 m++S3::l)(S2::S2::r))=
 Some(sh_front StA(S1::l)(repeat S3 m++S2::S2::r))).
 rewrite csteps_add,sh_B_left_ones;reflexivity.
Qed.
Lemma sh_small_one : forall l r,
 csteps sh_tm 5(sh_front StA(S1::S3::l)(S3::r))=
 Some(sh_front StA(S1::S1::S1::l)r).
Proof. intros;reflexivity. Qed.
Lemma sh_fall : forall m r,
 csteps sh_tm(m+5)(sh_front StA(repeat S1(m+2)++[S0])(S3::r))=
 Some(sh_front StA[S1;S0](repeat S3 m++S2::S2::r)).
Proof.
 intros;replace(m+5)with(2+((m+1)+2))by lia.
 replace(m+2)with(S(S m))by lia;rewrite csteps_add.
 change(csteps sh_tm((m+1)+2)(sh_back StB(repeat S1(S m)++[S0])(S2::S2::r))=
 Some(sh_front StA[S1;S0](repeat S3 m++S2::S2::r))).
 replace(m+1)with(S m)by lia;rewrite csteps_add,sh_B_left_ones;reflexivity.
Qed.
Lemma sh_blank_single : forall m r,
 csteps sh_tm(m+6)(sh_front StA[S1;S0](S3::(repeat S2 m++S3::r)))=
 Some(sh_front StA(S1::(repeat S3(m+2)++[S0]))r).
Proof.
 intros;replace(m+6)with(3+((m+2)+1))by lia;rewrite csteps_add.
 change(csteps sh_tm((m+2)+1)(sh_front StB[S0](S2::S2::(repeat S2 m++S3::r)))=
 Some(sh_front StA(S1::(repeat S3(m+2)++[S0]))r)).
 replace(m+2)with(S(S m))by lia;pose proof(sh_B_right_twos(S(S m))[S0](S3::r))as E;cbn[repeat app]in E;rewrite csteps_add,E;reflexivity.
Qed.
Lemma sh_seven_after_even : forall l r,
 csteps sh_tm 7(sh_front StA(S1::S3::l)(S3::S2::S2::r))=
 Some(sh_front StA(repeat S1 5++l)r).
Proof. intros;reflexivity. Qed.
Theorem sh_five_even : forall j r,
 csteps sh_tm(12*j+21)(sh_front StA(repeat S1 5++repeat S3(2*j)++[S0])(S3::r))=
 Some(sh_front StA(repeat S1 5++repeat S3(2*j+1)++[S0])r).
Proof.
 intros;replace(12*j+21)with(6+(10*j+((2*j+8)+7)))by lia;rewrite csteps_add.
 change(csteps sh_tm(10*j+((2*j+8)+7))
 (sh_back StB(repeat S3(2*j)++[S0])(S3::S3::S3::S3::S2::S2::r))=
 Some(sh_front StA(repeat S1 5++repeat S3(2*j+1)++[S0])r)).
 rewrite csteps_add,sh_pairs,csteps_add,sh_blank_C.
 replace(2*j+2)with(S(2*j+1))by lia;apply sh_seven_after_even.
Qed.
Theorem sh_five_odd_bridge : forall j r,
 csteps sh_tm(12*j+13)(sh_front StA(repeat S1 5++repeat S3(2*j+1)++[S0])(S3::r))=
 Some(sh_H j(S3::S2::S2::r)).
Proof.
 intros;replace(12*j+13)with(6+(10*j+(2*j+7)))by lia;rewrite csteps_add.
 change(csteps sh_tm(10*j+(2*j+7))
 (sh_back StB(repeat S3(2*j+1)++[S0])(S3::S3::S3::S3::S2::S2::r))=
 Some(sh_H j(S3::S2::S2::r))).
 rewrite repeat_app,<-app_assoc;cbn[repeat app];rewrite csteps_add,sh_pairs,sh_odd_boundary.
 unfold sh_H;replace(S(2*j))with(2*j+1)by lia;reflexivity.
Qed.
Lemma sh_entry : csteps sh_tm 142 c0=Some(sh_main 2 4).
Proof. vm_compute;reflexivity. Qed.
