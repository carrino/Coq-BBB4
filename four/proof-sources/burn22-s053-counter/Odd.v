From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement Spec CTape Census.
From BBB24Burn22S053Counter Require Import S053Core.
Import ListNotations.

Lemma so_launch : forall m l r,
 csteps sc_tm(m+3)(sc_front StA(repeat S1(S m)++S3::l)(S3::r))=
 Some(sc_front StA(S1::l)(repeat S3 m++S2::S2::r)).
Proof.
 intros m l r;replace(m+3)with(2+(m+1))by lia;rewrite csteps_add.
 change(csteps sc_tm(m+1)(sc_back StB(repeat S1 m++S3::l)(S2::S2::r))=
 Some(sc_front StA(S1::l)(repeat S3 m++S2::S2::r))).
 rewrite csteps_add,sc_B_left_ones;reflexivity.
Qed.

Lemma so_five_step : forall j r,
 csteps sc_tm(12*j+21)(sc_front StA(repeat S1 5++repeat S3(2*j))(S3::r))=
 Some(sc_front StA(repeat S1 5++repeat S3(2*j+2))r).
Proof.
 intros j r;replace(12*j+21)with(6+(10*j+((2*j+7)+8)))by lia.
 rewrite csteps_add.
 change(csteps sc_tm(10*j+((2*j+7)+8))
 (sc_back StB(repeat S3(2*j))(S3::S3::S3::S3::S2::S2::r))=
 Some(sc_front StA(repeat S1 5++repeat S3(2*j+2))r)).
 rewrite <-(app_nil_r(repeat S3(2*j)))at 1.
 rewrite csteps_add,sc_pairs,csteps_add,sc_blank_C.
 replace(2*j+4)with(S(S(2*j+2)))by lia;reflexivity.
Qed.

Definition so_drain_cost m j:=6*m*m+12*j*m+15*m.
Theorem so_five_iter : forall m j r,
 csteps sc_tm(so_drain_cost m j)
 (sc_front StA(repeat S1 5++repeat S3(2*j))(repeat S3 m++r))=
 Some(sc_front StA(repeat S1 5++repeat S3(2*(j+m)))r).
Proof.
 induction m;intros j r.
 - replace(so_drain_cost 0 j)with 0 by(unfold so_drain_cost;lia).
   rewrite Nat.add_0_r;reflexivity.
 - replace(so_drain_cost(S m)j)with((12*j+21)+so_drain_cost m(S j))
   by(unfold so_drain_cost;nia).
   cbn[repeat app];rewrite csteps_add,so_five_step.
   replace(2*j+2)with(2*S j)by lia;rewrite IHm.
   replace(S j+m)with(j+S m)by lia;reflexivity.
Qed.

Lemma so_small_one : forall r,
 csteps sc_tm 5(sc_front StA[S1;S3;S2](S3::r))=
 Some(sc_front StA[S1;S1;S1;S2]r).
Proof. intro r;reflexivity. Qed.
Lemma so_small_two : forall r,
 csteps sc_tm 13(sc_front StA[S1;S1;S1;S2](S3::r))=
 Some(sc_front StA(repeat S1 5)r).
Proof. intro r;reflexivity. Qed.

Lemma so_prepare : forall n r,
 csteps sc_tm(2*S n+21)
 (sc_front StA(repeat S1(2*S n+1)++[S3;S3;S2])(S3::S3::r))=
 Some(sc_front StA(repeat S1 5)(repeat S3(2*n)++S2::S2::S3::r)).
Proof.
 intros n r;replace(2*S n+21)with((2*S n+3)+(5+13))by lia.
 replace(2*S n+1)with(S(2*S n))by lia.
 rewrite csteps_add,so_launch.
 replace(2*S n)with(S(S(2*n)))by lia;cbn[repeat app].
 rewrite csteps_add,so_small_one,so_small_two;reflexivity.
Qed.

Theorem so_seven_finish : forall j r,
 csteps sc_tm(24*j+46)(sc_front StA(repeat S1 7++repeat S3(2*j))(S3::r))=
 Some(sc_back StB(repeat S3(2*j+8))(S2::S2::r)).
Proof.
 intros j r;replace(24*j+46)with(8+(10*j+((2*j+7)+(12*(j+2)+7))))by lia.
 rewrite csteps_add.
 change(csteps sc_tm(10*j+((2*j+7)+(12*(j+2)+7)))
 (sc_back StB(repeat S3(2*j))(S3::S3::S3::S3::S3::S3::S2::S2::r))=
 Some(sc_back StB(repeat S3(2*j+8))(S2::S2::r))).
 rewrite <-(app_nil_r(repeat S3(2*j)))at 1.
 rewrite csteps_add,sc_pairs,csteps_add,sc_blank_C.
 replace(2*j+4)with(2*(j+2))by lia.
 replace(2*j+8)with(2*(j+2)+4)by lia.
 apply sc_even.
Qed.

Theorem so_odd_normalizer : forall n r,
 csteps sc_tm(24*n*n+32*n+15)
 (sc_front StA(repeat S1(2*n+1)++[S3;S3;S2])(S3::S3::r))=
 Some(sc_back StB(repeat S3(4*n+4))(S2::S2::r)).
Proof.
 intros n r;destruct n as[|n];[reflexivity|].
 replace(24*S n*S n+32*S n+15)with
 ((2*S n+21)+(so_drain_cost(2*n)0+(2+(24*(2*n)+46))))
 by(unfold so_drain_cost;nia).
 rewrite csteps_add,so_prepare,csteps_add.
 change(match csteps sc_tm(so_drain_cost(2*n)0)
 (sc_front StA(repeat S1 5++repeat S3(2*0))(repeat S3(2*n)++S2::S2::S3::r))with
 |Some c=>csteps sc_tm(2+(24*(2*n)+46))c|None=>None end=
 Some(sc_back StB(repeat S3(4*S n+4))(S2::S2::r))).
 rewrite so_five_iter,csteps_add.
 change(csteps sc_tm(24*(2*n)+46)
 (sc_front StA(repeat S1 7++repeat S3(2*(2*n)))(S3::r))=
 Some(sc_back StB(repeat S3(4*S n+4))(S2::S2::r))).
 replace(4*S n+4)with(2*(2*n)+8)by lia;apply so_seven_finish.
Qed.
