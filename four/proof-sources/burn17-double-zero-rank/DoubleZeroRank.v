(** A binary countdown with B at a two-zero boundary. The bit-value lemmas
    are reused from BinaryRank; every machine-specific run is proved here. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census.
From BBB24Burn17BinaryRank Require Import BinaryRank.
Import ListNotations.

Definition dr_tm : TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S0 DR StA
 |StA,S2=>mkTrans S0 DL StB |StA,S3=>mkTrans S2 DR StA
 |StB,S0=>mkTrans S1 DR StB |StB,S1=>mkTrans S3 DL StB
 |StB,S2=>mkTrans S2 DL StB |StB,S3=>mkTrans S1 DL StA end).
Definition dr_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition dr_back q l r:cconf := (q,(ctl l,chd l,r)).
Definition dr_config l r := dr_back StB(S0::S0::l)r.

Lemma dr_left_twos : forall n l r,
 csteps dr_tm n(dr_back StB(repeat S2 n++l)r)=
 Some(dr_back StB l(repeat S2 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app dr_back csteps cstep dr_tm ctape_move chd ctl].
 change(csteps dr_tm n(dr_back StB(repeat S2 n++l)(S2::r))=
 Some(dr_back StB l(S2::(repeat S2 n++r)))).
 rewrite IHn,br_repeat_shift;reflexivity.
Qed.
Lemma dr_left_ones : forall n l r,
 csteps dr_tm n(dr_back StB(repeat S1 n++l)r)=
 Some(dr_back StB l(repeat S3 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app dr_back csteps cstep dr_tm ctape_move chd ctl].
 change(csteps dr_tm n(dr_back StB(repeat S1 n++l)(S3::r))=
 Some(dr_back StB l(S3::(repeat S3 n++r)))).
 rewrite IHn,br_repeat_shift;reflexivity.
Qed.
Lemma dr_right_zeros : forall n l r,
 csteps dr_tm n(dr_front StB l(repeat S0 n++r))=
 Some(dr_front StB(repeat S1 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app dr_front csteps cstep dr_tm ctape_move chd ctl].
 change(csteps dr_tm n(dr_front StB(S1::l)(repeat S0 n++r))=
 Some(dr_front StB(S1::(repeat S1 n++l))r)).
 rewrite IHn,br_repeat_shift;reflexivity.
Qed.
Lemma dr_right_threes : forall n l r,
 csteps dr_tm n(dr_front StA l(repeat S3 n++r))=
 Some(dr_front StA(repeat S2 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app dr_front csteps cstep dr_tm ctape_move chd ctl].
 change(csteps dr_tm n(dr_front StA(S2::l)(repeat S3 n++r))=
 Some(dr_front StA(S2::(repeat S2 n++l))r)).
 rewrite IHn,br_repeat_shift;reflexivity.
Qed.
Lemma dr_boundary : forall l r,
 csteps dr_tm 4(dr_back StB(S0::l)(S3::r))=
 Some(dr_front StA(S0::S0::l)r).
Proof. intros l r;reflexivity. Qed.

Theorem dr_decrement : forall n l r,
 csteps dr_tm(4*n+8)(dr_config l(repeat S0 n++S2::r))=
 Some(dr_config l(repeat S2 n++S0::r)).
Proof.
 intros n l r;replace(4*n+8)with(1+(n+(1+(S n+(4+(n+(1+n)))))))by lia.
 rewrite csteps_add.
 change(csteps dr_tm(n+(1+(S n+(4+(n+(1+n))))))
   (dr_front StB(S1::S0::l)(repeat S0 n++S2::r))=
 Some(dr_config l(repeat S2 n++S0::r))).
 rewrite csteps_add,dr_right_zeros,csteps_add,br_repeat_shift.
 change(csteps dr_tm(S n+(4+(n+(1+n))))
   (dr_back StB(repeat S1(S n)++S0::l)(S2::r))=
 Some(dr_config l(repeat S2 n++S0::r))).
 rewrite csteps_add,dr_left_ones,csteps_add.
 change(match csteps dr_tm 4(dr_back StB(S0::l)(S3::(repeat S3 n++S2::r)))with
 |Some c=>csteps dr_tm(n+(1+n))c|None=>None end=Some(dr_config l(repeat S2 n++S0::r))).
 rewrite dr_boundary,csteps_add,dr_right_threes,csteps_add.
 change(csteps dr_tm n(dr_back StB(repeat S2 n++S0::S0::l)(S0::r))=
 Some(dr_back StB(S0::S0::l)(repeat S2 n++S0::r))).
 apply dr_left_twos.
Qed.
Theorem dr_zero_finish : forall n l r,
 csteps dr_tm(3*n+7)(dr_config l(repeat S0 n++S1::r))=
 Some(dr_front StA(repeat S2 n++S0::S0::l)(S3::r)).
Proof.
 intros n l r;replace(3*n+7)with(1+(n+(1+(S n+(4+n)))))by lia.
 rewrite csteps_add.
 change(csteps dr_tm(n+(1+(S n+(4+n))))
   (dr_front StB(S1::S0::l)(repeat S0 n++S1::r))=
 Some(dr_front StA(repeat S2 n++S0::S0::l)(S3::r))).
 rewrite csteps_add,dr_right_zeros,csteps_add,br_repeat_shift.
 change(csteps dr_tm(S n+(4+n))
   (dr_back StB(repeat S1(S n)++S0::l)(S3::r))=
 Some(dr_front StA(repeat S2 n++S0::S0::l)(S3::r))).
 rewrite csteps_add,dr_left_ones,csteps_add.
 change(match csteps dr_tm 4(dr_back StB(S0::l)(S3::(repeat S3 n++S3::r)))with
 |Some c=>csteps dr_tm n c|None=>None end=
 Some(dr_front StA(repeat S2 n++S0::S0::l)(S3::r))).
 rewrite dr_boundary;apply dr_right_threes.
Qed.

Theorem dr_drain : forall v ds l r,br_value ds=v ->
 exists t,0<t /\ csteps dr_tm t(dr_config l(br_bits ds++S1::r))=
 Some(dr_front StA(repeat S2(length ds)++S0::S0::l)(S3::r)).
Proof.
 induction v using lt_wf_ind;intros ds l r Hv.
 destruct(br_decompose ds)as[(n&E)|(n&tail&E)];subst ds.
 - exists(3*n+7);split;[lia|].
   rewrite br_bits_repeat,repeat_length;apply dr_zero_finish.
 - set(ds':=repeat true n++false::tail).
   assert(Hsmall:br_value ds'<v).
   {unfold ds';rewrite br_value_decrease in Hv;lia. }
   destruct(H(br_value ds')Hsmall ds' l r eq_refl)as(t&Ht&Et).
   exists(4*n+8+t);split;[lia|];rewrite csteps_add.
   rewrite br_bits_app,br_bits_repeat;cbn[br_bits];rewrite <-app_assoc;cbn[app].
   rewrite dr_decrement.
   unfold ds' in Et;rewrite br_bits_app,br_bits_repeat in Et;cbn[br_bits]in Et.
   rewrite <-app_assoc in Et;cbn[app]in Et.
   rewrite !app_length,!repeat_length in *;cbn[length]in *;exact Et.
Qed.

Definition dr_main n:cconf := (StA,(repeat S2(S n)++[S0;S0],S0,[])).
Theorem dr_main_next : forall n,exists t,0<t /\
 csteps dr_tm t(dr_main n)=Some(dr_main(S n)).
Proof.
 intro n.
 destruct(dr_drain(br_value(repeat true(S n)))(repeat true(S n))[][]eq_refl)as(t&Ht&Et).
 rewrite br_bits_repeat,repeat_length in Et.
 exists(1+(S n+(t+1)));split;[lia|];rewrite csteps_add.
 change(csteps dr_tm(S n+(t+1))(dr_back StB(repeat S2(S n)++[S0;S0])[S1])=
 Some(dr_main(S n))).
 rewrite csteps_add,dr_left_twos,csteps_add.
 fold(dr_config[](repeat S2(S n)++[S1]));rewrite Et;unfold dr_main;reflexivity.
Qed.
Example dr_entry : csteps dr_tm 9 c0=Some(dr_main 0).
Proof. reflexivity. Qed.
Lemma dr_returns : forall N,exists t n,N<=t /\ csteps dr_tm t c0=Some(dr_main n).
Proof.
 induction N as[|N IH].
 - exists 9,0;split;[lia|exact dr_entry].
 - destruct IH as(t&n&Ht&E);destruct(dr_main_next n)as(j&Hj&E').
   exists(t+j),(S n);split;[lia|];rewrite csteps_add,E;exact E'.
Qed.
Theorem dr_nonhalt : NonHalt dr_tm.
Proof.
 intros n Hnone;destruct(dr_returns n)as(t&d&Ht&E).
 pose proof(csteps_lift dr_tm t c0(dr_main d)E)as Hrun;rewrite lift_c0 in Hrun.
 destruct(stepn_prefix dr_tm n t InitES(lift(dr_main d))Ht Hrun)as(c&Ec&_);congruence.
Qed.
Theorem dr_A_recurrent : forall N,exists t,N<=t /\ VisitsAt dr_tm StA t.
Proof.
 intro N;destruct(dr_returns N)as(t&n&Ht&E).
 exists t;split;[exact Ht|];exists(lift(dr_main n));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem dr_B_recurrent : forall N,exists t,N<=t /\ VisitsAt dr_tm StB t.
Proof.
 intro N;destruct(dr_returns N)as(t&n&Ht&E).
 exists(t+1);split;[lia|];exists(lift(dr_back StB(repeat S2(S n)++[S0;S0])[S1]));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem dr_state_zero : QHBound 0 dr_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(dr_A_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(dr_B_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem dr_sound : NonHalt dr_tm /\ QHBound 0 dr_tm.
Proof. split;[exact dr_nonhalt|exact dr_state_zero]. Qed.
Print Assumptions dr_sound.
