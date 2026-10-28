(** A finite binary countdown between a fixed 3 boundary and a terminal 1.
    The nonempty bit block is essential: the empty block can escape in B. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census.
Import ListNotations.

Definition br_tm : TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S1 DR StB
 |StA,S2=>mkTrans S0 DL StB |StA,S3=>mkTrans S2 DR StA
 |StB,S0=>mkTrans S1 DR StB |StB,S1=>mkTrans S3 DL StB
 |StB,S2=>mkTrans S2 DL StB |StB,S3=>mkTrans S3 DR StA end).
Definition br_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition br_back q l r:cconf := (q,(ctl l,chd l,r)).
Fixpoint br_bits(ds:list bool):list Sym := match ds with
 |[]=>[]|b::ds=>(if b then S2 else S0)::br_bits ds end.
Fixpoint br_value(ds:list bool):nat := match ds with
 |[]=>0|b::ds=>(if b then 1 else 0)+2*br_value ds end.

Lemma br_repeat_shift : forall (x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma br_bits_app : forall ds es,br_bits(ds++es)=br_bits ds++br_bits es.
Proof. induction ds;intro es;cbn;[reflexivity|now rewrite IHds]. Qed.
Lemma br_bits_repeat : forall b n,br_bits(repeat b n)=repeat(if b then S2 else S0)n.
Proof. intros b n;induction n;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma br_value_decrease : forall n ds,
 br_value(repeat false n++true::ds)=S(br_value(repeat true n++false::ds)).
Proof. induction n;intro ds;cbn[repeat app br_value];[lia|rewrite IHn;lia]. Qed.

Lemma br_left_twos : forall n l r,
 csteps br_tm(n+1)(br_back StB(repeat S2 n++S3::l)r)=
 Some(br_front StA(S3::l)(repeat S2 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(S n+1)with(S(n+1))by lia.
 cbn[repeat app br_back csteps cstep br_tm ctape_move chd ctl].
 change(csteps br_tm(n+1)(br_back StB(repeat S2 n++S3::l)(S2::r))=
 Some(br_front StA(S3::l)(S2::(repeat S2 n++r)))).
 rewrite IHn,br_repeat_shift;reflexivity.
Qed.
Lemma br_left_ones : forall n l r,
 csteps br_tm(n+1)(br_back StB(repeat S1 n++S3::l)r)=
 Some(br_front StA(S3::l)(repeat S3 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(S n+1)with(S(n+1))by lia.
 cbn[repeat app br_back csteps cstep br_tm ctape_move chd ctl].
 change(csteps br_tm(n+1)(br_back StB(repeat S1 n++S3::l)(S3::r))=
 Some(br_front StA(S3::l)(S3::(repeat S3 n++r)))).
 rewrite IHn,br_repeat_shift;reflexivity.
Qed.
Lemma br_right_zeros : forall n l r,
 csteps br_tm n(br_front StB l(repeat S0 n++r))=
 Some(br_front StB(repeat S1 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app br_front csteps cstep br_tm ctape_move chd ctl].
 change(csteps br_tm n(br_front StB(S1::l)(repeat S0 n++r))=
 Some(br_front StB(S1::(repeat S1 n++l))r)).
 rewrite IHn,br_repeat_shift;reflexivity.
Qed.
Lemma br_right_threes : forall n l r,
 csteps br_tm n(br_front StA l(repeat S3 n++r))=
 Some(br_front StA(repeat S2 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app br_front csteps cstep br_tm ctape_move chd ctl].
 change(csteps br_tm n(br_front StA(S2::l)(repeat S3 n++r))=
 Some(br_front StA(S2::(repeat S2 n++l))r)).
 rewrite IHn,br_repeat_shift;reflexivity.
Qed.

Definition br_cost n := match n with 0=>2|S n=>4*S n+6 end.
Theorem br_decrement : forall n l r,
 csteps br_tm(br_cost n)(br_front StA(S3::l)(repeat S0 n++S2::r))=
 Some(br_front StA(S3::l)(repeat S2 n++S0::r)).
Proof.
 intros n l r;destruct n;[reflexivity|].
 unfold br_cost;replace(4*S n+6)with(3+(n+(1+((S n+1)+(S n+(1+(S n+1)))))))by lia.
 rewrite csteps_add.
 change(csteps br_tm(n+(1+((S n+1)+(S n+(1+(S n+1))))))
   (br_front StB(S1::S3::l)(repeat S0 n++S2::r))=
 Some(br_front StA(S3::l)(repeat S2(S n)++S0::r))).
 rewrite csteps_add,br_right_zeros,csteps_add.
 rewrite br_repeat_shift.
 change(csteps br_tm((S n+1)+(S n+(1+(S n+1))))
   (br_back StB(repeat S1(S n)++S3::l)(S2::r))=
 Some(br_front StA(S3::l)(repeat S2(S n)++S0::r))).
 rewrite csteps_add,br_left_ones,csteps_add,br_right_threes,csteps_add.
 change(csteps br_tm(S n+1)(br_back StB(repeat S2(S n)++S3::l)(S0::r))=
 Some(br_front StA(S3::l)(repeat S2(S n)++S0::r))).
 apply br_left_twos.
Qed.
Theorem br_zero_finish : forall n l r,
 csteps br_tm(3*S n+4)(br_front StA(S3::l)(repeat S0(S n)++S1::r))=
 Some(br_front StA(repeat S2(S n)++S3::l)(S3::r)).
Proof.
 intros n l r;replace(3*S n+4)with(3+(n+(1+((S n+1)+S n))))by lia.
 rewrite csteps_add.
 change(csteps br_tm(n+(1+((S n+1)+S n)))
   (br_front StB(S1::S3::l)(repeat S0 n++S1::r))=
 Some(br_front StA(repeat S2(S n)++S3::l)(S3::r))).
 rewrite csteps_add,br_right_zeros,csteps_add,br_repeat_shift.
 change(csteps br_tm((S n+1)+S n)
   (br_back StB(repeat S1(S n)++S3::l)(S3::r))=
 Some(br_front StA(repeat S2(S n)++S3::l)(S3::r))).
 rewrite csteps_add,br_left_ones;apply br_right_threes.
Qed.

Lemma br_decompose : forall ds,
 (exists n,ds=repeat false n) \/
 (exists n tail,ds=repeat false n++true::tail).
Proof.
 induction ds as[|b ds IH].
 - left;exists 0;reflexivity.
 - destruct b.
   + right;exists 0,ds;reflexivity.
   + destruct IH as[(n&E)|(n&tail&E)];subst ds.
     * left;exists(S n);reflexivity.
     * right;exists(S n),tail;reflexivity.
Qed.
Theorem br_drain : forall v ds l r,br_value ds=v ->ds<>[] ->
 exists t,0<t /\ csteps br_tm t(br_front StA(S3::l)(br_bits ds++S1::r))=
 Some(br_front StA(repeat S2(length ds)++S3::l)(S3::r)).
Proof.
 induction v using lt_wf_ind;intros ds l r Hv Hne.
 destruct(br_decompose ds)as[(n&E)|(n&tail&E)];subst ds.
 - destruct n;[contradiction|].
   exists(3*S n+4);split;[lia|].
   rewrite br_bits_repeat,repeat_length;apply br_zero_finish.
 - set(ds':=repeat true n++false::tail).
   assert(Hsmall:br_value ds'<v).
   {unfold ds';rewrite br_value_decrease in Hv;lia. }
   assert(Hne':ds'<>[]). {unfold ds';destruct n;discriminate. }
   destruct(H(br_value ds')Hsmall ds' l r eq_refl Hne')as(t&Ht&Et).
   exists(br_cost n+t);split;[destruct n;cbn[br_cost];lia|].
   rewrite csteps_add.
   rewrite br_bits_app,br_bits_repeat;cbn[br_bits];rewrite <-app_assoc;cbn[app].
   rewrite br_decrement.
   unfold ds' in Et;rewrite br_bits_app,br_bits_repeat in Et;cbn[br_bits]in Et.
   rewrite <-app_assoc in Et;cbn[app]in Et.
   rewrite !app_length,!repeat_length in *;cbn[length]in *;exact Et.
Qed.

Definition br_main n:cconf := (StA,(repeat S2(S n)++[S3;S1],S0,[])).
Theorem br_main_next : forall n,exists t,0<t /\
 csteps br_tm t(br_main n)=Some(br_main(S n)).
Proof.
 intro n.
 assert(Hne:repeat true(S n)<>[])by discriminate.
 destruct(br_drain(br_value(repeat true(S n)))(repeat true(S n))[S1][]eq_refl Hne)as(t&Ht&Et).
 rewrite br_bits_repeat,repeat_length in Et.
 exists(1+((S n+1)+(t+1)));split;[lia|].
 rewrite csteps_add.
 change(csteps br_tm((S n+1)+(t+1))(br_back StB(repeat S2(S n)++[S3;S1])[S1])=
 Some(br_main(S n))).
 rewrite csteps_add,br_left_twos,csteps_add,Et;unfold br_main;reflexivity.
Qed.
Example br_entry : csteps br_tm 7 c0=Some(br_main 0).
Proof. reflexivity. Qed.
Lemma br_returns : forall N,exists t n,N<=t /\ csteps br_tm t c0=Some(br_main n).
Proof.
 induction N as[|N IH].
 - exists 7,0;split;[lia|exact br_entry].
 - destruct IH as(t&n&Ht&E);destruct(br_main_next n)as(j&Hj&E').
   exists(t+j),(S n);split;[lia|];rewrite csteps_add,E;exact E'.
Qed.
Theorem br_nonhalt : NonHalt br_tm.
Proof.
 intros n Hnone;destruct(br_returns n)as(t&d&Ht&E).
 pose proof(csteps_lift br_tm t c0(br_main d)E)as Hrun;rewrite lift_c0 in Hrun.
 destruct(stepn_prefix br_tm n t InitES(lift(br_main d))Ht Hrun)as(c&Ec&_);congruence.
Qed.
Theorem br_A_recurrent : forall N,exists t,N<=t /\ VisitsAt br_tm StA t.
Proof.
 intro N;destruct(br_returns N)as(t&n&Ht&E).
 exists t;split;[exact Ht|];exists(lift(br_main n));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem br_B_recurrent : forall N,exists t,N<=t /\ VisitsAt br_tm StB t.
Proof.
 intro N;destruct(br_returns N)as(t&n&Ht&E).
 exists(t+1);split;[lia|];exists(lift(br_back StB(repeat S2(S n)++[S3;S1])[S1]));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem br_state_zero : QHBound 0 br_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(br_A_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(br_B_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem br_sound : NonHalt br_tm /\ QHBound 0 br_tm.
Proof. split;[exact br_nonhalt|exact br_state_zero]. Qed.
Print Assumptions br_sound.
