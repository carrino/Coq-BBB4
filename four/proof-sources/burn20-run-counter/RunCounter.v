(** A counter in equal pairs: false=11 and true=33. Every selected return
    is A on blank with nearest-first left word 3 enc(bits) 3. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census OneStateReach.
Import ListNotations.
Definition rc_tm:TM:=fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S0 DL StB
 |StA,S2=>mkTrans S0 DL StA |StA,S3=>mkTrans S0 DR StA
 |StB,S0=>mkTrans S3 DR StB |StB,S1=>mkTrans S3 DR StA
 |StB,S2=>mkTrans S1 DR StB |StB,S3=>mkTrans S2 DL StB end).
Definition rc_front q l r:cconf:=(q,(l,chd r,ctl r)).
Definition rc_back q l r:cconf:=(q,(ctl l,chd l,r)).
Fixpoint rc_enc(ds:list bool):list Sym:=match ds with
 |[]=>[]|b::ds=>(if b then S3 else S1)::(if b then S3 else S1)::rc_enc ds end.
Definition rc_main ds r:cconf:=(StA,(S3::(rc_enc ds++[S3]),S0,r)).
Lemma rc_repeat_shift : forall (x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma rc_enc_app : forall ds es,rc_enc(ds++es)=rc_enc ds++rc_enc es.
Proof. induction ds as[|b ds IH];intro es;cbn;[reflexivity|now rewrite IH]. Qed.
Lemma rc_enc_repeat : forall b n,rc_enc(repeat b n)=repeat(if b then S3 else S1)(2*n).
Proof.
 intros b n;induction n;[reflexivity|].
 replace(2*S n)with(S(S(2*n)))by lia;cbn[repeat rc_enc];rewrite IHn;reflexivity.
Qed.
Lemma rc_left_threes : forall n l r,
 csteps rc_tm n(rc_back StB(repeat S3 n++l)r)=Some(rc_back StB l(repeat S2 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app rc_back csteps cstep rc_tm ctape_move chd ctl].
 change(csteps rc_tm n(rc_back StB(repeat S3 n++l)(S2::r))=
 Some(rc_back StB l(S2::(repeat S2 n++r)))).
 rewrite IHn,rc_repeat_shift;reflexivity.
Qed.
Lemma rc_right_B_twos : forall n l r,
 csteps rc_tm n(rc_front StB l(repeat S2 n++r))=Some(rc_front StB(repeat S1 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app rc_front csteps cstep rc_tm ctape_move chd ctl].
 change(csteps rc_tm n(rc_front StB(S1::l)(repeat S2 n++r))=
 Some(rc_front StB(S1::(repeat S1 n++l))r)).
 rewrite IHn,rc_repeat_shift;reflexivity.
Qed.
Lemma rc_right_A_twos : forall n l r,
 csteps rc_tm(5*n)(rc_front StA(S3::l)(repeat S2 n++r))=
 Some(rc_front StA(repeat S3 n++S3::l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(5*S n)with(5+5*n)by lia;rewrite csteps_add.
 change(csteps rc_tm(5*n)(rc_front StA(S3::S3::l)(repeat S2 n++r))=
 Some(rc_front StA(S3::(repeat S3 n++S3::l))r)).
 rewrite IHn,rc_repeat_shift;reflexivity.
Qed.
Lemma rc_phase_zero : forall n l r,
 csteps rc_tm(n+2)(StA,(repeat S3 n++S1::l,S0,r))=
 Some(rc_front StA(S3::l)(repeat S2 n++S1::r)).
Proof.
 intros n l r;replace(n+2)with(1+(n+1))by lia;rewrite csteps_add.
 change(csteps rc_tm(n+1)(rc_back StB(repeat S3 n++S1::l)(S1::r))=
 Some(rc_front StA(S3::l)(repeat S2 n++S1::r))).
 rewrite csteps_add,rc_left_threes;reflexivity.
Qed.
Lemma rc_phase_one : forall n l r,
 csteps rc_tm(n+2)(StA,(repeat S3 n++S1::l,S1,r))=
 Some(rc_front StA(S3::l)(repeat S2 n++S0::r)).
Proof.
 intros n l r;replace(n+2)with(1+(n+1))by lia;rewrite csteps_add.
 change(csteps rc_tm(n+1)(rc_back StB(repeat S3 n++S1::l)(S0::r))=
 Some(rc_front StA(S3::l)(repeat S2 n++S0::r))).
 rewrite csteps_add,rc_left_threes;reflexivity.
Qed.
Theorem rc_set_false_run : forall n l r,
 csteps rc_tm(12*n+10)(StA,(repeat S3 n++S1::S1::l,S0,r))=
 Some(StA,(repeat S3(n+2)++l,S0,r)).
Proof.
 intros n l r;replace(12*n+10)with((n+2)+(5*n+((S n+2)+5*S n)))by lia.
 rewrite csteps_add,rc_phase_zero,csteps_add,rc_right_A_twos.
 rewrite rc_repeat_shift.
 change(csteps rc_tm((S n+2)+5*S n)(StA,(repeat S3(S n)++S1::l,S1,r))=
 Some(StA,(repeat S3(n+2)++l,S0,r))).
 rewrite csteps_add,rc_phase_one,rc_right_A_twos.
 replace(n+2)with(S(S n))by lia;rewrite rc_repeat_shift;reflexivity.
Qed.
Lemma rc_all_true_run : forall n r,
 csteps rc_tm(2*n+3)(StA,(repeat S3 n,S0,r))=
 Some(rc_front StA(S3::(repeat S1 n++[S3]))r).
Proof.
 intros n r;replace(2*n+3)with(1+(n+(1+(n+1))))by lia;rewrite csteps_add.
 change(csteps rc_tm(n+(1+(n+1)))(rc_back StB(repeat S3 n)(S1::r))=
 Some(rc_front StA(S3::(repeat S1 n++[S3]))r)).
 rewrite <-(app_nil_r(repeat S3 n))at 1.
 rewrite csteps_add,rc_left_threes,csteps_add.
 change(csteps rc_tm(n+1)(rc_front StB[S3](repeat S2 n++S1::r))=
 Some(rc_front StA(S3::(repeat S1 n++[S3]))r)).
 rewrite csteps_add,rc_right_B_twos;reflexivity.
Qed.
Lemma rc_blank_head : forall r,all_blank r=true ->chd r=S0.
Proof. intros[|h r]H;[reflexivity|];cbn[all_blank]in H;apply andb_prop in H as[H _];apply sym_eqb_spec;exact H. Qed.
Lemma rc_blank_tail : forall r,all_blank r=true ->all_blank(ctl r)=true.
Proof. intros[|h r]H;[reflexivity|];cbn[all_blank]in H;apply andb_prop in H;tauto. Qed.
Theorem rc_set_false : forall n ds r,
 csteps rc_tm(24*n+22)(rc_main(repeat true n++false::ds)r)=
 Some(rc_main(repeat true n++true::ds)r).
Proof.
 intros n ds r;unfold rc_main;rewrite !rc_enc_app,!rc_enc_repeat.
 cbn[rc_enc];repeat rewrite <-app_assoc;cbn[app].
 replace(24*n+22)with(12*(S(2*n))+10)by lia.
 change(csteps rc_tm(12*S(2*n)+10)(StA,(repeat S3(S(2*n))++S1::S1::(rc_enc ds++[S3]),S0,r))=
 Some(StA,(repeat S3(S(2*n))++S3::S3::(rc_enc ds++[S3]),S0,r))).
 rewrite rc_set_false_run.
 replace(S(2*n)+2)with(S(S(S(2*n))))by lia;rewrite !rc_repeat_shift;reflexivity.
Qed.
Theorem rc_overflow : forall n r,all_blank r=true ->
 csteps rc_tm(4*n+7)(rc_main(repeat true n)r)=Some(rc_main(repeat false(S n))(ctl r)).
Proof.
 intros n r Hr;unfold rc_main;rewrite !rc_enc_repeat.
 replace(2*S n)with(S(S(2*n)))by lia.
 rewrite rc_repeat_shift,app_nil_r.
 replace(4*n+7)with(2*(2*n+2)+3)by lia.
 replace(2*n+2)with(S(S(2*n)))by lia.
 change(csteps rc_tm(2*S(S(2*n))+3)(StA,(repeat S3(S(S(2*n))),S0,r))=
 Some(StA,(S3::(repeat S1(S(S(2*n)))++[S3]),S0,ctl r))).
 rewrite rc_all_true_run;unfold rc_front;rewrite(rc_blank_head r Hr).
 reflexivity.
Qed.
Lemma rc_decompose : forall ds,
 (exists n,ds=repeat true n) \/(exists n tail,ds=repeat true n++false::tail).
Proof.
 induction ds as[|b ds IH].
 - left;exists 0;reflexivity.
 - destruct b.
   + destruct IH as[(n&E)|(n&tail&E)];subst ds.
     * left;exists(S n);reflexivity.
     * right;exists(S n),tail;reflexivity.
   + right;exists 0,ds;reflexivity.
Qed.
Theorem rc_main_next : forall ds r,all_blank r=true ->
 exists t ds' r',0<t /\csteps rc_tm t(rc_main ds r)=Some(rc_main ds' r') /\all_blank r'=true.
Proof.
 intros ds r Hr;destruct(rc_decompose ds)as[(n&E)|(n&tail&E)];subst ds.
 - exists(4*n+7),(repeat false(S n)),(ctl r);split;[lia|];split.
   + apply rc_overflow;exact Hr.
   + apply rc_blank_tail;exact Hr.
 - exists(24*n+22),(repeat true n++true::tail),r;split;[lia|];split;[apply rc_set_false|exact Hr].
Qed.
Example rc_entry : csteps rc_tm 3 c0=Some(rc_main[][]).
Proof. reflexivity. Qed.
Lemma rc_returns : forall N,exists t ds r,N<=t /\csteps rc_tm t c0=Some(rc_main ds r) /\all_blank r=true.
Proof.
 induction N as[|N IH].
 - exists 3,[],[];split;[lia|];split;[exact rc_entry|reflexivity].
 - destruct IH as(t&ds&r&Ht&E&Hr).
   destruct(rc_main_next ds r Hr)as(j&ds'&r'&Hj&E'&Hr').
   exists(t+j),ds',r';split;[lia|];split;[rewrite csteps_add,E;exact E'|exact Hr'].
Qed.
Theorem rc_nonhalt : NonHalt rc_tm.
Proof. apply ore_total_nonhalt;intros q h;destruct q,h;eexists;reflexivity. Qed.
Theorem rc_A_recurrent : forall N,exists t,N<=t /\VisitsAt rc_tm StA t.
Proof.
 intro N;destruct(rc_returns N)as(t&ds&r&Ht&E&Hr).
 exists t;split;[exact Ht|];exists(lift(rc_main ds r));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem rc_B_recurrent : forall N,exists t,N<=t /\VisitsAt rc_tm StB t.
Proof.
 intro N;destruct(rc_returns N)as(t&ds&r&Ht&E&Hr).
 exists(t+1);split;[lia|];exists(lift(rc_back StB(S3::(rc_enc ds++[S3]))(S1::r)));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem rc_state_zero : QHBound 0 rc_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(rc_A_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(rc_B_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem rc_sound : NonHalt rc_tm /\QHBound 0 rc_tm.
Proof. split;[exact rc_nonhalt|exact rc_state_zero]. Qed.
Print Assumptions rc_sound.
