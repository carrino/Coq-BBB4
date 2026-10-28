(** The frozen S009 sibling in equal pairs: false=11 and true=33. Every selected return
    is A on blank with nearest-first left word 3 enc(bits) 3. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census OneStateReach.
Import ListNotations.
Definition rs_tm:TM:=fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S0 DL StB
 |StA,S2=>mkTrans S1 DL StA |StA,S3=>mkTrans S3 DR StB
 |StB,S0=>mkTrans S3 DR StB |StB,S1=>mkTrans S3 DR StA
 |StB,S2=>mkTrans S1 DR StB |StB,S3=>mkTrans S2 DL StB end).
Definition rs_front q l r:cconf:=(q,(l,chd r,ctl r)).
Definition rs_back q l r:cconf:=(q,(ctl l,chd l,r)).
Fixpoint rs_enc(ds:list bool):list Sym:=match ds with
 |[]=>[]|b::ds=>(if b then S3 else S1)::(if b then S3 else S1)::rs_enc ds end.
Definition rs_main ds r:cconf:=(StA,(S3::(rs_enc ds++[S3]),S0,r)).
Lemma rs_repeat_shift : forall (x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma rs_enc_app : forall ds es,rs_enc(ds++es)=rs_enc ds++rs_enc es.
Proof. induction ds as[|b ds IH];intro es;cbn;[reflexivity|now rewrite IH]. Qed.
Lemma rs_enc_repeat : forall b n,rs_enc(repeat b n)=repeat(if b then S3 else S1)(2*n).
Proof.
 intros b n;induction n;[reflexivity|].
 replace(2*S n)with(S(S(2*n)))by lia;cbn[repeat rs_enc];rewrite IHn;reflexivity.
Qed.
Lemma rs_left_threes : forall n l r,
 csteps rs_tm n(rs_back StB(repeat S3 n++l)r)=Some(rs_back StB l(repeat S2 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app rs_back csteps cstep rs_tm ctape_move chd ctl].
 change(csteps rs_tm n(rs_back StB(repeat S3 n++l)(S2::r))=
 Some(rs_back StB l(S2::(repeat S2 n++r)))).
 rewrite IHn,rs_repeat_shift;reflexivity.
Qed.
Lemma rs_right_B_twos : forall n l r,
 csteps rs_tm n(rs_front StB l(repeat S2 n++r))=Some(rs_front StB(repeat S1 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app rs_front csteps cstep rs_tm ctape_move chd ctl].
 change(csteps rs_tm n(rs_front StB(S1::l)(repeat S2 n++r))=
 Some(rs_front StB(S1::(repeat S1 n++l))r)).
 rewrite IHn,rs_repeat_shift;reflexivity.
Qed.
Lemma rs_right_A_twos : forall n l r,
 csteps rs_tm(3*n)(rs_front StA(S3::l)(repeat S2 n++r))=
 Some(rs_front StA(repeat S3 n++S3::l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(3*S n)with(3+3*n)by lia;rewrite csteps_add.
 change(csteps rs_tm(3*n)(rs_front StA(S3::S3::l)(repeat S2 n++r))=
 Some(rs_front StA(S3::(repeat S3 n++S3::l))r)).
 rewrite IHn,rs_repeat_shift;reflexivity.
Qed.
Lemma rs_phase_zero : forall n l r,
 csteps rs_tm(n+2)(StA,(repeat S3 n++S1::l,S0,r))=
 Some(rs_front StA(S3::l)(repeat S2 n++S1::r)).
Proof.
 intros n l r;replace(n+2)with(1+(n+1))by lia;rewrite csteps_add.
 change(csteps rs_tm(n+1)(rs_back StB(repeat S3 n++S1::l)(S1::r))=
 Some(rs_front StA(S3::l)(repeat S2 n++S1::r))).
 rewrite csteps_add,rs_left_threes;reflexivity.
Qed.
Lemma rs_phase_one : forall n l r,
 csteps rs_tm(n+2)(StA,(repeat S3 n++S1::l,S1,r))=
 Some(rs_front StA(S3::l)(repeat S2 n++S0::r)).
Proof.
 intros n l r;replace(n+2)with(1+(n+1))by lia;rewrite csteps_add.
 change(csteps rs_tm(n+1)(rs_back StB(repeat S3 n++S1::l)(S0::r))=
 Some(rs_front StA(S3::l)(repeat S2 n++S0::r))).
 rewrite csteps_add,rs_left_threes;reflexivity.
Qed.
Theorem rs_set_false_run : forall n l r,
 csteps rs_tm(8*n+8)(StA,(repeat S3 n++S1::S1::l,S0,r))=
 Some(StA,(repeat S3(n+2)++l,S0,r)).
Proof.
 intros n l r;replace(8*n+8)with((n+2)+(3*n+((S n+2)+3*S n)))by lia.
 rewrite csteps_add,rs_phase_zero,csteps_add,rs_right_A_twos.
 rewrite rs_repeat_shift.
 change(csteps rs_tm((S n+2)+3*S n)(StA,(repeat S3(S n)++S1::l,S1,r))=
 Some(StA,(repeat S3(n+2)++l,S0,r))).
 rewrite csteps_add,rs_phase_one,rs_right_A_twos.
 replace(n+2)with(S(S n))by lia;rewrite rs_repeat_shift;reflexivity.
Qed.
Lemma rs_all_true_run : forall n r,
 csteps rs_tm(2*n+3)(StA,(repeat S3 n,S0,r))=
 Some(rs_front StA(S3::(repeat S1 n++[S3]))r).
Proof.
 intros n r;replace(2*n+3)with(1+(n+(1+(n+1))))by lia;rewrite csteps_add.
 change(csteps rs_tm(n+(1+(n+1)))(rs_back StB(repeat S3 n)(S1::r))=
 Some(rs_front StA(S3::(repeat S1 n++[S3]))r)).
 rewrite <-(app_nil_r(repeat S3 n))at 1.
 rewrite csteps_add,rs_left_threes,csteps_add.
 change(csteps rs_tm(n+1)(rs_front StB[S3](repeat S2 n++S1::r))=
 Some(rs_front StA(S3::(repeat S1 n++[S3]))r)).
 rewrite csteps_add,rs_right_B_twos;reflexivity.
Qed.
Lemma rs_blank_head : forall r,all_blank r=true ->chd r=S0.
Proof. intros[|h r]H;[reflexivity|];cbn[all_blank]in H;apply andb_prop in H as[H _];apply sym_eqb_spec;exact H. Qed.
Lemma rs_blank_tail : forall r,all_blank r=true ->all_blank(ctl r)=true.
Proof. intros[|h r]H;[reflexivity|];cbn[all_blank]in H;apply andb_prop in H;tauto. Qed.
Theorem rs_set_false : forall n ds r,
 csteps rs_tm(16*n+16)(rs_main(repeat true n++false::ds)r)=
 Some(rs_main(repeat true n++true::ds)r).
Proof.
 intros n ds r;unfold rs_main;rewrite !rs_enc_app,!rs_enc_repeat.
 cbn[rs_enc];repeat rewrite <-app_assoc;cbn[app].
 replace(16*n+16)with(8*(S(2*n))+8)by lia.
 change(csteps rs_tm(8*S(2*n)+8)(StA,(repeat S3(S(2*n))++S1::S1::(rs_enc ds++[S3]),S0,r))=
 Some(StA,(repeat S3(S(2*n))++S3::S3::(rs_enc ds++[S3]),S0,r))).
 rewrite rs_set_false_run.
 replace(S(2*n)+2)with(S(S(S(2*n))))by lia;rewrite !rs_repeat_shift;reflexivity.
Qed.
Theorem rs_overflow : forall n r,all_blank r=true ->
 csteps rs_tm(4*n+7)(rs_main(repeat true n)r)=Some(rs_main(repeat false(S n))(ctl r)).
Proof.
 intros n r Hr;unfold rs_main;rewrite !rs_enc_repeat.
 replace(2*S n)with(S(S(2*n)))by lia.
 rewrite rs_repeat_shift,app_nil_r.
 replace(4*n+7)with(2*(2*n+2)+3)by lia.
 replace(2*n+2)with(S(S(2*n)))by lia.
 change(csteps rs_tm(2*S(S(2*n))+3)(StA,(repeat S3(S(S(2*n))),S0,r))=
 Some(StA,(S3::(repeat S1(S(S(2*n)))++[S3]),S0,ctl r))).
 rewrite rs_all_true_run;unfold rs_front;rewrite(rs_blank_head r Hr).
 reflexivity.
Qed.
Lemma rs_decompose : forall ds,
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
Theorem rs_main_next : forall ds r,all_blank r=true ->
 exists t ds' r',0<t /\csteps rs_tm t(rs_main ds r)=Some(rs_main ds' r') /\all_blank r'=true.
Proof.
 intros ds r Hr;destruct(rs_decompose ds)as[(n&E)|(n&tail&E)];subst ds.
 - exists(4*n+7),(repeat false(S n)),(ctl r);split;[lia|];split.
   + apply rs_overflow;exact Hr.
   + apply rs_blank_tail;exact Hr.
 - exists(16*n+16),(repeat true n++true::tail),r;split;[lia|];split;[apply rs_set_false|exact Hr].
Qed.
Example rs_entry : csteps rs_tm 3 c0=Some(rs_main[][]).
Proof. reflexivity. Qed.
Lemma rs_returns : forall N,exists t ds r,N<=t /\csteps rs_tm t c0=Some(rs_main ds r) /\all_blank r=true.
Proof.
 induction N as[|N IH].
 - exists 3,[],[];split;[lia|];split;[exact rs_entry|reflexivity].
 - destruct IH as(t&ds&r&Ht&E&Hr).
   destruct(rs_main_next ds r Hr)as(j&ds'&r'&Hj&E'&Hr').
   exists(t+j),ds',r';split;[lia|];split;[rewrite csteps_add,E;exact E'|exact Hr'].
Qed.
Theorem rs_nonhalt : NonHalt rs_tm.
Proof. apply ore_total_nonhalt;intros q h;destruct q,h;eexists;reflexivity. Qed.
Theorem rs_A_recurrent : forall N,exists t,N<=t /\VisitsAt rs_tm StA t.
Proof.
 intro N;destruct(rs_returns N)as(t&ds&r&Ht&E&Hr).
 exists t;split;[exact Ht|];exists(lift(rs_main ds r));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem rs_B_recurrent : forall N,exists t,N<=t /\VisitsAt rs_tm StB t.
Proof.
 intro N;destruct(rs_returns N)as(t&ds&r&Ht&E&Hr).
 exists(t+1);split;[lia|];exists(lift(rs_back StB(S3::(rs_enc ds++[S3]))(S1::r)));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem rs_state_zero : QHBound 0 rs_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(rs_A_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(rs_B_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem rs_sound : NonHalt rs_tm /\QHBound 0 rs_tm.
Proof. split;[exact rs_nonhalt|exact rs_state_zero]. Qed.
Print Assumptions rs_sound.
