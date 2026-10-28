(** Base-four digits encoded as 11,21,12,22. The boundary head is the digit
    sum modulo three; this excludes the unsafe all-maximal overflow heads. *)
From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement Spec CTape Census.
Import ListNotations.

Definition qs_tm : TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StB
 |StA,S2=>mkTrans S0 DL StB |StA,S3=>mkTrans S1 DR StA
 |StB,S0=>mkTrans S2 DR StB |StB,S1=>mkTrans S2 DR StA
 |StB,S2=>mkTrans S3 DL StB |StB,S3=>mkTrans S1 DR StB end).
Definition qs_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition qs_back q l r:cconf := (q,(ctl l,chd l,r)).
Inductive qs_digit := D0|D1|D2|D3.
Fixpoint qs_enc(ds:list qs_digit) := match ds with
 |[]=>[] |D0::ds=>S1::S1::qs_enc ds |D1::ds=>S2::S1::qs_enc ds
 |D2::ds=>S1::S2::qs_enc ds |D3::ds=>S2::S2::qs_enc ds end.
Definition qs_zeros n := qs_enc(repeat D0 n).
Definition qs_rot h := match h with S0=>S1|S1=>S2|_=>S0 end.
Fixpoint qs_head(ds:list qs_digit) := match ds with
 |[]=>S0 |D1::ds=>qs_rot(qs_head ds)
 |D2::ds=>qs_rot(qs_rot(qs_head ds)) |_::ds=>qs_head ds end.
Definition qs_bump d := match d with D0=>D1|D1=>D2|D2=>D3|D3=>D0 end.
Definition qs_main ds:cconf := (StA,(qs_enc ds,qs_head ds,[])).

Lemma qs_repeat_shift : forall (x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma qs_zeros_shift : forall n l,qs_zeros n++S1::S1::l=S1::S1::(qs_zeros n++l).
Proof.
 induction n;intro l;[reflexivity|].
 change(S1::S1::(qs_zeros n++S1::S1::l)=S1::S1::S1::S1::(qs_zeros n++l)).
 now rewrite IHn.
Qed.
Lemma qs_enc_app : forall ds es,qs_enc(ds++es)=qs_enc ds++qs_enc es.
Proof. induction ds as[|d ds IH];intro es;[reflexivity|destruct d;cbn;now rewrite IH]. Qed.
Lemma qs_enc_max : forall n,qs_enc(repeat D3 n)=repeat S2(2*n).
Proof.
 induction n;[reflexivity|].
 replace(2*S n)with(S(S(2*n)))by lia;cbn[repeat qs_enc];now rewrite IHn.
Qed.
Lemma qs_rot_good : forall h,h=S0 \/ h=S1 \/ h=S2 ->
 qs_rot h=S0 \/ qs_rot h=S1 \/ qs_rot h=S2.
Proof. intros h[H|[H|H]];subst h;cbn[qs_rot];auto. Qed.
Lemma qs_head_good : forall ds,qs_head ds=S0 \/ qs_head ds=S1 \/ qs_head ds=S2.
Proof. induction ds as[|d ds IH];[left;reflexivity|destruct d;cbn[qs_head];auto using qs_rot_good]. Qed.
Lemma qs_rot_three : forall h,h=S0 \/ h=S1 \/ h=S2 ->qs_rot(qs_rot(qs_rot h))=h.
Proof. intros h[H|[H|H]];subst h;reflexivity. Qed.
Lemma qs_head_zero_prefix : forall n ds,qs_head(repeat D0 n++ds)=qs_head ds.
Proof. induction n;intro ds;cbn;auto. Qed.
Lemma qs_head_max_prefix : forall n ds,qs_head(repeat D3 n++ds)=qs_head ds.
Proof. induction n;intro ds;cbn;auto. Qed.
Lemma qs_head_all_max : forall n,qs_head(repeat D3 n)=S0.
Proof. induction n;cbn;auto. Qed.
Lemma qs_head_increment : forall n d ds,d<>D3 ->
 qs_head(repeat D0 n++qs_bump d::ds)=qs_rot(qs_head(repeat D3 n++d::ds)).
Proof.
 intros n d ds Hd;rewrite qs_head_zero_prefix,qs_head_max_prefix.
 destruct d;cbn[qs_bump qs_head];try reflexivity;[symmetry;apply qs_rot_three;apply qs_head_good|contradiction].
Qed.
Lemma qs_head_overflow : forall n,qs_head(D1::(repeat D0 n++[D2]))=S0.
Proof. intro n;cbn[qs_head];rewrite qs_head_zero_prefix;reflexivity. Qed.

Lemma qs_left_twos : forall n l r,
 csteps qs_tm n(qs_back StB(repeat S2 n++l)r)=Some(qs_back StB l(repeat S3 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app qs_back csteps cstep qs_tm ctape_move chd ctl].
 change(csteps qs_tm n(qs_back StB(repeat S2 n++l)(S3::r))=
 Some(qs_back StB l(S3::(repeat S3 n++r)))).
 rewrite IHn,qs_repeat_shift;reflexivity.
Qed.
Lemma qs_right_pairs : forall n l r,
 csteps qs_tm(2*n)(qs_front StA l(repeat S3(2*n)++r))=
 Some(qs_front StA(qs_zeros n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(2*S n)with(2+2*n)by lia;rewrite csteps_add.
 change(csteps qs_tm(2*n)(qs_front StA(S1::S1::l)(repeat S3(2*n)++r))=
 Some(qs_front StA(S1::S1::(qs_zeros n++l))r)).
 rewrite IHn,qs_zeros_shift;reflexivity.
Qed.
Lemma qs_start : forall l r h,h=S0 \/ h=S1 \/ h=S2 ->
 csteps qs_tm 1(StA,(l,h,r))=Some(qs_back StB l(qs_rot h::r)).
Proof. intros l r h[H|[H|H]];subst h;reflexivity. Qed.
Theorem qs_short_increment : forall n x l r h,h=S0 \/ h=S1 \/ h=S2 ->
 csteps qs_tm(4*n+2)(StA,(repeat S2(2*n)++S1::x::l,h,r))=
 Some(StA,(qs_zeros n++S2::x::l,qs_rot h,r)).
Proof.
 intros n x l r h Hh;replace(4*n+2)with(1+(2*n+(1+2*n)))by lia.
 rewrite csteps_add,qs_start by exact Hh.
 rewrite csteps_add,qs_left_twos,csteps_add.
 change(csteps qs_tm(2*n)(qs_front StA(S2::x::l)(repeat S3(2*n)++qs_rot h::r))=
 Some(qs_front StA(qs_zeros n++S2::x::l)(qs_rot h::r))).
 apply qs_right_pairs.
Qed.
Theorem qs_long_increment : forall n l r h,h=S0 \/ h=S1 \/ h=S2 ->
 csteps qs_tm(4*n+4)(StA,(repeat S2(2*n)++S2::S1::l,h,r))=
 Some(StA,(qs_zeros n++S1::S2::l,qs_rot h,r)).
Proof.
 intros n l r h Hh;replace(4*n+4)with(1+(2*n+(3+2*n)))by lia.
 rewrite csteps_add,qs_start by exact Hh.
 rewrite csteps_add,qs_left_twos,csteps_add.
 change(csteps qs_tm(2*n)(qs_front StA(S1::S2::l)(repeat S3(2*n)++qs_rot h::r))=
 Some(qs_front StA(qs_zeros n++S1::S2::l)(qs_rot h::r))).
 apply qs_right_pairs.
Qed.
Lemma qs_zeros_ones : forall n,qs_zeros n=repeat S1(2*n).
Proof.
 induction n;[reflexivity|].
 replace(2*S n)with(S(S(2*n)))by lia.
 change(S1::S1::qs_zeros n=S1::S1::repeat S1(2*n));now rewrite IHn.
Qed.
Lemma qs_right_threes : forall n l r,
 csteps qs_tm n(qs_front StB l(repeat S3 n++r))=
 Some(qs_front StB(repeat S1 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app qs_front csteps cstep qs_tm ctape_move chd ctl].
 change(csteps qs_tm n(qs_front StB(S1::l)(repeat S3 n++r))=
 Some(qs_front StB(S1::(repeat S1 n++l))r)).
 rewrite IHn,qs_repeat_shift;reflexivity.
Qed.
Theorem qs_overflow : forall n,
 csteps qs_tm(4*S n+3)(StA,(repeat S2(2*S n),S0,[]))=
 Some(StA,(S2::S1::(qs_zeros n++[S1;S2]),S0,[])).
Proof.
 intro n;replace(4*S n+3)with(1+(2*S n+(1+(2*S n+1))))by lia.
 rewrite csteps_add,qs_start by auto.
 rewrite <-(app_nil_r(repeat S2(2*S n)))at 1.
 rewrite csteps_add,qs_left_twos,csteps_add.
 change(csteps qs_tm(2*S n+1)(qs_front StB[S2](repeat S3(2*S n)++[S1]))=
 Some(StA,(S2::S1::(qs_zeros n++[S1;S2]),S0,[]))).
 rewrite csteps_add,qs_right_threes,qs_zeros_ones.
 replace(2*S n)with(S(S(2*n)))by lia.
 cbn[repeat app qs_front csteps cstep qs_tm ctape_move chd ctl].
 rewrite qs_repeat_shift;reflexivity.
Qed.

Lemma qs_decompose : forall ds,
 (exists n,ds=repeat D3 n) \/
 (exists n d tail,ds=repeat D3 n++d::tail /\ d<>D3).
Proof.
 induction ds as[|d ds IH].
 - left;exists 0;reflexivity.
 - destruct d.
   + right;exists 0,D0,ds;split;[reflexivity|discriminate].
   + right;exists 0,D1,ds;split;[reflexivity|discriminate].
   + right;exists 0,D2,ds;split;[reflexivity|discriminate].
   + destruct IH as[(n&E)|(n&d&tail&E&Hd)];subst ds.
     * left;exists(S n);reflexivity.
     * right;exists(S n),d,tail;split;[reflexivity|exact Hd].
Qed.
Theorem qs_main_next : forall ds,ds<>[] ->
 exists k ds',0<k /\ ds'<>[] /\ csteps qs_tm k(qs_main ds)=Some(qs_main ds').
Proof.
 intros ds Hne;destruct(qs_decompose ds)as[(n&E)|(n&d&tail&E&Hd)];subst ds.
 - destruct n;[contradiction|].
   exists(4*S n+3),(D1::(repeat D0 n++[D2]));split;[lia|];split;[discriminate|].
   unfold qs_main;rewrite qs_head_all_max,qs_head_overflow,qs_enc_max.
   cbn[qs_enc];rewrite qs_enc_app;apply qs_overflow.
 - exists(4*n+match d with D1=>4|_=>2 end),(repeat D0 n++qs_bump d::tail).
   split;[destruct d;lia|];split;[destruct n;discriminate|].
   unfold qs_main;rewrite(qs_head_increment n d tail Hd).
   rewrite !qs_enc_app,qs_enc_max;fold(qs_zeros n).
   pose proof(qs_head_good(repeat D3 n++d::tail))as Hhead.
   destruct d;[apply qs_short_increment|apply qs_long_increment|apply qs_short_increment|contradiction];exact Hhead.
Qed.
Example qs_entry : csteps qs_tm 3 c0=Some(qs_main[D3]).
Proof. reflexivity. Qed.
Lemma qs_returns : forall N,exists k ds,N<=k /\ ds<>[] /\ csteps qs_tm k c0=Some(qs_main ds).
Proof.
 induction N as[|N IH].
 - exists 3,[D3];split;[lia|];split;[discriminate|exact qs_entry].
 - destruct IH as(k&ds&Hk&Hne&E).
   destruct(qs_main_next ds Hne)as(j&ds'&Hj&Hne'&E').
   exists(k+j),ds';split;[lia|];split;[exact Hne'|];rewrite csteps_add,E;exact E'.
Qed.
Theorem qs_nonhalt : NonHalt qs_tm.
Proof.
 intros n Hnone;destruct(qs_returns n)as(k&ds&Hk&_&E).
 pose proof(csteps_lift qs_tm k c0(qs_main ds)E)as Hrun;rewrite lift_c0 in Hrun.
 destruct(stepn_prefix qs_tm n k InitES(lift(qs_main ds))Hk Hrun)as(c&Ec&_);congruence.
Qed.
Theorem qs_A_recurrent : forall N,exists k,N<=k /\ VisitsAt qs_tm StA k.
Proof.
 intro N;destruct(qs_returns N)as(k&ds&Hk&_&E).
 exists k;split;[exact Hk|];exists(lift(qs_main ds));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem qs_B_recurrent : forall N,exists k,N<=k /\ VisitsAt qs_tm StB k.
Proof.
 intro N;destruct(qs_returns N)as(k&ds&Hk&_&E).
 exists(k+1);split;[lia|];exists(lift(qs_back StB(qs_enc ds)[qs_rot(qs_head ds)]));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;apply qs_start;apply qs_head_good.
Qed.
Theorem qs_state_zero : QHBound 0 qs_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(qs_A_recurrent(S s))as(k&Hk&Hv);exfalso;apply(Hquiet k);[lia|exact Hv].
 - destruct(qs_B_recurrent(S s))as(k&Hk&Hv);exfalso;apply(Hquiet k);[lia|exact Hv].
Qed.
Theorem qs_sound : NonHalt qs_tm /\ QHBound 0 qs_tm.
Proof. split;[exact qs_nonhalt|exact qs_state_zero]. Qed.
Print Assumptions qs_sound.
