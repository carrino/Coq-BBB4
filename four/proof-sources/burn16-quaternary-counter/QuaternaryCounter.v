(** Base-four digits encoded as 10,20,12,22. The boundary head is the digit
    sum modulo three; this excludes the unsafe all-maximal overflow heads. *)
From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement Spec CTape Census.
Import ListNotations.

Definition qc_tm : TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StB
 |StA,S2=>mkTrans S0 DL StB |StA,S3=>mkTrans S0 DR StB
 |StB,S0=>mkTrans S2 DR StB |StB,S1=>mkTrans S2 DR StA
 |StB,S2=>mkTrans S3 DL StB |StB,S3=>mkTrans S1 DR StA end).
Definition qc_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition qc_back q l r:cconf := (q,(ctl l,chd l,r)).
Inductive qc_digit := D0|D1|D2|D3.
Fixpoint qc_enc(ds:list qc_digit) := match ds with
 |[]=>[] |D0::ds=>S1::S0::qc_enc ds |D1::ds=>S2::S0::qc_enc ds
 |D2::ds=>S1::S2::qc_enc ds |D3::ds=>S2::S2::qc_enc ds end.
Definition qc_zeros n := qc_enc(repeat D0 n).
Definition qc_rot h := match h with S0=>S1|S1=>S2|_=>S0 end.
Fixpoint qc_head(ds:list qc_digit) := match ds with
 |[]=>S0 |D1::ds=>qc_rot(qc_head ds)
 |D2::ds=>qc_rot(qc_rot(qc_head ds)) |_::ds=>qc_head ds end.
Definition qc_bump d := match d with D0=>D1|D1=>D2|D2=>D3|D3=>D0 end.
Definition qc_main ds:cconf := (StA,(qc_enc ds,qc_head ds,[])).

Lemma qc_repeat_shift : forall (x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma qc_zeros_shift : forall n l,qc_zeros n++S1::S0::l=S1::S0::(qc_zeros n++l).
Proof.
 induction n;intro l;[reflexivity|].
 change(S1::S0::(qc_zeros n++S1::S0::l)=S1::S0::S1::S0::(qc_zeros n++l)).
 now rewrite IHn.
Qed.
Lemma qc_enc_app : forall ds es,qc_enc(ds++es)=qc_enc ds++qc_enc es.
Proof. induction ds as[|d ds IH];intro es;[reflexivity|destruct d;cbn;now rewrite IH]. Qed.
Lemma qc_enc_max : forall n,qc_enc(repeat D3 n)=repeat S2(2*n).
Proof.
 induction n;[reflexivity|].
 replace(2*S n)with(S(S(2*n)))by lia;cbn[repeat qc_enc];now rewrite IHn.
Qed.
Lemma qc_rot_good : forall h,h=S0 \/ h=S1 \/ h=S2 ->
 qc_rot h=S0 \/ qc_rot h=S1 \/ qc_rot h=S2.
Proof. intros h[H|[H|H]];subst h;cbn[qc_rot];auto. Qed.
Lemma qc_head_good : forall ds,qc_head ds=S0 \/ qc_head ds=S1 \/ qc_head ds=S2.
Proof. induction ds as[|d ds IH];[left;reflexivity|destruct d;cbn[qc_head];auto using qc_rot_good]. Qed.
Lemma qc_rot_three : forall h,h=S0 \/ h=S1 \/ h=S2 ->qc_rot(qc_rot(qc_rot h))=h.
Proof. intros h[H|[H|H]];subst h;reflexivity. Qed.
Lemma qc_head_zero_prefix : forall n ds,qc_head(repeat D0 n++ds)=qc_head ds.
Proof. induction n;intro ds;cbn;auto. Qed.
Lemma qc_head_max_prefix : forall n ds,qc_head(repeat D3 n++ds)=qc_head ds.
Proof. induction n;intro ds;cbn;auto. Qed.
Lemma qc_head_all_max : forall n,qc_head(repeat D3 n)=S0.
Proof. induction n;cbn;auto. Qed.
Lemma qc_head_increment : forall n d ds,d<>D3 ->
 qc_head(repeat D0 n++qc_bump d::ds)=qc_rot(qc_head(repeat D3 n++d::ds)).
Proof.
 intros n d ds Hd;rewrite qc_head_zero_prefix,qc_head_max_prefix.
 destruct d;cbn[qc_bump qc_head];try reflexivity;[symmetry;apply qc_rot_three;apply qc_head_good|contradiction].
Qed.
Lemma qc_head_overflow : forall n,qc_head(D1::(repeat D0 n++[D2]))=S0.
Proof. intro n;cbn[qc_head];rewrite qc_head_zero_prefix;reflexivity. Qed.

Lemma qc_left_twos : forall n l r,
 csteps qc_tm n(qc_back StB(repeat S2 n++l)r)=Some(qc_back StB l(repeat S3 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app qc_back csteps cstep qc_tm ctape_move chd ctl].
 change(csteps qc_tm n(qc_back StB(repeat S2 n++l)(S3::r))=
 Some(qc_back StB l(S3::(repeat S3 n++r)))).
 rewrite IHn,qc_repeat_shift;reflexivity.
Qed.
Lemma qc_right_pairs : forall n l r,
 csteps qc_tm(2*n)(qc_front StA l(repeat S3(2*n)++r))=
 Some(qc_front StA(qc_zeros n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(2*S n)with(2+2*n)by lia;rewrite csteps_add.
 change(csteps qc_tm(2*n)(qc_front StA(S1::S0::l)(repeat S3(2*n)++r))=
 Some(qc_front StA(S1::S0::(qc_zeros n++l))r)).
 rewrite IHn,qc_zeros_shift;reflexivity.
Qed.
Lemma qc_start : forall l r h,h=S0 \/ h=S1 \/ h=S2 ->
 csteps qc_tm 1(StA,(l,h,r))=Some(qc_back StB l(qc_rot h::r)).
Proof. intros l r h[H|[H|H]];subst h;reflexivity. Qed.
Theorem qc_short_increment : forall n x l r h,h=S0 \/ h=S1 \/ h=S2 ->
 csteps qc_tm(4*n+2)(StA,(repeat S2(2*n)++S1::x::l,h,r))=
 Some(StA,(qc_zeros n++S2::x::l,qc_rot h,r)).
Proof.
 intros n x l r h Hh;replace(4*n+2)with(1+(2*n+(1+2*n)))by lia.
 rewrite csteps_add,qc_start by exact Hh.
 rewrite csteps_add,qc_left_twos,csteps_add.
 change(csteps qc_tm(2*n)(qc_front StA(S2::x::l)(repeat S3(2*n)++qc_rot h::r))=
 Some(qc_front StA(qc_zeros n++S2::x::l)(qc_rot h::r))).
 apply qc_right_pairs.
Qed.
Theorem qc_long_increment : forall n l r h,h=S0 \/ h=S1 \/ h=S2 ->
 csteps qc_tm(4*n+4)(StA,(repeat S2(2*n)++S2::S0::l,h,r))=
 Some(StA,(qc_zeros n++S1::S2::l,qc_rot h,r)).
Proof.
 intros n l r h Hh;replace(4*n+4)with(1+(2*n+(3+2*n)))by lia.
 rewrite csteps_add,qc_start by exact Hh.
 rewrite csteps_add,qc_left_twos,csteps_add.
 change(csteps qc_tm(2*n)(qc_front StA(S1::S2::l)(repeat S3(2*n)++qc_rot h::r))=
 Some(qc_front StA(qc_zeros n++S1::S2::l)(qc_rot h::r))).
 apply qc_right_pairs.
Qed.
Theorem qc_overflow : forall n,
 csteps qc_tm(4*S n+3)(StA,(repeat S2(2*S n),S0,[]))=
 Some(StA,(S2::S0::(qc_zeros n++[S1;S2]),S0,[])).
Proof.
 intro n;replace(4*S n+3)with(1+(2*S n+(2+(2*n+2))))by lia.
 rewrite csteps_add,qc_start by auto.
 rewrite <-(app_nil_r(repeat S2(2*S n)))at 1.
 rewrite csteps_add,qc_left_twos,csteps_add.
 assert(E:csteps qc_tm 2(qc_back StB[](repeat S3(2*S n)++[S1]))=
 Some(qc_front StA[S1;S2](repeat S3(2*n)++[S3;S1]))).
 {replace(2*S n)with(S(S(2*n)))by lia.
  cbn[repeat app qc_back qc_front csteps cstep qc_tm ctape_move chd ctl].
  rewrite qc_repeat_shift;reflexivity. }
 cbn[qc_rot];rewrite E,csteps_add,qc_right_pairs;reflexivity.
Qed.

Lemma qc_decompose : forall ds,
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
Theorem qc_main_next : forall ds,ds<>[] ->
 exists k ds',0<k /\ ds'<>[] /\ csteps qc_tm k(qc_main ds)=Some(qc_main ds').
Proof.
 intros ds Hne;destruct(qc_decompose ds)as[(n&E)|(n&d&tail&E&Hd)];subst ds.
 - destruct n;[contradiction|].
   exists(4*S n+3),(D1::(repeat D0 n++[D2]));split;[lia|];split;[discriminate|].
   unfold qc_main;rewrite qc_head_all_max,qc_head_overflow,qc_enc_max.
   cbn[qc_enc];rewrite qc_enc_app;apply qc_overflow.
 - exists(4*n+match d with D1=>4|_=>2 end),(repeat D0 n++qc_bump d::tail).
   split;[destruct d;lia|];split;[destruct n;discriminate|].
   unfold qc_main;rewrite(qc_head_increment n d tail Hd).
   rewrite !qc_enc_app,qc_enc_max;fold(qc_zeros n).
   pose proof(qc_head_good(repeat D3 n++d::tail))as Hhead.
   destruct d;[apply qc_short_increment|apply qc_long_increment|apply qc_short_increment|contradiction];exact Hhead.
Qed.
Example qc_entry : csteps qc_tm 3 c0=Some(qc_main[D3]).
Proof. reflexivity. Qed.
Lemma qc_returns : forall N,exists k ds,N<=k /\ ds<>[] /\ csteps qc_tm k c0=Some(qc_main ds).
Proof.
 induction N as[|N IH].
 - exists 3,[D3];split;[lia|];split;[discriminate|exact qc_entry].
 - destruct IH as(k&ds&Hk&Hne&E).
   destruct(qc_main_next ds Hne)as(j&ds'&Hj&Hne'&E').
   exists(k+j),ds';split;[lia|];split;[exact Hne'|];rewrite csteps_add,E;exact E'.
Qed.
Theorem qc_nonhalt : NonHalt qc_tm.
Proof.
 intros n Hnone;destruct(qc_returns n)as(k&ds&Hk&_&E).
 pose proof(csteps_lift qc_tm k c0(qc_main ds)E)as Hrun;rewrite lift_c0 in Hrun.
 destruct(stepn_prefix qc_tm n k InitES(lift(qc_main ds))Hk Hrun)as(c&Ec&_);congruence.
Qed.
Theorem qc_A_recurrent : forall N,exists k,N<=k /\ VisitsAt qc_tm StA k.
Proof.
 intro N;destruct(qc_returns N)as(k&ds&Hk&_&E).
 exists k;split;[exact Hk|];exists(lift(qc_main ds));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem qc_B_recurrent : forall N,exists k,N<=k /\ VisitsAt qc_tm StB k.
Proof.
 intro N;destruct(qc_returns N)as(k&ds&Hk&_&E).
 exists(k+1);split;[lia|];exists(lift(qc_back StB(qc_enc ds)[qc_rot(qc_head ds)]));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;apply qc_start;apply qc_head_good.
Qed.
Theorem qc_state_zero : QHBound 0 qc_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(qc_A_recurrent(S s))as(k&Hk&Hv);exfalso;apply(Hquiet k);[lia|exact Hv].
 - destruct(qc_B_recurrent(S s))as(k&Hk&Hv);exfalso;apply(Hquiet k);[lia|exact Hv].
Qed.
Theorem qc_sound : NonHalt qc_tm /\ QHBound 0 qc_tm.
Proof. split;[exact qc_nonhalt|exact qc_state_zero]. Qed.
Print Assumptions qc_sound.
