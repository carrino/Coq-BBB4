(** Binary pairs20/22 carry the value; the boundary head is its residue
    modulo three. B1 introduces a finite auxiliary binary count-up,
    proved terminating by a decreasing complement value. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census.
Import ListNotations.
Definition s44_tm : TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StB
 |StA,S2=>mkTrans S0 DL StB |StA,S3=>mkTrans S0 DR StB
 |StB,S0=>mkTrans S2 DR StB |StB,S1=>mkTrans S1 DL StB
 |StB,S2=>mkTrans S3 DL StB |StB,S3=>mkTrans S2 DR StA end).
Definition s44_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition s44_back q l r:cconf := (q,(ctl l,chd l,r)).
Definition s44_rot h := match h with S0=>S1|S1=>S2|_=>S0 end.
Definition s44_of_nat n := match n mod 3 with 0=>S0|1=>S1|_=>S2 end.
Fixpoint s44_value(ds:list bool):nat := match ds with
 |[]=>0|b::ds=>(if b then 1 else 0)+2*s44_value ds end.
Definition s44_head ds := s44_of_nat(s44_value ds).
Fixpoint s44_enc(ds:list bool):list Sym := match ds with
 |[]=>[]|b::ds=>S2::(if b then S2 else S0)::s44_enc ds end.
Definition s44_zeros n := s44_enc(repeat false n).
Definition s44_main ds:cconf := (StA,(s44_enc ds,s44_head ds,[])).
Lemma s44_of_nat_good : forall n,s44_of_nat n=S0 \/ s44_of_nat n=S1 \/ s44_of_nat n=S2.
Proof. intro n;unfold s44_of_nat;destruct(n mod 3)as[|[|r]];auto. Qed.
Lemma s44_of_nat_succ : forall n,s44_of_nat(S n)=s44_rot(s44_of_nat n).
Proof.
 intro n;unfold s44_of_nat;assert(Hr:n mod 3<3)by(apply Nat.mod_upper_bound;lia).
 replace(S n)with(n+1)by lia;rewrite Nat.add_mod by lia.
 destruct(n mod 3)as[|[|[|r]]];cbn[s44_rot];try reflexivity;lia.
Qed.
Lemma s44_value_nil_false : forall ds,s44_value(ds++[false])=s44_value ds.
Proof. induction ds;cbn;[reflexivity|now rewrite IHds]. Qed.
Lemma s44_value_increment : forall n ds,
 s44_value(repeat false n++true::ds)=S(s44_value(repeat true n++false::ds)).
Proof. induction n;intro ds;cbn[repeat app s44_value];[lia|rewrite IHn;lia]. Qed.
Lemma s44_value_max_next : forall n,
 s44_value(repeat false n++[true])=S(s44_value(repeat true n)).
Proof. intro n;rewrite s44_value_increment,s44_value_nil_false;reflexivity. Qed.
Lemma s44_value_max_mod : forall n,s44_value(repeat true n)mod 3=0 \/ s44_value(repeat true n)mod 3=1.
Proof.
 induction n;[left;reflexivity|].
 change((1+2*s44_value(repeat true n))mod 3=0 \/ (1+2*s44_value(repeat true n))mod 3=1).
 rewrite Nat.add_mod,Nat.mul_mod by lia;destruct IHn as[E|E];rewrite E;cbn;auto.
Qed.
Lemma s44_head_max : forall n,s44_head(repeat true n)=S0 \/ s44_head(repeat true n)=S1.
Proof. intro n;unfold s44_head,s44_of_nat;destruct(s44_value_max_mod n)as[E|E];rewrite E;auto. Qed.
Lemma s44_repeat_shift : forall (x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma s44_zeros_shift : forall n l,s44_zeros n++S2::S0::l=S2::S0::(s44_zeros n++l).
Proof.
 induction n;intro l;[reflexivity|].
 change(S2::S0::(s44_zeros n++S2::S0::l)=S2::S0::S2::S0::(s44_zeros n++l));now rewrite IHn.
Qed.
Lemma s44_enc_app : forall ds es,s44_enc(ds++es)=s44_enc ds++s44_enc es.
Proof. induction ds;intro es;cbn;[reflexivity|now rewrite IHds]. Qed.
Lemma s44_enc_max : forall n,s44_enc(repeat true n)=repeat S2(2*n).
Proof.
 induction n;[reflexivity|].
 replace(2*S n)with(S(S(2*n)))by lia;cbn[repeat s44_enc];now rewrite IHn.
Qed.
Lemma s44_left_twos : forall n l r,
 csteps s44_tm n(s44_back StB(repeat S2 n++l)r)=Some(s44_back StB l(repeat S3 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app s44_back csteps cstep s44_tm ctape_move chd ctl].
 change(csteps s44_tm n(s44_back StB(repeat S2 n++l)(S3::r))=
 Some(s44_back StB l(S3::(repeat S3 n++r)))).
 rewrite IHn,s44_repeat_shift;reflexivity.
Qed.
Lemma s44_right_pairs : forall n l r,
 csteps s44_tm(2*n)(s44_front StA l(repeat S3(2*n)++r))=Some(s44_front StA(s44_zeros n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(2*S n)with(2+2*n)by lia;rewrite csteps_add.
 change(csteps s44_tm(2*n)(s44_front StA(S2::S0::l)(repeat S3(2*n)++r))=
 Some(s44_front StA(S2::S0::(s44_zeros n++l))r)).
 rewrite IHn,s44_zeros_shift;reflexivity.
Qed.
Lemma s44_start : forall l r h,h=S0 \/ h=S1 \/ h=S2 ->
 csteps s44_tm 1(StA,(l,h,r))=Some(s44_back StB l(s44_rot h::r)).
Proof. intros l r h[H|[H|H]];subst h;reflexivity. Qed.
Theorem s44_increment : forall n l r h,h=S0 \/ h=S1 \/ h=S2 ->
 csteps s44_tm(4*n+4)(StA,(repeat S2(2*n)++S2::S0::l,h,r))=
 Some(StA,(s44_zeros n++S2::S2::l,s44_rot h,r)).
Proof.
 intros n l r h Hh;replace(4*n+4)with(1+(S(2*n)+(2+2*n)))by lia.
 rewrite csteps_add,s44_start by exact Hh.
 rewrite s44_repeat_shift.
 change(csteps s44_tm(S(2*n)+(2+2*n))(s44_back StB(repeat S2(S(2*n))++S0::l)(s44_rot h::r))=
 Some(StA,(s44_zeros n++S2::S2::l,s44_rot h,r))).
 rewrite csteps_add,s44_left_twos,csteps_add.
 change(csteps s44_tm(2*n)(s44_front StA(S2::S2::l)(repeat S3(2*n)++s44_rot h::r))=
 Some(s44_front StA(s44_zeros n++S2::S2::l)(s44_rot h::r))).
 apply s44_right_pairs.
Qed.
Fixpoint s44_auxenc(ds:list bool):list Sym := match ds with
 |[]=>[]|b::ds=>(if b then S2 else S0)::S2::s44_auxenc ds end.
Definition s44_auxzeros n := s44_auxenc(repeat false n).
Definition s44_room ds := 2^length ds-1-s44_value ds.
Lemma s44_auxenc_app : forall ds es,s44_auxenc(ds++es)=s44_auxenc ds++s44_auxenc es.
Proof. induction ds;intro es;cbn;[reflexivity|now rewrite IHds]. Qed.
Lemma s44_auxenc_max : forall n,s44_auxenc(repeat true n)=repeat S2(2*n).
Proof.
 induction n;[reflexivity|].
 replace(2*S n)with(S(S(2*n)))by lia;cbn[repeat s44_auxenc];now rewrite IHn.
Qed.
Lemma s44_auxzeros_shift : forall n l,
 s44_auxzeros n++S0::S2::l=S0::S2::(s44_auxzeros n++l).
Proof.
 induction n;intro l;[reflexivity|].
 change(S0::S2::(s44_auxzeros n++S0::S2::l)=S0::S2::S0::S2::(s44_auxzeros n++l)).
 now rewrite IHn.
Qed.
Lemma s44_B_right_pairs : forall n l r,
 csteps s44_tm(2*n)(s44_front StB l(repeat S3(2*n)++r))=
 Some(s44_front StB(s44_auxzeros n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(2*S n)with(2+2*n)by lia;rewrite csteps_add.
 change(csteps s44_tm(2*n)(s44_front StB(S0::S2::l)(repeat S3(2*n)++r))=
 Some(s44_front StB(S0::S2::(s44_auxzeros n++l))r)).
 rewrite IHn,s44_auxzeros_shift;reflexivity.
Qed.
Lemma s44_B_left_even : forall n r,
 csteps s44_tm(4*n+1)(s44_back StB(repeat S2(2*n))r)=
 Some(s44_front StB(s44_auxzeros n++[S2])r).
Proof.
 intros n r;replace(4*n+1)with(2*n+(1+2*n))by lia.
 rewrite <-(app_nil_r(repeat S2(2*n)))at 1.
 rewrite csteps_add,s44_left_twos,csteps_add.
 change(csteps s44_tm(2*n)(s44_front StB[S2](repeat S3(2*n)++r))=
 Some(s44_front StB(s44_auxzeros n++[S2])r)).
 apply s44_B_right_pairs.
Qed.
Theorem s44_aux_increment : forall n l r,
 csteps s44_tm(4*n+2)(StB,(repeat S2(2*n)++S0::S2::l,S1,r))=
 Some(StB,(s44_auxzeros n++S2::S2::l,S1,r)).
Proof.
 intros n l r;replace(4*n+2)with(1+(2*n+(1+2*n)))by lia;rewrite csteps_add.
 change(csteps s44_tm(2*n+(1+2*n))
 (s44_back StB(repeat S2(2*n)++S0::S2::l)(S1::r))=
 Some(StB,(s44_auxzeros n++S2::S2::l,S1,r))).
 rewrite csteps_add,s44_left_twos,csteps_add.
 change(csteps s44_tm(2*n)(s44_front StB(S2::S2::l)(repeat S3(2*n)++S1::r))=
 Some(s44_front StB(s44_auxzeros n++S2::S2::l)(S1::r))).
 apply s44_B_right_pairs.
Qed.
Theorem s44_aux_finish : forall n r,
 csteps s44_tm(4*n+4)(StB,(repeat S2(2*n)++[S2],S1,r))=
 Some(StA,(s44_zeros n++[S2;S2],S1,r)).
Proof.
 intros n r;rewrite s44_repeat_shift,app_nil_r.
 change(csteps s44_tm(4*n+4)(StB,(repeat S2(S(2*n)),S1,r))=
 Some(StA,(s44_zeros n++[S2;S2],S1,r))).
 replace(4*n+4)with(1+(S(2*n)+(2+2*n)))by lia;rewrite csteps_add.
 change(csteps s44_tm(S(2*n)+(2+2*n))(s44_back StB(repeat S2(S(2*n)))(S1::r))=
 Some(StA,(s44_zeros n++[S2;S2],S1,r))).
 rewrite <-(app_nil_r(repeat S2(S(2*n))))at 1.
 rewrite csteps_add,s44_left_twos,csteps_add.
 change(csteps s44_tm(2*n)(s44_front StA[S2;S2](repeat S3(2*n)++S1::r))=
 Some(s44_front StA(s44_zeros n++[S2;S2])(S1::r))).
 apply s44_right_pairs.
Qed.
Lemma s44_value_bound : forall ds,s44_value ds<2^length ds.
Proof. induction ds as[|b ds IH];[cbn;lia|destruct b;cbn[s44_value length Nat.pow];nia]. Qed.
Lemma s44_room_decrease : forall n tail,
 s44_room(repeat false n++true::tail)<s44_room(repeat true n++false::tail).
Proof.
 intros n tail.
 pose proof(s44_value_bound(repeat false n++true::tail))as Hb.
 rewrite s44_value_increment in Hb.
 unfold s44_room;rewrite s44_value_increment.
 rewrite !app_length,!repeat_length in *;cbn[length]in *;lia.
Qed.
Lemma s44_decompose : forall ds,
 (exists n,ds=repeat true n) \/ (exists n tail,ds=repeat true n++false::tail).
Proof.
 induction ds as[|b ds IH].
 - left;exists 0;reflexivity.
 - destruct b.
   + destruct IH as[(n&E)|(n&tail&E)];subst ds.
     * left;exists(S n);reflexivity.
     * right;exists(S n),tail;reflexivity.
   + right;exists 0,ds;reflexivity.
Qed.
Theorem s44_aux_drain : forall v ds r,s44_room ds=v ->exists t,0<t /\
 csteps s44_tm t(StB,(s44_auxenc ds++[S2],S1,r))=
 Some(StA,(s44_zeros(length ds)++[S2;S2],S1,r)).
Proof.
 induction v using lt_wf_ind;intros ds r Hv.
 destruct(s44_decompose ds)as[(n&E)|(n&tail&E)];subst ds.
 - exists(4*n+4);split;[lia|].
   rewrite s44_auxenc_max,repeat_length;apply s44_aux_finish.
 - set(ds':=repeat false n++true::tail).
   assert(Hsmall:s44_room ds'<v).
   {unfold ds';rewrite <-Hv;apply s44_room_decrease. }
   destruct(H(s44_room ds')Hsmall ds' r eq_refl)as(t&Ht&Et).
   exists(4*n+2+t);split;[lia|].
   rewrite csteps_add,s44_auxenc_app,s44_auxenc_max;cbn[s44_auxenc].
   rewrite <-app_assoc;cbn[app];rewrite s44_aux_increment.
   unfold ds' in Et;rewrite s44_auxenc_app in Et;cbn[s44_auxenc]in Et.
   fold(s44_auxzeros n)in Et;rewrite <-app_assoc in Et;cbn[app]in Et.
   rewrite !app_length,!repeat_length in *;cbn[length]in *;exact Et.
Qed.
Theorem s44_overflow_zero : forall n,exists t,0<t /\
 csteps s44_tm t(StA,(repeat S2(2*n),S0,[]))=
 Some(StA,(s44_zeros n++[S2;S2],S1,[])).
Proof.
 intro n;destruct(s44_aux_drain(s44_room(repeat false n))
 (repeat false n)[]eq_refl)as(t&Ht&Et).
 rewrite repeat_length in Et;fold(s44_auxzeros n)in Et.
 exists(1+(4*n+1+t));split;[lia|].
 rewrite csteps_add.
 change(csteps s44_tm(4*n+1+t)(s44_back StB(repeat S2(2*n))[S1])=
 Some(StA,(s44_zeros n++[S2;S2],S1,[]))).
 rewrite csteps_add,s44_B_left_even;exact Et.
Qed.
Theorem s44_overflow_one : forall n,
 csteps s44_tm(4*S n+5)(StA,(repeat S2(2*S n),S1,[]))=
 Some(StA,(S2::S2::(s44_zeros n++[S2;S2]),S0,[])).
Proof.
 intro n;replace(4*S n+5)with(1+(2*S n+(2+(2*n+4))))by lia.
 rewrite csteps_add,s44_start by auto.
 rewrite <-(app_nil_r(repeat S2(2*S n)))at 1.
 rewrite csteps_add,s44_left_twos,csteps_add.
 replace(2*S n)with(S(S(2*n)))by lia.
 change(csteps s44_tm(2*n+4)(s44_front StA[S2;S2](S3::(repeat S3(2*n)++[S2])))=
 Some(StA,(S2::S2::(s44_zeros n++[S2;S2]),S0,[]))).
 rewrite <-s44_repeat_shift,csteps_add,s44_right_pairs;reflexivity.
Qed.
Theorem s44_main_next : forall ds,exists k ds',0<k /\ csteps s44_tm k(s44_main ds)=Some(s44_main ds').
Proof.
 intro ds;destruct(s44_decompose ds)as[(n&E)|(n&tail&E)];subst ds.
 - destruct(s44_head_max n)as[Hh|Hh].
   + destruct(s44_overflow_zero n)as(t&Ht&Et).
     exists t,(repeat false n++[true]);split;[exact Ht|].
     unfold s44_main;rewrite s44_enc_app,s44_enc_max;cbn[s44_enc];fold(s44_zeros n).
     unfold s44_head at 2;rewrite s44_value_max_next,s44_of_nat_succ;fold(s44_head(repeat true n));rewrite Hh.
     exact Et.
   + destruct n as[|n];[discriminate|].
     exists(4*S n+5),(true::(repeat false n++[true]));split;[lia|].
     assert(Hval:s44_value(true::(repeat false n++[true]))=S(S(s44_value(repeat true(S n))))).
     {cbn[s44_value repeat];rewrite s44_value_max_next;lia. }
     unfold s44_main;rewrite s44_enc_max.
     unfold s44_head at 2;rewrite Hval,!s44_of_nat_succ;fold(s44_head(repeat true(S n)));rewrite Hh.
     cbn[s44_enc s44_rot];rewrite s44_enc_app;cbn[s44_enc];fold(s44_zeros n);apply s44_overflow_one.
 - exists(4*n+4),(repeat false n++true::tail);split;[lia|].
   unfold s44_main;rewrite !s44_enc_app,s44_enc_max;cbn[s44_enc];fold(s44_zeros n).
   unfold s44_head at 2;rewrite s44_value_increment,s44_of_nat_succ.
   apply s44_increment;apply s44_of_nat_good.
Qed.
Example s44_entry : csteps s44_tm 6 c0=Some(s44_main[true]).
Proof. reflexivity. Qed.
Lemma s44_returns : forall N,exists k ds,N<=k /\ csteps s44_tm k c0=Some(s44_main ds).
Proof.
 induction N as[|N IH].
 - exists 6,[true];split;[lia|exact s44_entry].
 - destruct IH as(k&ds&Hk&E);destruct(s44_main_next ds)as(j&ds'&Hj&E').
   exists(k+j),ds';split;[lia|];rewrite csteps_add,E;exact E'.
Qed.
Theorem s44_nonhalt : NonHalt s44_tm.
Proof.
 intros n Hnone;destruct(s44_returns n)as(k&ds&Hk&E).
 pose proof(csteps_lift s44_tm k c0(s44_main ds)E)as Hrun;rewrite lift_c0 in Hrun.
 destruct(stepn_prefix s44_tm n k InitES(lift(s44_main ds))Hk Hrun)as(c&Ec&_);congruence.
Qed.
Theorem s44_A_recurrent : forall N,exists k,N<=k /\ VisitsAt s44_tm StA k.
Proof.
 intro N;destruct(s44_returns N)as(k&ds&Hk&E).
 exists k;split;[exact Hk|];exists(lift(s44_main ds));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem s44_B_recurrent : forall N,exists k,N<=k /\ VisitsAt s44_tm StB k.
Proof.
 intro N;destruct(s44_returns N)as(k&ds&Hk&E).
 exists(k+1);split;[lia|];exists(lift(s44_back StB(s44_enc ds)[s44_rot(s44_head ds)]));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;apply s44_start;apply s44_of_nat_good.
Qed.
Theorem s44_state_zero : QHBound 0 s44_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(s44_A_recurrent(S s))as(k&Hk&Hv);exfalso;apply(Hquiet k);[lia|exact Hv].
 - destruct(s44_B_recurrent(S s))as(k&Hk&Hv);exfalso;apply(Hquiet k);[lia|exact Hv].
Qed.
Theorem s44_sound : NonHalt s44_tm /\ QHBound 0 s44_tm.
Proof. split;[exact s44_nonhalt|exact s44_state_zero]. Qed.
Print Assumptions s44_sound.
