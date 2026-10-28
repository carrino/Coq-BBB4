(** Pairs20/22 encode binary bits. The boundary head is the binary value
    modulo three; in particular an all-maximal word cannot have head2. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census.
Import ListNotations.
Definition pz_tm : TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StB
 |StA,S2=>mkTrans S0 DL StB |StA,S3=>mkTrans S0 DR StB
 |StB,S0=>mkTrans S2 DR StB |StB,S1=>mkTrans S3 DR StA
 |StB,S2=>mkTrans S3 DL StB |StB,S3=>mkTrans S2 DR StA end).
Definition pz_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition pz_back q l r:cconf := (q,(ctl l,chd l,r)).
Definition pz_rot h := match h with S0=>S1|S1=>S2|_=>S0 end.
Definition pz_of_nat n := match n mod 3 with 0=>S0|1=>S1|_=>S2 end.
Fixpoint pz_value(ds:list bool):nat := match ds with
 |[]=>0|b::ds=>(if b then 1 else 0)+2*pz_value ds end.
Definition pz_head ds := pz_of_nat(pz_value ds).
Fixpoint pz_enc(ds:list bool):list Sym := match ds with
 |[]=>[]|b::ds=>S2::(if b then S2 else S0)::pz_enc ds end.
Definition pz_zeros n := pz_enc(repeat false n).
Definition pz_main ds:cconf := (StA,(pz_enc ds,pz_head ds,[])).
Lemma pz_of_nat_good : forall n,pz_of_nat n=S0 \/ pz_of_nat n=S1 \/ pz_of_nat n=S2.
Proof. intro n;unfold pz_of_nat;destruct(n mod 3)as[|[|r]];auto. Qed.
Lemma pz_of_nat_succ : forall n,pz_of_nat(S n)=pz_rot(pz_of_nat n).
Proof.
 intro n;unfold pz_of_nat;assert(Hr:n mod 3<3)by(apply Nat.mod_upper_bound;lia).
 replace(S n)with(n+1)by lia;rewrite Nat.add_mod by lia.
 destruct(n mod 3)as[|[|[|r]]];cbn[pz_rot];try reflexivity;lia.
Qed.
Lemma pz_value_nil_false : forall ds,pz_value(ds++[false])=pz_value ds.
Proof. induction ds;cbn;[reflexivity|now rewrite IHds]. Qed.
Lemma pz_value_increment : forall n ds,
 pz_value(repeat false n++true::ds)=S(pz_value(repeat true n++false::ds)).
Proof. induction n;intro ds;cbn[repeat app pz_value];[lia|rewrite IHn;lia]. Qed.
Lemma pz_value_max_next : forall n,
 pz_value(repeat false n++[true])=S(pz_value(repeat true n)).
Proof. intro n;rewrite pz_value_increment,pz_value_nil_false;reflexivity. Qed.
Lemma pz_value_max_mod : forall n,pz_value(repeat true n)mod 3=0 \/ pz_value(repeat true n)mod 3=1.
Proof.
 induction n;[left;reflexivity|].
 change((1+2*pz_value(repeat true n))mod 3=0 \/ (1+2*pz_value(repeat true n))mod 3=1).
 rewrite Nat.add_mod,Nat.mul_mod by lia;destruct IHn as[E|E];rewrite E;cbn;auto.
Qed.
Lemma pz_head_max : forall n,pz_head(repeat true n)=S0 \/ pz_head(repeat true n)=S1.
Proof. intro n;unfold pz_head,pz_of_nat;destruct(pz_value_max_mod n)as[E|E];rewrite E;auto. Qed.
Lemma pz_repeat_shift : forall (x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma pz_zeros_shift : forall n l,pz_zeros n++S2::S0::l=S2::S0::(pz_zeros n++l).
Proof.
 induction n;intro l;[reflexivity|].
 change(S2::S0::(pz_zeros n++S2::S0::l)=S2::S0::S2::S0::(pz_zeros n++l));now rewrite IHn.
Qed.
Lemma pz_enc_app : forall ds es,pz_enc(ds++es)=pz_enc ds++pz_enc es.
Proof. induction ds;intro es;cbn;[reflexivity|now rewrite IHds]. Qed.
Lemma pz_enc_max : forall n,pz_enc(repeat true n)=repeat S2(2*n).
Proof.
 induction n;[reflexivity|].
 replace(2*S n)with(S(S(2*n)))by lia;cbn[repeat pz_enc];now rewrite IHn.
Qed.
Lemma pz_left_twos : forall n l r,
 csteps pz_tm n(pz_back StB(repeat S2 n++l)r)=Some(pz_back StB l(repeat S3 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app pz_back csteps cstep pz_tm ctape_move chd ctl].
 change(csteps pz_tm n(pz_back StB(repeat S2 n++l)(S3::r))=
 Some(pz_back StB l(S3::(repeat S3 n++r)))).
 rewrite IHn,pz_repeat_shift;reflexivity.
Qed.
Lemma pz_right_pairs : forall n l r,
 csteps pz_tm(2*n)(pz_front StA l(repeat S3(2*n)++r))=Some(pz_front StA(pz_zeros n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(2*S n)with(2+2*n)by lia;rewrite csteps_add.
 change(csteps pz_tm(2*n)(pz_front StA(S2::S0::l)(repeat S3(2*n)++r))=
 Some(pz_front StA(S2::S0::(pz_zeros n++l))r)).
 rewrite IHn,pz_zeros_shift;reflexivity.
Qed.
Lemma pz_start : forall l r h,h=S0 \/ h=S1 \/ h=S2 ->
 csteps pz_tm 1(StA,(l,h,r))=Some(pz_back StB l(pz_rot h::r)).
Proof. intros l r h[H|[H|H]];subst h;reflexivity. Qed.
Theorem pz_increment : forall n l r h,h=S0 \/ h=S1 \/ h=S2 ->
 csteps pz_tm(4*n+4)(StA,(repeat S2(2*n)++S2::S0::l,h,r))=
 Some(StA,(pz_zeros n++S2::S2::l,pz_rot h,r)).
Proof.
 intros n l r h Hh;replace(4*n+4)with(1+(S(2*n)+(2+2*n)))by lia.
 rewrite csteps_add,pz_start by exact Hh.
 rewrite pz_repeat_shift.
 change(csteps pz_tm(S(2*n)+(2+2*n))(pz_back StB(repeat S2(S(2*n))++S0::l)(pz_rot h::r))=
 Some(StA,(pz_zeros n++S2::S2::l,pz_rot h,r))).
 rewrite csteps_add,pz_left_twos,csteps_add.
 change(csteps pz_tm(2*n)(pz_front StA(S2::S2::l)(repeat S3(2*n)++pz_rot h::r))=
 Some(pz_front StA(pz_zeros n++S2::S2::l)(pz_rot h::r))).
 apply pz_right_pairs.
Qed.
Theorem pz_overflow_zero : forall n,
 csteps pz_tm(4*n+5)(StA,(repeat S2(2*n),S0,[]))=
 Some(StA,(pz_zeros n++[S2;S2],S1,[])).
Proof.
 intro n;destruct n as[|n];[reflexivity|].
 replace(4*S n+5)with(1+(2*S n+(2+(2*n+4))))by lia.
 rewrite csteps_add,pz_start by auto.
 rewrite <-(app_nil_r(repeat S2(2*S n)))at 1.
 rewrite csteps_add,pz_left_twos,csteps_add.
 replace(2*S n)with(S(S(2*n)))by lia.
 change(csteps pz_tm(2*n+4)(pz_front StA[S2;S2](S3::(repeat S3(2*n)++[S1])))=
 Some(StA,(S2::S0::(pz_zeros n++[S2;S2]),S1,[]))).
 rewrite <-pz_repeat_shift,csteps_add,pz_right_pairs;reflexivity.
Qed.
Theorem pz_overflow_one : forall n,
 csteps pz_tm(4*S n+5)(StA,(repeat S2(2*S n),S1,[]))=
 Some(StA,(S2::S2::(pz_zeros n++[S2;S2]),S0,[])).
Proof.
 intro n;replace(4*S n+5)with(1+(2*S n+(2+(2*n+4))))by lia.
 rewrite csteps_add,pz_start by auto.
 rewrite <-(app_nil_r(repeat S2(2*S n)))at 1.
 rewrite csteps_add,pz_left_twos,csteps_add.
 replace(2*S n)with(S(S(2*n)))by lia.
 change(csteps pz_tm(2*n+4)(pz_front StA[S2;S2](S3::(repeat S3(2*n)++[S2])))=
 Some(StA,(S2::S2::(pz_zeros n++[S2;S2]),S0,[]))).
 rewrite <-pz_repeat_shift,csteps_add,pz_right_pairs;reflexivity.
Qed.
Lemma pz_decompose : forall ds,
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
Theorem pz_main_next : forall ds,exists k ds',0<k /\ csteps pz_tm k(pz_main ds)=Some(pz_main ds').
Proof.
 intro ds;destruct(pz_decompose ds)as[(n&E)|(n&tail&E)];subst ds.
 - destruct(pz_head_max n)as[Hh|Hh].
   + exists(4*n+5),(repeat false n++[true]);split;[lia|].
     unfold pz_main;rewrite pz_enc_app,pz_enc_max;cbn[pz_enc];fold(pz_zeros n).
     unfold pz_head at 2;rewrite pz_value_max_next,pz_of_nat_succ;fold(pz_head(repeat true n));rewrite Hh.
     apply pz_overflow_zero.
   + destruct n as[|n];[discriminate|].
     exists(4*S n+5),(true::(repeat false n++[true]));split;[lia|].
     assert(Hval:pz_value(true::(repeat false n++[true]))=S(S(pz_value(repeat true(S n))))).
     {cbn[pz_value repeat];rewrite pz_value_max_next;lia. }
     unfold pz_main;rewrite pz_enc_max.
     unfold pz_head at 2;rewrite Hval,!pz_of_nat_succ;fold(pz_head(repeat true(S n)));rewrite Hh.
     cbn[pz_enc pz_rot];rewrite pz_enc_app;cbn[pz_enc];fold(pz_zeros n);apply pz_overflow_one.
 - exists(4*n+4),(repeat false n++true::tail);split;[lia|].
   unfold pz_main;rewrite !pz_enc_app,pz_enc_max;cbn[pz_enc];fold(pz_zeros n).
   unfold pz_head at 2;rewrite pz_value_increment,pz_of_nat_succ.
   apply pz_increment;apply pz_of_nat_good.
Qed.
Example pz_entry : csteps pz_tm 5 c0=Some(pz_main[true]).
Proof. reflexivity. Qed.
Lemma pz_returns : forall N,exists k ds,N<=k /\ csteps pz_tm k c0=Some(pz_main ds).
Proof.
 induction N as[|N IH].
 - exists 5,[true];split;[lia|exact pz_entry].
 - destruct IH as(k&ds&Hk&E);destruct(pz_main_next ds)as(j&ds'&Hj&E').
   exists(k+j),ds';split;[lia|];rewrite csteps_add,E;exact E'.
Qed.
Theorem pz_nonhalt : NonHalt pz_tm.
Proof.
 intros n Hnone;destruct(pz_returns n)as(k&ds&Hk&E).
 pose proof(csteps_lift pz_tm k c0(pz_main ds)E)as Hrun;rewrite lift_c0 in Hrun.
 destruct(stepn_prefix pz_tm n k InitES(lift(pz_main ds))Hk Hrun)as(c&Ec&_);congruence.
Qed.
Theorem pz_A_recurrent : forall N,exists k,N<=k /\ VisitsAt pz_tm StA k.
Proof.
 intro N;destruct(pz_returns N)as(k&ds&Hk&E).
 exists k;split;[exact Hk|];exists(lift(pz_main ds));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem pz_B_recurrent : forall N,exists k,N<=k /\ VisitsAt pz_tm StB k.
Proof.
 intro N;destruct(pz_returns N)as(k&ds&Hk&E).
 exists(k+1);split;[lia|];exists(lift(pz_back StB(pz_enc ds)[pz_rot(pz_head ds)]));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;apply pz_start;apply pz_of_nat_good.
Qed.
Theorem pz_state_zero : QHBound 0 pz_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(pz_A_recurrent(S s))as(k&Hk&Hv);exfalso;apply(Hquiet k);[lia|exact Hv].
 - destruct(pz_B_recurrent(S s))as(k&Hk&Hv);exfalso;apply(Hquiet k);[lia|exact Hv].
Qed.
Theorem pz_sound : NonHalt pz_tm /\ QHBound 0 pz_tm.
Proof. split;[exact pz_nonhalt|exact pz_state_zero]. Qed.
Print Assumptions pz_sound.
