(** Binary pairs12/22 followed by a terminal11,21,or2. Terminal values
    2,0,1 give a closed modulo-three checksum at the blank right boundary. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census.
Import ListNotations.
Definition tp_tm : TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StB
 |StA,S2=>mkTrans S0 DL StB |StA,S3=>mkTrans S2 DR StB
 |StB,S0=>mkTrans S1 DR StB |StB,S1=>mkTrans S2 DR StA
 |StB,S2=>mkTrans S3 DL StB |StB,S3=>mkTrans S1 DR StA end).
Definition tp_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition tp_back q l r:cconf := (q,(ctl l,chd l,r)).
Definition tp_rot h := match h with S0=>S1|S1=>S2|_=>S0 end.
Definition tp_of_nat n := match n mod 3 with 0=>S0|1=>S1|_=>S2 end.
Inductive tp_tail := T11|T21|T2.
Definition tp_base t := match t with T11=>2|T21=>0|T2=>1 end.
Definition tp_end t := match t with T11=>[S1;S1]|T21=>[S2;S1]|T2=>[S2] end.
Fixpoint tp_value(ds:list bool)(base:nat):nat := match ds with
 |[]=>base|b::ds=>(if b then 1 else 0)+2*tp_value ds base end.
Definition tp_head ds t := tp_of_nat(tp_value ds(tp_base t)).
Fixpoint tp_enc(ds:list bool):list Sym := match ds with
 |[]=>[]|b::ds=>(if b then S2 else S1)::S2::tp_enc ds end.
Definition tp_zeros n := tp_enc(repeat false n).
Definition tp_main ds t:cconf := (StA,(tp_enc ds++tp_end t,tp_head ds t,[])).
Lemma tp_of_nat_good : forall n,tp_of_nat n=S0 \/ tp_of_nat n=S1 \/ tp_of_nat n=S2.
Proof. intro n;unfold tp_of_nat;destruct(n mod 3)as[|[|r]];auto. Qed.
Lemma tp_of_nat_succ : forall n,tp_of_nat(S n)=tp_rot(tp_of_nat n).
Proof.
 intro n;unfold tp_of_nat;assert(Hr:n mod 3<3)by(apply Nat.mod_upper_bound;lia).
 replace(S n)with(n+1)by lia;rewrite Nat.add_mod by lia.
 destruct(n mod 3)as[|[|[|r]]];cbn[tp_rot];try reflexivity;lia.
Qed.
Lemma tp_of_nat_zero : forall n,tp_of_nat n=S0 -> n mod 3=0.
Proof. intro n;unfold tp_of_nat;destruct(n mod 3)as[|[|r]];intro H;try discriminate;reflexivity. Qed.
Lemma tp_of_nat_one : forall n,tp_of_nat n=S1 -> n mod 3=1.
Proof. intro n;unfold tp_of_nat;destruct(n mod 3)as[|[|r]];intro H;try discriminate;reflexivity. Qed.
Lemma tp_value_increment : forall n ds b,
 tp_value(repeat false n++true::ds)b=S(tp_value(repeat true n++false::ds)b).
Proof. induction n;intros ds b;cbn[repeat app tp_value];[lia|rewrite IHn;lia]. Qed.
Lemma tp_value_zeros_zero : forall n,tp_value(repeat false n)0=0.
Proof. induction n;cbn;lia. Qed.
Lemma tp_value_zeros_one : forall n,tp_value(repeat false n)1=S(tp_value(repeat true n)0).
Proof. induction n;cbn[repeat tp_value];[reflexivity|rewrite IHn;lia]. Qed.
Lemma tp_value_outer : forall n,tp_value(repeat false n)2=S(tp_value(repeat true n)1).
Proof. induction n;cbn[repeat tp_value];[reflexivity|rewrite IHn;lia]. Qed.
Lemma tp_value_terminal_zero : forall n,
 tp_value(true::repeat false n)1=2*tp_value(repeat true n)0+3.
Proof. intro n;cbn[tp_value];rewrite tp_value_zeros_one;lia. Qed.
Lemma tp_value_terminal_one : forall n,
 tp_value(false::true::repeat false n)1=2*tp_value(repeat true(S n))0+4.
Proof. intro n;cbn[tp_value repeat];rewrite tp_value_zeros_one;lia. Qed.
Lemma tp_value_max_zero_mod : forall n,tp_value(repeat true n)0 mod 3=0 \/ tp_value(repeat true n)0 mod 3=1.
Proof.
 induction n;[left;reflexivity|].
 change((1+2*tp_value(repeat true n)0)mod 3=0 \/ (1+2*tp_value(repeat true n)0)mod 3=1).
 rewrite Nat.add_mod,Nat.mul_mod by lia;destruct IHn as[E|E];rewrite E;cbn;auto.
Qed.
Lemma tp_value_max_two_mod : forall n,tp_value(repeat true n)2 mod 3=2.
Proof.
 induction n;[reflexivity|].
 change((1+2*tp_value(repeat true n)2)mod 3=2).
 rewrite Nat.add_mod,Nat.mul_mod by lia;rewrite IHn;reflexivity.
Qed.
Lemma tp_head_max_11 : forall n,tp_head(repeat true n)T11=S2.
Proof. intro n;unfold tp_head,tp_base,tp_of_nat;rewrite tp_value_max_two_mod;reflexivity. Qed.
Lemma tp_head_max_21 : forall n,tp_head(repeat true n)T21=S0 \/ tp_head(repeat true n)T21=S1.
Proof. intro n;unfold tp_head,tp_base,tp_of_nat;destruct(tp_value_max_zero_mod n)as[E|E];rewrite E;auto. Qed.
Lemma tp_head_new_zero : forall n,tp_head(repeat true n)T21=S0 ->tp_head(true::repeat false n)T2=S0.
Proof.
 intros n Hh;unfold tp_head,tp_base in *;apply tp_of_nat_zero in Hh.
 rewrite tp_value_terminal_zero;unfold tp_of_nat.
 rewrite Nat.add_mod,Nat.mul_mod by lia;rewrite Hh;reflexivity.
Qed.
Lemma tp_head_new_one : forall n,tp_head(repeat true(S n))T21=S1 ->tp_head(false::true::repeat false n)T2=S0.
Proof.
 intros n Hh;unfold tp_head,tp_base in *;apply tp_of_nat_one in Hh.
 rewrite tp_value_terminal_one;unfold tp_of_nat.
 rewrite Nat.add_mod,Nat.mul_mod by lia;rewrite Hh;reflexivity.
Qed.
Lemma tp_repeat_shift : forall (x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma tp_zeros_shift : forall n l,tp_zeros n++S1::S2::l=S1::S2::(tp_zeros n++l).
Proof.
 induction n;intro l;[reflexivity|].
 change(S1::S2::(tp_zeros n++S1::S2::l)=S1::S2::S1::S2::(tp_zeros n++l));now rewrite IHn.
Qed.
Lemma tp_enc_app : forall ds es,tp_enc(ds++es)=tp_enc ds++tp_enc es.
Proof. induction ds;intro es;cbn;[reflexivity|now rewrite IHds]. Qed.
Lemma tp_enc_max : forall n,tp_enc(repeat true n)=repeat S2(2*n).
Proof.
 induction n;[reflexivity|].
 replace(2*S n)with(S(S(2*n)))by lia;cbn[repeat tp_enc];now rewrite IHn.
Qed.
Lemma tp_left_twos : forall n l r,
 csteps tp_tm n(tp_back StB(repeat S2 n++l)r)=Some(tp_back StB l(repeat S3 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app tp_back csteps cstep tp_tm ctape_move chd ctl].
 change(csteps tp_tm n(tp_back StB(repeat S2 n++l)(S3::r))=
 Some(tp_back StB l(S3::(repeat S3 n++r)))).
 rewrite IHn,tp_repeat_shift;reflexivity.
Qed.
Lemma tp_right_pairs : forall n l r,
 csteps tp_tm(2*n)(tp_front StA l(repeat S3(2*n)++r))=Some(tp_front StA(tp_zeros n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(2*S n)with(2+2*n)by lia;rewrite csteps_add.
 change(csteps tp_tm(2*n)(tp_front StA(S1::S2::l)(repeat S3(2*n)++r))=
 Some(tp_front StA(S1::S2::(tp_zeros n++l))r)).
 rewrite IHn,tp_zeros_shift;reflexivity.
Qed.
Lemma tp_start : forall l r h,h=S0 \/ h=S1 \/ h=S2 ->
 csteps tp_tm 1(StA,(l,h,r))=Some(tp_back StB l(tp_rot h::r)).
Proof. intros l r h[H|[H|H]];subst h;reflexivity. Qed.
Theorem tp_increment : forall n x l r h,h=S0 \/ h=S1 \/ h=S2 ->
 csteps tp_tm(4*n+2)(StA,(repeat S2(2*n)++S1::x::l,h,r))=
 Some(StA,(tp_zeros n++S2::x::l,tp_rot h,r)).
Proof.
 intros n x l r h Hh;replace(4*n+2)with(1+(2*n+(1+2*n)))by lia.
 rewrite csteps_add,tp_start by exact Hh.
 rewrite csteps_add,tp_left_twos,csteps_add.
 change(csteps tp_tm(2*n)(tp_front StA(S2::x::l)(repeat S3(2*n)++tp_rot h::r))=
 Some(tp_front StA(tp_zeros n++S2::x::l)(tp_rot h::r))).
 apply tp_right_pairs.
Qed.
Theorem tp_outer_odd : forall n h,h=S0 \/ h=S1 \/ h=S2 ->
 csteps tp_tm(4*n+4)(StA,(repeat S2(S(2*n)),h,[]))=
 Some(StA,(tp_zeros n++[S1;S1],tp_rot h,[])).
Proof.
 intros n h Hh;replace(4*n+4)with(1+(S(2*n)+(2+2*n)))by lia.
 rewrite csteps_add,tp_start by exact Hh.
 rewrite <-(app_nil_r(repeat S2(S(2*n))))at 1.
 rewrite csteps_add,tp_left_twos,csteps_add.
 change(csteps tp_tm(2*n)(tp_front StA[S1;S1](repeat S3(2*n)++[tp_rot h]))=
 Some(tp_front StA(tp_zeros n++[S1;S1])[tp_rot h])).
 apply tp_right_pairs.
Qed.
Theorem tp_terminal_zero : forall n,
 csteps tp_tm(4*n+5)(StA,(repeat S2(2*n)++[S2;S1],S0,[]))=
 Some(StA,(S2::S2::(tp_zeros n++[S2]),S0,[])).
Proof.
 intro n;replace(4*n+5)with(1+(S(2*n)+(1+(2*n+2))))by lia.
 rewrite csteps_add,tp_start by auto;rewrite tp_repeat_shift.
 change(csteps tp_tm(S(2*n)+(1+(2*n+2)))(tp_back StB(repeat S2(S(2*n))++[S1])[S1])=
 Some(StA,(S2::S2::(tp_zeros n++[S2]),S0,[]))).
 rewrite csteps_add,tp_left_twos,csteps_add.
 change(csteps tp_tm(2*n+2)(tp_front StA[S2](S3::(repeat S3(2*n)++[S1])))=
 Some(StA,(S2::S2::(tp_zeros n++[S2]),S0,[]))).
 rewrite <-tp_repeat_shift,csteps_add,tp_right_pairs;reflexivity.
Qed.
Theorem tp_terminal_one : forall n,
 csteps tp_tm(4*S n+9)(StA,(repeat S2(2*S n)++[S2;S1],S1,[]))=
 Some(StA,(S1::S2::S2::S2::(tp_zeros n++[S2]),S0,[])).
Proof.
 intro n;replace(4*S n+9)with(1+(S(2*S n)+(1+(2*S n+6))))by lia.
 rewrite csteps_add,tp_start by auto;rewrite tp_repeat_shift.
 change(csteps tp_tm(S(2*S n)+(1+(2*S n+6)))(tp_back StB(repeat S2(S(2*S n))++[S1])[S2])=
 Some(StA,(S1::S2::S2::S2::(tp_zeros n++[S2]),S0,[]))).
 rewrite csteps_add,tp_left_twos,csteps_add.
 change(csteps tp_tm(2*S n+6)(tp_front StA[S2](S3::(repeat S3(2*S n)++[S2])))=
 Some(StA,(S1::S2::S2::S2::(tp_zeros n++[S2]),S0,[]))).
 rewrite <-tp_repeat_shift,csteps_add,tp_right_pairs;reflexivity.
Qed.
Lemma tp_decompose : forall ds,
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
Theorem tp_main_next : forall ds t,exists k ds' t',0<k /\
 csteps tp_tm k(tp_main ds t)=Some(tp_main ds' t').
Proof.
 intros ds t;destruct(tp_decompose ds)as[(n&E)|(n&tail&E)];subst ds.
 - destruct t.
   + exists(4*n+2),(repeat false n),T21;split;[lia|].
     unfold tp_main;rewrite tp_enc_max,tp_head_max_11.
     unfold tp_head at 1;cbn[tp_base];rewrite tp_value_zeros_zero.
     change(csteps tp_tm(4*n+2)(StA,(repeat S2(2*n)++[S1;S1],S2,[]))=
      Some(StA,(tp_zeros n++[S2;S1],tp_rot S2,[]))).
     apply tp_increment;auto.
   + destruct(tp_head_max_21 n)as[Hh|Hh].
     * exists(4*n+5),(true::repeat false n),T2;split;[lia|].
       unfold tp_main;rewrite tp_enc_max,Hh,tp_head_new_zero by exact Hh.
       change(csteps tp_tm(4*n+5)(StA,(repeat S2(2*n)++[S2;S1],S0,[]))=
        Some(StA,(S2::S2::(tp_zeros n++[S2]),S0,[]))).
       apply tp_terminal_zero.
     * destruct n as[|n];[discriminate|].
       exists(4*S n+9),(false::true::repeat false n),T2;split;[lia|].
       unfold tp_main;rewrite tp_enc_max,Hh,tp_head_new_one by exact Hh.
       change(csteps tp_tm(4*S n+9)(StA,(repeat S2(2*S n)++[S2;S1],S1,[]))=
        Some(StA,(S1::S2::S2::S2::(tp_zeros n++[S2]),S0,[]))).
       apply tp_terminal_one.
   + exists(4*n+4),(repeat false n),T11;split;[lia|].
     unfold tp_main;rewrite tp_enc_max.
     unfold tp_head at 2;cbn[tp_base];rewrite tp_value_outer,tp_of_nat_succ.
     assert(Er:repeat S2(2*n)++[S2]=repeat S2(S(2*n))).
     {rewrite tp_repeat_shift,app_nil_r;reflexivity. }
     cbn[tp_end];rewrite Er;change(csteps tp_tm(4*n+4)(StA,(repeat S2(S(2*n)),tp_head(repeat true n)T2,[]))=
      Some(StA,(tp_zeros n++[S1;S1],tp_rot(tp_head(repeat true n)T2),[]))).
     apply tp_outer_odd;apply tp_of_nat_good.
 - exists(4*n+2),(repeat false n++true::tail),t;split;[lia|].
   unfold tp_main;rewrite !tp_enc_app,tp_enc_max;cbn[tp_enc];fold(tp_zeros n).
   rewrite <-!app_assoc;cbn[app].
   unfold tp_head at 2;rewrite tp_value_increment,tp_of_nat_succ.
   apply tp_increment;apply tp_of_nat_good.
Qed.
Example tp_entry : csteps tp_tm 3 c0=Some(tp_main[]T21).
Proof. reflexivity. Qed.
Lemma tp_returns : forall N,exists k ds t,N<=k /\ csteps tp_tm k c0=Some(tp_main ds t).
Proof.
 induction N as[|N IH].
 - exists 3,[],T21;split;[lia|exact tp_entry].
 - destruct IH as(k&ds&t&Hk&E);destruct(tp_main_next ds t)as(j&ds'&t'&Hj&E').
   exists(k+j),ds',t';split;[lia|];rewrite csteps_add,E;exact E'.
Qed.
Theorem tp_nonhalt : NonHalt tp_tm.
Proof.
 intros n Hnone;destruct(tp_returns n)as(k&ds&t&Hk&E).
 pose proof(csteps_lift tp_tm k c0(tp_main ds t)E)as Hrun;rewrite lift_c0 in Hrun.
 destruct(stepn_prefix tp_tm n k InitES(lift(tp_main ds t))Hk Hrun)as(c&Ec&_);congruence.
Qed.
Theorem tp_A_recurrent : forall N,exists k,N<=k /\ VisitsAt tp_tm StA k.
Proof.
 intro N;destruct(tp_returns N)as(k&ds&t&Hk&E).
 exists k;split;[exact Hk|];exists(lift(tp_main ds t));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem tp_B_recurrent : forall N,exists k,N<=k /\ VisitsAt tp_tm StB k.
Proof.
 intro N;destruct(tp_returns N)as(k&ds&t&Hk&E).
 exists(k+1);split;[lia|];exists(lift(tp_back StB(tp_enc ds++tp_end t)[tp_rot(tp_head ds t)]));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;apply tp_start;apply tp_of_nat_good.
Qed.
Theorem tp_state_zero : QHBound 0 tp_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(tp_A_recurrent(S s))as(k&Hk&Hv);exfalso;apply(Hquiet k);[lia|exact Hv].
 - destruct(tp_B_recurrent(S s))as(k&Hk&Hv);exfalso;apply(Hquiet k);[lia|exact Hv].
Qed.
Theorem tp_sound : NonHalt tp_tm /\ QHBound 0 tp_tm.
Proof. split;[exact tp_nonhalt|exact tp_state_zero]. Qed.
Print Assumptions tp_sound.
