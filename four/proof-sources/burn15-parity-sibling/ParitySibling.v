(** A complete-table sibling of the parity counter. Odd digit parity requires
    head 1; even parity allows head 0 or 2. Fresh overflows reset the head to 0. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census OneStateReach OneStateConditional.
From BBB24Burn13ParityCounter Require Import ParityCounter.
Import ListNotations.

Definition ps_tm : TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StB
 |StA,S2=>mkTrans S1 DL StB |StA,S3=>mkTrans S0 DR StB
 |StB,S0=>mkTrans S2 DR StB |StB,S1=>mkTrans S3 DL StB
 |StB,S2=>mkTrans S1 DR StB |StB,S3=>mkTrans S1 DR StA end).
Definition ps_write h := match h with S1=>S2|_=>S1 end.
Definition ps_ok (p:bool) h := if p then h=S1 else h=S0 \/ h=S2.
Definition ps_main ds h:cconf := (StA,(pc_enc ds,h,[])).

Lemma ps_left_ones : forall n l r,
 csteps ps_tm n(pc_back StB(repeat S1 n++l)r)=
 Some(pc_back StB l(repeat S3 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app pc_back csteps cstep ps_tm ctape_move chd ctl].
 change(csteps ps_tm n(pc_back StB(repeat S1 n++l)(S3::r))=
 Some(pc_back StB l(S3::(repeat S3 n++r)))).
 rewrite IHn,pc_repeat_shift;reflexivity.
Qed.
Lemma ps_right_pairs : forall n l r,
 csteps ps_tm(2*n)(pc_front StA l(repeat S3(2*n)++r))=
 Some(pc_front StA(pc_zeros n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(2*S n)with(2+2*n)by lia;rewrite csteps_add.
 change(csteps ps_tm(2*n)(pc_front StA(S1::S0::l)(repeat S3(2*n)++r))=
 Some(pc_front StA(S1::S0::(pc_zeros n++l))r)).
 rewrite IHn,pc_zeros_shift;reflexivity.
Qed.
Lemma ps_increment_run : forall n d l r h,
 d=S0 \/ d=S2 -> h=S0 \/ h=S1 \/ h=S2 ->
 csteps ps_tm(4*n+4)(StA,(repeat S1(2*n+1)++d::l,h,r))=
 Some(StA,(pc_zeros n++S1::pc_bump d::l,ps_write h,r)).
Proof.
 intros n d l r h Hd Hh.
 assert(E:csteps ps_tm 1(StA,(repeat S1(2*n+1)++d::l,h,r))=
  Some(pc_back StB(repeat S1(2*n+1)++d::l)(ps_write h::r))).
 {destruct Hh as[Hh|[Hh|Hh]];subst h;reflexivity. }
 replace(4*n+4)with(1+((2*n+1)+(2+2*n)))by lia.
 rewrite csteps_add,E,csteps_add,ps_left_ones.
 replace(2*n+1)with(S(2*n))by lia;rewrite csteps_add.
 destruct Hd as[Hd|Hd];subst d.
 - change(csteps ps_tm(2*n)(pc_front StA(S1::S2::l)(repeat S3(2*n)++ps_write h::r))=
   Some(pc_front StA(pc_zeros n++S1::S2::l)(ps_write h::r))).
   apply ps_right_pairs.
 - change(csteps ps_tm(2*n)(pc_front StA(S1::S1::l)(repeat S3(2*n)++ps_write h::r))=
   Some(pc_front StA(pc_zeros n++S1::S1::l)(ps_write h::r))).
   apply ps_right_pairs.
Qed.
Lemma ps_overflow_run : forall n h,
 h=S0 \/ h=S2 ->
 csteps ps_tm(4*S n+5)(StA,(repeat S1(2*S n),h,[]))=
 Some(StA,(S1::S2::(pc_zeros n++[S1;S2]),S0,[])).
Proof.
 intros n h Hh.
 assert(E:csteps ps_tm 1(StA,(repeat S1(2*S n),h,[]))=
  Some(pc_back StB(repeat S1(2*S n)) [S1])).
 {destruct Hh as[Hh|Hh];subst h;reflexivity. }
 replace(4*S n+5)with(1+(2*S n+(2+(2*n+4))))by lia.
 rewrite csteps_add,E.
 rewrite <-(app_nil_r(repeat S1(2*S n)))at 1.
 rewrite csteps_add,ps_left_ones,csteps_add.
 assert(E2:csteps ps_tm 2(pc_back StB[](repeat S3(2*S n)++[S1]))=
  Some(pc_front StA[S1;S2](repeat S3(2*n)++[S3;S1]))).
 {replace(2*S n)with(S(S(2*n)))by lia.
  cbn[repeat app pc_back pc_front csteps cstep ps_tm ctape_move chd ctl].
  rewrite pc_repeat_shift;reflexivity. }
 rewrite E2,csteps_add,ps_right_pairs;reflexivity.
Qed.
Lemma ps_ok_head : forall p h,ps_ok p h -> h=S0 \/ h=S1 \/ h=S2.
Proof. intros p h H;destruct p;cbn[ps_ok]in H;tauto. Qed.
Lemma ps_ok_flip : forall p h,ps_ok p h -> ps_ok(negb p)(ps_write h).
Proof.
 intros p h H;destruct p;cbn[ps_ok]in H.
 - subst h;right;reflexivity.
 - destruct H as[H|H];subst h;reflexivity.
Qed.

Theorem ps_main_next : forall ds h,
 pc_good ds -> ds<>[] -> ps_ok(pc_parity ds)h ->
 exists k ds' h',0<k /\ pc_good ds' /\ ds'<>[] /\ ps_ok(pc_parity ds')h' /\
 csteps ps_tm k(ps_main ds h)=Some(ps_main ds' h').
Proof.
 intros ds h Hgood Hne Hhead.
 destruct(pc_decompose ds Hgood)as[(n&E)|(n&d&tail&E&Hd&Htail)];subst ds.
 - destruct n;[contradiction|].
   exists(4*S n+5),(S2::(repeat S0 n++[S2])),S0;split;[lia|].
   split.
   + constructor;[unfold pc_digit;auto|].
     apply Forall_app;split.
     * apply pc_good_repeat;unfold pc_digit;auto.
     * constructor;[unfold pc_digit;auto|constructor].
   + split;[discriminate|];split.
     * rewrite pc_grow_parity;left;reflexivity.
     * unfold ps_main;rewrite pc_enc_ones.
       cbn[pc_enc];rewrite pc_enc_app.
       change(csteps ps_tm(4*S n+5)(StA,(repeat S1(2*S n),h,[]))=
         Some(StA,(S1::S2::(pc_zeros n++[S1;S2]),S0,[]))).
       apply ps_overflow_run;rewrite pc_ones_only in Hhead;exact Hhead.
 - exists(4*n+4),(repeat S0 n++pc_bump d::tail),(ps_write h);split;[lia|].
   split.
   + apply Forall_app;split.
     * apply pc_good_repeat;unfold pc_digit;auto.
     * constructor;[destruct Hd as[Hd|Hd];subst d;unfold pc_digit;cbn[pc_bump];auto|exact Htail].
   + split;[destruct n;discriminate|];split.
     * rewrite(pc_increment_parity n d tail Hd);apply ps_ok_flip;exact Hhead.
     * unfold ps_main;rewrite pc_prefix_enc,pc_enc_app;cbn[pc_enc];fold(pc_zeros n).
       apply ps_increment_run;[exact Hd|eapply ps_ok_head;exact Hhead].
Qed.
Example ps_entry : csteps ps_tm 5 c0=Some(ps_main[S1]S0).
Proof. reflexivity. Qed.
Lemma ps_returns : forall N,exists k ds h,
 N<=k /\ pc_good ds /\ ds<>[] /\ ps_ok(pc_parity ds)h /\
 csteps ps_tm k c0=Some(ps_main ds h).
Proof.
 induction N as[|N IH].
 - exists 5,[S1],S0;split;[lia|];split.
   + constructor;[unfold pc_digit;auto|constructor].
   + split;[discriminate|];split;[left;reflexivity|exact ps_entry].
 - destruct IH as(k&ds&h&Hk&Hg&Hne&Hh&E).
   destruct(ps_main_next ds h Hg Hne Hh)as(j&ds'&h'&Hj&Hg'&Hne'&Hh'&E').
   exists(k+j),ds',h';split;[lia|];split;[exact Hg'|];split;[exact Hne'|];split;[exact Hh'|].
   rewrite csteps_add,E;exact E'.
Qed.
Theorem ps_nonhalt : NonHalt ps_tm.
Proof.
 intros n Hnone;destruct(ps_returns n)as(k&ds&h&Hk&_&_&_&E).
 pose proof(csteps_lift ps_tm k c0(ps_main ds h)E)as Hrun;rewrite lift_c0 in Hrun.
 destruct(stepn_prefix ps_tm n k InitES(lift(ps_main ds h))Hk Hrun)as(c&Ec&_);congruence.
Qed.
Theorem ps_A_recurrent : forall N,exists k,N<=k /\ VisitsAt ps_tm StA k.
Proof.
 intro N;destruct(ps_returns N)as(k&ds&h&Hk&_&_&_&E).
 exists k;split;[exact Hk|];exists(lift(ps_main ds h));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Lemma ps_B_checked : ore_auto_goal(orc_fill_goal ps_tm StB)StB=true.
Proof. vm_compute;reflexivity. Qed.
Theorem ps_state_zero : QHBound 0 ps_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(ps_A_recurrent(S s))as(k&Hk&Hv);exfalso;apply(Hquiet k);[lia|exact Hv].
 - destruct(orc_goal_recurs ps_tm StB ps_nonhalt ps_B_checked(S s))as(k&Hk&Hv).
   exfalso;apply(Hquiet k);[lia|exact Hv].
Qed.
Theorem ps_sound : NonHalt ps_tm /\ QHBound 0 ps_tm.
Proof. split;[exact ps_nonhalt|exact ps_state_zero]. Qed.
Print Assumptions ps_sound.
