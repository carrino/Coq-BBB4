(** A ternary counter with a parity bit at the right boundary. Digits 0,1,2
    are encoded as physical symbols 0,2,1, each preceded (nearest first) by 1.
    The head bit is the parity of the number of physical digit-2 cells. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census OneStateReach OneStateConditional.
Import ListNotations.

Definition pc_tm : TM := fun q h=>match q,h with
 |StA,S0=>Some(mkTrans S1 DL StB)
 |StA,S1=>Some(mkTrans S0 DL StB)
 |StA,S2=>None
 |StA,S3=>Some(mkTrans S0 DR StB)
 |StB,S0=>Some(mkTrans S2 DR StB)
 |StB,S1=>Some(mkTrans S3 DL StB)
 |StB,S2=>Some(mkTrans S1 DR StB)
 |StB,S3=>Some(mkTrans S1 DR StA)
 end.
Definition pc_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition pc_back q l r:cconf := (q,(ctl l,chd l,r)).
Definition pc_head (p:bool) := if p then S1 else S0.
Fixpoint pc_enc(ds:list Sym) := match ds with []=>[]|d::ds=>S1::d::pc_enc ds end.
Definition pc_zeros n := pc_enc(repeat S0 n).
Definition pc_bump d := match d with S0=>S2|_=>S1 end.

Lemma pc_enc_app : forall ds es,pc_enc(ds++es)=pc_enc ds++pc_enc es.
Proof. induction ds;intro es;cbn;[reflexivity|now rewrite IHds]. Qed.
Lemma pc_enc_ones : forall n,pc_enc(repeat S1 n)=repeat S1(2*n).
Proof.
 induction n;[reflexivity|].
 replace(2*S n)with(S(S(2*n)))by lia;cbn[repeat pc_enc];now rewrite IHn.
Qed.
Lemma pc_repeat_shift : forall (x:Sym)n r,
 repeat x n++x::r=x::(repeat x n++r).
Proof. intros x n;induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma pc_zeros_shift : forall n l,
 pc_zeros n++S1::S0::l=S1::S0::(pc_zeros n++l).
Proof.
 induction n;intro l;[reflexivity|].
 change(S1::S0::(pc_zeros n++S1::S0::l)=S1::S0::S1::S0::(pc_zeros n++l)).
 now rewrite IHn.
Qed.

Lemma pc_left_ones : forall n l r,
 csteps pc_tm n(pc_back StB(repeat S1 n++l)r)=
 Some(pc_back StB l(repeat S3 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app pc_back csteps cstep pc_tm ctape_move chd ctl].
 change(csteps pc_tm n(pc_back StB(repeat S1 n++l)(S3::r))=
 Some(pc_back StB l(S3::(repeat S3 n++r)))).
 rewrite IHn,pc_repeat_shift;reflexivity.
Qed.

Lemma pc_right_pairs : forall n l r,
 csteps pc_tm(2*n)(pc_front StA l(repeat S3(2*n)++r))=
 Some(pc_front StA(pc_zeros n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(2*S n)with(2+2*n)by lia;rewrite csteps_add.
 change(csteps pc_tm(2*n)(pc_front StA(S1::S0::l)(repeat S3(2*n)++r))=
 Some(pc_front StA(S1::S0::(pc_zeros n++l))r)).
 rewrite IHn,pc_zeros_shift;reflexivity.
Qed.

Lemma pc_increment_run : forall n d l r p,
 d=S0 \/ d=S2 ->
 csteps pc_tm(4*n+4)
  (StA,(repeat S1(2*n+1)++d::l,pc_head p,r))=
 Some(StA,(pc_zeros n++S1::pc_bump d::l,pc_head(negb p),r)).
Proof.
 intros n d l r p Hd.
 assert(E:csteps pc_tm 1(StA,(repeat S1(2*n+1)++d::l,pc_head p,r))=
  Some(pc_back StB(repeat S1(2*n+1)++d::l)(pc_head(negb p)::r))).
 {destruct p;reflexivity. }
 replace(4*n+4)with(1+((2*n+1)+(2+2*n)))by lia.
 rewrite csteps_add,E,csteps_add,pc_left_ones.
 replace(2*n+1)with(S(2*n))by lia;rewrite csteps_add.
 destruct Hd as[Hd|Hd];subst d.
 - change(csteps pc_tm(2*n)(pc_front StA(S1::S2::l)(repeat S3(2*n)++pc_head(negb p)::r))=
   Some(pc_front StA(pc_zeros n++S1::S2::l)(pc_head(negb p)::r))).
   apply pc_right_pairs.
 - change(csteps pc_tm(2*n)(pc_front StA(S1::S1::l)(repeat S3(2*n)++pc_head(negb p)::r))=
   Some(pc_front StA(pc_zeros n++S1::S1::l)(pc_head(negb p)::r))).
   apply pc_right_pairs.
Qed.

Lemma pc_overflow_run : forall n,
 csteps pc_tm(4*S n+5)(StA,(repeat S1(2*S n),S0,[]))=
 Some(StA,(S1::S2::(pc_zeros n++[S1;S2]),S0,[])).
Proof.
 intro n.
 assert(E:csteps pc_tm 1(StA,(repeat S1(2*S n),S0,[]))=
  Some(pc_back StB(repeat S1(2*S n)) [S1])).
 {reflexivity. }
 replace(4*S n+5)with(1+(2*S n+(2+(2*n+4))))by lia.
 rewrite csteps_add,E.
 rewrite <-(app_nil_r(repeat S1(2*S n)))at 1.
 rewrite csteps_add,pc_left_ones,csteps_add.
 assert(E2:csteps pc_tm 2(pc_back StB[](repeat S3(2*S n)++[S1]))=
  Some(pc_front StA[S1;S2](repeat S3(2*n)++[S3;S1]))).
 {replace(2*S n)with(S(S(2*n)))by lia.
  cbn[repeat app pc_back pc_front csteps cstep pc_tm ctape_move chd ctl].
  rewrite pc_repeat_shift;reflexivity. }
 rewrite E2,csteps_add,pc_right_pairs.
 reflexivity.
Qed.

Definition pc_digit d := d=S0 \/ d=S1 \/ d=S2.
Definition pc_good ds := Forall pc_digit ds.
Fixpoint pc_parity(ds:list Sym) := match ds with
 |[]=>false |S2::ds=>negb(pc_parity ds)|_::ds=>pc_parity ds end.
Definition pc_main ds:cconf := (StA,(pc_enc ds,pc_head(pc_parity ds),[])).

Lemma pc_good_repeat : forall d n,pc_digit d -> pc_good(repeat d n).
Proof. intros d n H;unfold pc_good;induction n;cbn[repeat];constructor;assumption. Qed.
Lemma pc_ones_parity : forall n ds,pc_parity(repeat S1 n++ds)=pc_parity ds.
Proof. induction n;intro ds;cbn;auto. Qed.
Lemma pc_zeros_parity : forall n ds,pc_parity(repeat S0 n++ds)=pc_parity ds.
Proof. induction n;intro ds;cbn;auto. Qed.
Lemma pc_ones_only : forall n,pc_parity(repeat S1 n)=false.
Proof. induction n;cbn;auto. Qed.
Lemma pc_grow_parity : forall n,pc_parity(S2::(repeat S0 n++[S2]))=false.
Proof. intro n;cbn[pc_parity];rewrite pc_zeros_parity;reflexivity. Qed.
Lemma pc_prefix_enc : forall n d ds,
 pc_enc(repeat S1 n++d::ds)=repeat S1(2*n+1)++d::pc_enc ds.
Proof.
 intros;rewrite pc_enc_app,pc_enc_ones;cbn[pc_enc].
 replace(2*n+1)with(S(2*n))by lia;cbn[repeat app].
 apply pc_repeat_shift.
Qed.
Lemma pc_increment_parity : forall n d ds,
 d=S0 \/ d=S2 ->
 pc_parity(repeat S0 n++pc_bump d::ds)=negb(pc_parity(repeat S1 n++d::ds)).
Proof.
 intros n d ds Hd;rewrite pc_zeros_parity,pc_ones_parity.
 destruct Hd as[Hd|Hd];subst d;cbn[pc_bump pc_parity];destruct(pc_parity ds);reflexivity.
Qed.
Lemma pc_decompose : forall ds,pc_good ds ->
 (exists n,ds=repeat S1 n) \/
 (exists n d tail,ds=repeat S1 n++d::tail /\ (d=S0 \/ d=S2) /\ pc_good tail).
Proof.
 induction ds as[|d ds IH];intro H.
 - left;exists 0;reflexivity.
 - inversion H as[|x xs Hd Htail];subst.
   destruct Hd as[Hd|[Hd|Hd]];subst d.
   + right;exists 0,S0,ds;repeat split;auto.
   + destruct(IH Htail)as[(n&E)|(n&d&tail&E&Hd&Ht)].
     * left;exists(S n);cbn[repeat];now rewrite E.
     * right;exists(S n),d,tail;split;[cbn[repeat app];now rewrite E|auto].
   + right;exists 0,S2,ds;repeat split;auto.
Qed.

Theorem pc_main_next : forall ds,
 pc_good ds -> ds<>[] ->
 exists k ds',0<k /\ pc_good ds' /\ ds'<>[] /\
 csteps pc_tm k(pc_main ds)=Some(pc_main ds').
Proof.
 intros ds Hgood Hne;destruct(pc_decompose ds Hgood)as[(n&E)|(n&d&tail&E&Hd&Htail)];subst ds.
 - destruct n;[contradiction|].
   exists(4*S n+5),(S2::(repeat S0 n++[S2]));split;[lia|].
   split.
   + constructor;[unfold pc_digit;auto|].
     apply Forall_app;split.
     * apply pc_good_repeat;unfold pc_digit;auto.
     * constructor;[unfold pc_digit;auto|constructor].
   + split;[discriminate|].
     unfold pc_main;rewrite pc_enc_ones,pc_ones_only,pc_grow_parity.
     cbn[pc_head pc_enc];rewrite pc_enc_app.
     change(csteps pc_tm(4*S n+5)(StA,(repeat S1(2*S n),S0,[]))=
       Some(StA,(S1::S2::(pc_zeros n++[S1;S2]),S0,[]))).
     apply pc_overflow_run.
 - exists(4*n+4),(repeat S0 n++pc_bump d::tail);split;[lia|].
   split.
   + apply Forall_app;split.
     * apply pc_good_repeat;unfold pc_digit;auto.
     * constructor;[destruct Hd as[Hd|Hd];subst d;unfold pc_digit;cbn[pc_bump];auto|exact Htail].
   + split;[destruct n;discriminate|].
     unfold pc_main;rewrite pc_prefix_enc,pc_enc_app.
     cbn[pc_enc];fold(pc_zeros n).
     rewrite(pc_increment_parity n d tail Hd).
     apply pc_increment_run;exact Hd.
Qed.

Example pc_entry : csteps pc_tm 5 c0=Some(pc_main[S1]).
Proof. reflexivity. Qed.

Lemma pc_returns : forall N,exists k ds,
 N<=k /\ pc_good ds /\ ds<>[] /\ csteps pc_tm k c0=Some(pc_main ds).
Proof.
 induction N as[|N IH].
 - exists 5,[S1];split;[lia|];split.
   + constructor;[unfold pc_digit;auto|constructor].
   + split;[discriminate|exact pc_entry].
 - destruct IH as(k&ds&Hk&Hg&Hne&E).
   destruct(pc_main_next ds Hg Hne)as(j&ds'&Hj&Hg'&Hne'&E').
   exists(k+j),ds';split;[lia|];split;[exact Hg'|];split;[exact Hne'|].
   rewrite csteps_add,E;exact E'.
Qed.

Theorem pc_nonhalt : NonHalt pc_tm.
Proof.
 intros n Hnone;destruct(pc_returns n)as(k&ds&Hk&_&_&E).
 pose proof(csteps_lift pc_tm k c0(pc_main ds)E)as Hrun;rewrite lift_c0 in Hrun.
 destruct(stepn_prefix pc_tm n k InitES(lift(pc_main ds))Hk Hrun)as(c&Ec&_);congruence.
Qed.
Theorem pc_A_recurrent : forall N,exists k,N<=k /\ VisitsAt pc_tm StA k.
Proof.
 intro N;destruct(pc_returns N)as(k&ds&Hk&_&_&E).
 exists k;split;[exact Hk|];exists(lift(pc_main ds));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Lemma pc_B_checked : ore_auto_goal(orc_fill_goal pc_tm StB)StB=true.
Proof. vm_compute;reflexivity. Qed.
Theorem pc_state_zero : QHBound 0 pc_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(pc_A_recurrent(S s))as(k&Hk&Hv);exfalso;apply(Hquiet k);[lia|exact Hv].
 - destruct(orc_goal_recurs pc_tm StB pc_nonhalt pc_B_checked(S s))as(k&Hk&Hv).
   exfalso;apply(Hquiet k);[lia|exact Hv].
Qed.
Theorem pc_sound : NonHalt pc_tm /\ QHBound 0 pc_tm.
Proof. split;[exact pc_nonhalt|exact pc_state_zero]. Qed.
Print Assumptions pc_sound.
