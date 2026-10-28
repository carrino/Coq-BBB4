(** Three binary-counter siblings. A modulo-three checksum and bit-length
    parity exclude the all-ones carries which would expose an escaping B. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census OneStateReach.
Import ListNotations.
Definition bt_tm(v:nat):TM:=fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S0 DL StA
 |StA,S2=>mkTrans S0 DR StB |StA,S3=>mkTrans S3 DL StB
 |StB,S0=>mkTrans S3 DR StB
 |StB,S1=>match v with 0=>mkTrans S1 DL StB|1=>mkTrans S2 DR StA|_=>mkTrans S3 DL StB end
 |StB,S2=>mkTrans S3 DR StA |StB,S3=>mkTrans S2 DL StB end).
Definition bt_front q l r:cconf:=(q,(l,chd r,ctl r)).
Definition bt_back q l r:cconf:=(q,(ctl l,chd l,r)).
Fixpoint bt_enc(ds:list bool):list Sym:=match ds with
 |[]=>[]|b::ds=>S3::(if b then S3 else S0)::bt_enc ds end.
Fixpoint bt_value(ds:list bool):nat:=match ds with
 |[]=>0|b::ds=>(if b then 1 else 0)+2*bt_value ds end.
Inductive bt_kind:=K0|K1|K3|K21|K23.
Definition bt_word k r:=match k with
 |K0=>S0::r|K1=>S1::r|K3=>S3::r|K21=>S2::S1::r|K23=>S2::S3::r end.
Definition bt_main ds k r:=bt_front StA(bt_enc ds)(bt_word k r).
Definition bt_valid v ds k:=match k with
 |K0=>bt_value ds mod 3=0 |K1=>bt_value ds mod 3=1
 |K3=>Nat.even(length ds)=false
 |K21=>if v=?0 then Nat.even(length ds)=true else bt_value ds mod 3=2
 |K23=>bt_value ds mod 3=1 end.

Lemma bt_repeat_shift : forall (x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma bt_enc_app : forall ds es,bt_enc(ds++es)=bt_enc ds++bt_enc es.
Proof. induction ds as[|b ds IH];intro es;cbn;[reflexivity|now rewrite IH]. Qed.
Lemma bt_enc_false_shift : forall n l,bt_enc(repeat false n)++S3::S0::l=S3::S0::(bt_enc(repeat false n)++l).
Proof. induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma bt_value_zeros : forall n ds,bt_value(repeat false n++ds)=2^n*bt_value ds.
Proof. induction n;intro ds;cbn;[lia|rewrite IHn;lia]. Qed.
Lemma bt_increment_value : forall n ds,
 bt_value(repeat false n++true::ds)=S(bt_value(repeat true n++false::ds)).
Proof. induction n;intro ds;cbn;[lia|rewrite IHn;lia]. Qed.
Lemma bt_true_value : forall n,S(bt_value(repeat true n))=2^n.
Proof. induction n;cbn;[reflexivity|rewrite <-IHn;lia]. Qed.
Lemma bt_pow_mod : forall n,2^n mod 3=if Nat.even n then 1 else 2.
Proof.
 induction n;[reflexivity|]. rewrite Nat.pow_succ_r',Nat.mul_mod by lia.
 rewrite IHn,Nat.even_succ,<-Nat.negb_even.
 destruct(Nat.even n);reflexivity.
Qed.
Lemma bt_true_zero_even : forall n,bt_value(repeat true n)mod 3=0 -> Nat.even n=true.
Proof.
 intros n H;pose proof(bt_true_value n)as E.
 apply(f_equal(fun x=>x mod 3))in E.
 replace(S(bt_value(repeat true n)))with(bt_value(repeat true n)+1)in E by lia.
 rewrite Nat.add_mod,H,bt_pow_mod in E by lia;destruct(Nat.even n);cbn in E;congruence.
Qed.
Lemma bt_true_one_odd : forall n,bt_value(repeat true n)mod 3=1 -> Nat.even n=false.
Proof.
 intros n H;pose proof(bt_true_value n)as E.
 apply(f_equal(fun x=>x mod 3))in E.
 replace(S(bt_value(repeat true n)))with(bt_value(repeat true n)+1)in E by lia.
 rewrite Nat.add_mod,H,bt_pow_mod in E by lia;destruct(Nat.even n);cbn in E;congruence.
Qed.
Lemma bt_true_not_two : forall n,bt_value(repeat true n)mod 3<>2.
Proof.
 intros n H;pose proof(bt_true_value n)as E.
 apply(f_equal(fun x=>x mod 3))in E.
 replace(S(bt_value(repeat true n)))with(bt_value(repeat true n)+1)in E by lia.
 rewrite Nat.add_mod,H,bt_pow_mod in E by lia;destruct(Nat.even n);cbn in E;discriminate.
Qed.
Lemma bt_decompose : forall ds,
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
Lemma bt_increment_length : forall n ds,
 length(repeat false n++true::ds)=length(repeat true n++false::ds).
Proof. intros;rewrite !app_length,!repeat_length;reflexivity. Qed.
Lemma bt_mod_succ : forall x y a, y=S x -> x mod 3=a ->y mod 3=(a+1)mod 3.
Proof. intros x y a -> H;replace(S x)with(x+1)by lia;rewrite Nat.add_mod,H by lia;reflexivity. Qed.
Lemma bt_mod_twice : forall x a,x mod 3=a ->(2*x)mod 3=(2*a)mod 3.
Proof. intros x a H;rewrite Nat.mul_mod,H by lia;reflexivity. Qed.
Lemma bt_mod_digit : forall x a,x mod 3=a ->(1+2*x)mod 3=(1+2*a)mod 3.
Proof. intros x a H;rewrite Nat.add_mod by lia;rewrite(bt_mod_twice x a H),<-Nat.add_mod by lia;reflexivity. Qed.

Lemma bt_left_true : forall v n l r,
 csteps(bt_tm v)(2*n)(bt_back StB(bt_enc(repeat true n)++l)r)=
 Some(bt_back StB l(repeat S2(2*n)++r)).
Proof.
 intros v n;induction n;intros l r;[reflexivity|].
 replace(2*S n)with(2+2*n)by lia;rewrite csteps_add.
 change(csteps(bt_tm v)(2*n)(bt_back StB(bt_enc(repeat true n)++l)(S2::S2::r))=
 Some(bt_back StB l(S2::S2::(repeat S2(2*n)++r)))).
 rewrite IHn,!bt_repeat_shift;reflexivity.
Qed.
Lemma bt_right_pairs : forall v n l r,
 csteps(bt_tm v)(2*n)(bt_front StA l(repeat S2(2*n)++r))=
 Some(bt_front StA(bt_enc(repeat false n)++l)r).
Proof.
 intros v n;induction n;intros l r;[reflexivity|].
 replace(2*S n)with(2+2*n)by lia;rewrite csteps_add.
 change(csteps(bt_tm v)(2*n)(bt_front StA(S3::S0::l)(repeat S2(2*n)++r))=
 Some(bt_front StA(S3::S0::(bt_enc(repeat false n)++l))r)).
 rewrite IHn,bt_enc_false_shift;reflexivity.
Qed.
Theorem bt_increment : forall v n ds r,
 csteps(bt_tm v)(4*n+3)(bt_back StB(bt_enc(repeat true n++false::ds))r)=
 Some(bt_front StA(bt_enc(repeat false n++true::ds))r).
Proof.
 intros v n ds r;replace(4*n+3)with(2*n+(3+2*n))by lia.
 rewrite bt_enc_app,csteps_add,bt_left_true,csteps_add.
 change(csteps(bt_tm v)(2*n)(bt_front StA(S3::S3::bt_enc ds)(repeat S2(2*n)++r))=
 Some(bt_front StA(bt_enc(repeat false n++true::ds))r)).
 rewrite bt_right_pairs,bt_enc_app;reflexivity.
Qed.
Lemma bt_overflow_single : forall v n h r,
 csteps(bt_tm v)(4*S n)(bt_back StB(bt_enc(repeat true(S n)))(h::r))=
 Some(bt_front StA(bt_enc(repeat false n++[true]))(S2::h::r)).
Proof.
 intros v n h r;replace(4*S n)with(2*S n+(2+2*n))by lia.
 rewrite <-(app_nil_r(bt_enc(repeat true(S n))))at 1.
 rewrite csteps_add,bt_left_true,csteps_add.
 replace(2*S n)with(S(S(2*n)))by lia;cbn[repeat app].
 change(csteps(bt_tm v)(2*n)(bt_front StA[S3;S3](S2::(repeat S2(2*n)++h::r)))=
 Some(bt_front StA(bt_enc(repeat false n++[true]))(S2::h::r))).
 rewrite <-bt_repeat_shift,bt_right_pairs,bt_enc_app;reflexivity.
Qed.
Lemma bt_overflow_double : forall v n h r,
 csteps(bt_tm v)(4*n+2)(bt_back StB(bt_enc(repeat true n))(S2::h::r))=
 Some(bt_front StA(bt_enc(repeat false n++[true]))(h::r)).
Proof.
 intros v n h r;replace(4*n+2)with(2*n+(2+2*n))by lia.
 rewrite <-(app_nil_r(bt_enc(repeat true n)))at 1.
 rewrite csteps_add,bt_left_true,csteps_add,bt_repeat_shift.
 change(csteps(bt_tm v)(2*n)(bt_front StA[S3;S3](repeat S2(2*n)++h::r))=
 Some(bt_front StA(bt_enc(repeat false n++[true]))(h::r))).
 rewrite bt_right_pairs,bt_enc_app;reflexivity.
Qed.

Lemma bt_blank_head : forall r,all_blank r=true -> chd r=S0.
Proof. intros[|h r]H;[reflexivity|];cbn[all_blank]in H;apply andb_prop in H as[H _];apply sym_eqb_spec;exact H. Qed.
Lemma bt_blank_tail : forall r,all_blank r=true -> all_blank(ctl r)=true.
Proof. intros[|h r]H;[reflexivity|];cbn[all_blank]in H;apply andb_prop in H;tauto. Qed.
Definition bt_good_run v cc:=exists t ds k r,0<t /\ csteps(bt_tm v)t cc=Some(bt_main ds k r) /\
 all_blank r=true /\ bt_valid v ds k.
Lemma bt_compose : forall v n cc cc',csteps(bt_tm v)n cc=Some cc' ->bt_good_run v cc' ->bt_good_run v cc.
Proof.
 intros v n cc cc' E(t&ds&k&r&Ht&E'&Hr&Hv).
 exists(n+t),ds,k,r;split;[lia|];split;[rewrite csteps_add,E;exact E'|auto].
Qed.
Lemma bt_empty_one : forall v r,all_blank r=true ->bt_good_run v(bt_back StB[](S1::r)).
Proof.
 intros v r Hr;destruct v as[|[|v]].
 - exists 5,[true],K1,r;split;[lia|];split;[reflexivity|split;[exact Hr|reflexivity]].
 - exists 4,[true],K1,(ctl r);split;[lia|];split.
   + unfold bt_back,bt_main,bt_front;cbn[csteps cstep bt_tm ctape_move chd ctl bt_word bt_enc].
     destruct r as[|h r];[reflexivity|].
     cbn[all_blank]in Hr;apply andb_prop in Hr as[Hh _];apply sym_eqb_spec in Hh;subst h;reflexivity.
   + split;[apply bt_blank_tail;exact Hr|reflexivity].
 - exists 5,[true],K3,r;split;[lia|];split;[reflexivity|split;[exact Hr|reflexivity]].
Qed.
Lemma bt_carry_one : forall v ds r,bt_value ds mod 3=0 ->all_blank r=true ->
 bt_good_run v(bt_back StB(bt_enc ds)(S1::r)).
Proof.
 intros v ds r Hv Hr;destruct(bt_decompose ds)as[(n&E)|(n&tail&E)];subst ds.
 - destruct n as[|n];[apply bt_empty_one;exact Hr|].
   pose proof(bt_true_zero_even(S n)Hv)as He.
   exists(4*S n),(repeat false n++[true]),K21,r;split;[lia|];split;[apply bt_overflow_single|].
   split;[exact Hr|];unfold bt_valid;rewrite app_length,repeat_length;cbn[length].
   destruct v as[|[|v]];cbn[Nat.eqb].
   + replace(n+1)with(S n)by lia;exact He.
   + rewrite bt_value_zeros;cbn[bt_value];rewrite Nat.mul_1_r,bt_pow_mod.
     rewrite Nat.even_succ,<-Nat.negb_even in He;destruct(Nat.even n);[discriminate|reflexivity].
   + rewrite bt_value_zeros;cbn[bt_value];rewrite Nat.mul_1_r,bt_pow_mod.
     rewrite Nat.even_succ,<-Nat.negb_even in He;destruct(Nat.even n);[discriminate|reflexivity].
 - exists(4*n+3),(repeat false n++true::tail),K1,r;split;[lia|];split;[apply bt_increment|].
   split;[exact Hr|];unfold bt_valid;pose proof(bt_increment_value n tail)as E.
   exact(bt_mod_succ _ _ _ E Hv).
Qed.
Lemma bt_carry_three : forall v ds r,Nat.even(length ds)=false ->all_blank r=true ->
 bt_good_run v(bt_back StB(bt_enc ds)(S3::r)).
Proof.
 intros v ds r Hv Hr;destruct(bt_decompose ds)as[(n&E)|(n&tail&E)];subst ds.
 - rewrite repeat_length in Hv;destruct n as[|n];[discriminate|].
   exists(4*S n),(repeat false n++[true]),K23,r;split;[lia|];split;[apply bt_overflow_single|].
   split;[exact Hr|];unfold bt_valid;rewrite bt_value_zeros;cbn[bt_value];rewrite Nat.mul_1_r,bt_pow_mod.
   rewrite Nat.even_succ,<-Nat.negb_even in Hv;destruct(Nat.even n);[reflexivity|discriminate].
 - exists(4*n+3),(repeat false n++true::tail),K3,r;split;[lia|];split;[apply bt_increment|].
   split;[exact Hr|];unfold bt_valid;rewrite bt_increment_length;exact Hv.
Qed.
Lemma bt_carry_two_three : forall v ds r,bt_value ds mod 3=0 ->all_blank r=true ->
 bt_good_run v(bt_back StB(bt_enc ds)(S2::S3::r)).
Proof.
 intros v ds r Hv Hr;destruct(bt_decompose ds)as[(n&E)|(n&tail&E)];subst ds.
 - exists(4*n+2),(repeat false n++[true]),K3,r;split;[lia|];split;[apply bt_overflow_double|].
   split;[exact Hr|];unfold bt_valid;rewrite app_length,repeat_length;cbn[length].
   replace(n+1)with(S n)by lia;rewrite Nat.even_succ,<-Nat.negb_even.
   rewrite(bt_true_zero_even n Hv);reflexivity.
 - exists(4*n+3),(repeat false n++true::tail),K23,r;split;[lia|];split;[apply bt_increment|].
   split;[exact Hr|];unfold bt_valid;pose proof(bt_increment_value n tail)as E.
   exact(bt_mod_succ _ _ _ E Hv).
Qed.
Lemma bt_carry_two_two : forall v ds r,bt_value ds mod 3=2 ->all_blank r=true ->
 bt_good_run v(bt_back StB(bt_enc ds)(S2::S2::r)).
Proof.
 intros v ds r Hv Hr;destruct(bt_decompose ds)as[(n&E)|(n&tail&E)];subst ds.
 - exfalso;exact(bt_true_not_two n Hv).
 - exists((4*n+3)+2),(false::(repeat false n++true::tail)),K0,(ctl r);split;[lia|];split.
   + rewrite csteps_add,bt_increment.
     change(csteps(bt_tm v)(2*1)(bt_front StA(bt_enc(repeat false n++true::tail))(repeat S2(2*1)++r))=
       Some(bt_main(false::(repeat false n++true::tail))K0(ctl r))).
     rewrite bt_right_pairs;unfold bt_front,bt_main;rewrite(bt_blank_head r Hr);reflexivity.
   + split;[apply bt_blank_tail;exact Hr|];unfold bt_valid;cbn[bt_value].
     pose proof(bt_mod_succ _ _ _ (bt_increment_value n tail)Hv)as Hi.
     change(bt_value(repeat false n++true::tail)mod 3=0)in Hi.
     replace(bt_value(repeat false n++true::tail)+(bt_value(repeat false n++true::tail)+0))
       with(2*bt_value(repeat false n++true::tail))by lia.
     exact(bt_mod_twice _ _ Hi).
Qed.
Lemma bt_carry_two_one : forall ds r,Nat.even(length ds)=true ->all_blank r=true ->
 bt_good_run 0(bt_back StB(bt_enc ds)(S2::S1::r)).
Proof.
 intros ds r Hv Hr;destruct(bt_decompose ds)as[(n&E)|(n&tail&E)];subst ds.
 - exists(4*n+2),(repeat false n++[true]),K1,r;split;[lia|];split;[apply bt_overflow_double|].
   split;[exact Hr|];unfold bt_valid;rewrite bt_value_zeros;cbn[bt_value];rewrite Nat.mul_1_r,bt_pow_mod.
   rewrite repeat_length in Hv;rewrite Hv;reflexivity.
 - exists(4*n+3),(repeat false n++true::tail),K21,r;split;[lia|];split;[apply bt_increment|].
   split;[exact Hr|];unfold bt_valid;cbn[Nat.eqb];rewrite bt_increment_length;exact Hv.
Qed.

Lemma bt_mod_twice_inv : forall x,(2*x)mod 3=1 ->x mod 3=2.
Proof.
 intros x H;pose proof(Nat.mod_upper_bound x 3 ltac:(lia))as Hb.
 assert(E:x mod 3=0 \/ x mod 3=1 \/ x mod 3=2)by lia.
 destruct E as[E|[E|E]];[| |exact E];rewrite Nat.mul_mod,E in H by lia;cbn in H;discriminate.
Qed.
Lemma bt_mod_digit_inv : forall x,(1+2*x)mod 3=1 ->x mod 3=0.
Proof.
 intros x H;pose proof(Nat.mod_upper_bound x 3 ltac:(lia))as Hb.
 assert(E:x mod 3=0 \/ x mod 3=1 \/ x mod 3=2)by lia.
 destruct E as[E|[E|E]];[exact E| |];rewrite Nat.add_mod,Nat.mul_mod,E in H by lia;cbn in H;discriminate.
Qed.
Theorem bt_main_next : forall v ds k r,
 bt_valid v ds k ->all_blank r=true ->bt_good_run v(bt_main ds k r).
Proof.
 intros v ds k r Hv Hr;destruct k;cbn[bt_valid]in Hv.
 - eapply(bt_compose v 1 _ (bt_back StB(bt_enc ds)(S1::r)));[reflexivity|].
   apply bt_carry_one;assumption.
 - destruct ds as[|b ds];[discriminate|];destruct b.
   + eapply(bt_compose v 3 _ (bt_back StB(bt_enc ds)(S2::S3::S0::r)));[reflexivity|].
     apply bt_carry_two_three;[apply bt_mod_digit_inv;exact Hv|cbn[all_blank];exact Hr].
   + eapply(bt_compose v 5 _ (bt_back StB(bt_enc ds)(S2::S2::S0::r)));[reflexivity|].
     apply bt_carry_two_two;[apply bt_mod_twice_inv;exact Hv|cbn[all_blank];exact Hr].
 - eapply(bt_compose v 1 _ (bt_back StB(bt_enc ds)(S3::r)));[reflexivity|].
   apply bt_carry_three;assumption.
 - destruct v as[|[|v]].
   + eapply(bt_compose 0 5 _ (bt_back StB(bt_enc ds)(S2::S1::r)));[reflexivity|].
     apply bt_carry_two_one;assumption.
   + exists 4,(false::ds),K1,(ctl r);split;[lia|];split.
     * unfold bt_main,bt_front;cbn[csteps cstep bt_tm ctape_move chd ctl bt_word bt_enc].
       destruct r as[|h r];[reflexivity|].
       cbn[all_blank]in Hr;apply andb_prop in Hr as[Hh _];apply sym_eqb_spec in Hh;subst h;reflexivity.
     * split;[apply bt_blank_tail;exact Hr|].
       unfold bt_valid;change((2*bt_value ds)mod 3=1);exact(bt_mod_twice _ _ Hv).
   + eapply(bt_compose(S(S v))5 _ (bt_back StB(bt_enc ds)(S2::S2::r)));[reflexivity|].
     apply bt_carry_two_two;assumption.
 - exists 4,(true::ds),K0,(ctl r);split;[lia|];split.
   + unfold bt_main,bt_front;cbn[csteps cstep bt_tm ctape_move chd ctl bt_word bt_enc].
     destruct r as[|h r];[reflexivity|].
     cbn[all_blank]in Hr;apply andb_prop in Hr as[Hh _];apply sym_eqb_spec in Hh;subst h;reflexivity.
   + split;[apply bt_blank_tail;exact Hr|].
     unfold bt_valid;change((1+2*bt_value ds)mod 3=0);exact(bt_mod_digit _ _ Hv).
Qed.
Lemma bt_returns : forall v N,exists t ds k r,
 N<=t /\ csteps(bt_tm v)t c0=Some(bt_main ds k r) /\ all_blank r=true /\bt_valid v ds k.
Proof.
 intros v N;induction N as[|N IH].
 - exists 0,[],K0,[];split;[lia|];split;[reflexivity|split;reflexivity].
 - destruct IH as(t&ds&k&r&Ht&E&Hr&Hv).
   destruct(bt_main_next v ds k r Hv Hr)as(j&ds'&k'&r'&Hj&E'&Hr'&Hv').
   exists(t+j),ds',k',r';split;[lia|];split;[rewrite csteps_add,E;exact E'|auto].
Qed.
Theorem bt_nonhalt : forall v,NonHalt(bt_tm v).
Proof. intro v;apply ore_total_nonhalt;intros q h;destruct q,h;eexists;reflexivity. Qed.
Theorem bt_A_recurrent : forall v N,exists t,N<=t /\VisitsAt(bt_tm v)StA t.
Proof.
 intros v N;destruct(bt_returns v N)as(t&ds&k&r&Ht&E&Hr&Hv).
 exists t;split;[exact Ht|];exists(lift(bt_main ds k r));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem bt_B_recurrent : forall v N,exists t,N<=t /\VisitsAt(bt_tm v)StB t.
Proof.
 intro v;apply ore_reaches_recurs.
 - intros q h;destruct q,h;eexists;reflexivity.
 - apply ore_auto_goal_sound;destruct v as[|[|v]];reflexivity.
Qed.
Theorem bt_state_zero : forall v,QHBound 0(bt_tm v).
Proof.
 intros v q s[_ Hquiet];destruct q.
 - destruct(bt_A_recurrent v(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(bt_B_recurrent v(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem bt_sound : forall v,NonHalt(bt_tm v) /\ QHBound 0(bt_tm v).
Proof. intro v;split;[apply bt_nonhalt|apply bt_state_zero]. Qed.
Print Assumptions bt_sound.
