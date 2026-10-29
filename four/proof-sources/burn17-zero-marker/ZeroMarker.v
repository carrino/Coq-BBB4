(** A binary increment with one moving zero marker. The suffix beyond the
    marker contains only twos, and its length plus the prefix length is even.
    The modulo-three checksum alone is insufficient without this grammar. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census.
Import ListNotations.

Definition zm_tm : TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StB
 |StA,S2=>mkTrans S0 DL StB |StA,S3=>mkTrans S1 DR StA
 |StB,S0=>mkTrans S2 DR StB |StB,S1=>mkTrans S2 DR StA
 |StB,S2=>mkTrans S3 DL StB |StB,S3=>mkTrans S0 DR StA end).
Definition zm_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition zm_back q l r:cconf := (q,(ctl l,chd l,r)).
Definition zm_rot h := match h with S0=>S1|S1=>S2|_=>S0 end.
Definition zm_of_nat n := match n mod 3 with 0=>S0|1=>S1|_=>S2 end.
Fixpoint zm_value(l:list Sym):nat := match l with
 |[]=>0|h::l=>(match h with S2=>1|_=>0 end)+2*zm_value l end.
Definition zm_head l := zm_of_nat(zm_value l).
Fixpoint zm_bits(ds:list bool):list Sym := match ds with
 |[]=>[]|d::ds=>(if d then S2 else S1)::zm_bits ds end.
Inductive zm_word : list Sym -> Prop :=
 |zm_max : forall n,zm_word(repeat S2(2*n))
 |zm_mark : forall ds b e,0<b -> length ds+b=2*e ->
   zm_word(zm_bits ds++S0::repeat S2 b).
Definition zm_main l:cconf := (StA,(l,zm_head l,[])).

Lemma zm_of_nat_good : forall n,zm_of_nat n=S0 \/ zm_of_nat n=S1 \/ zm_of_nat n=S2.
Proof. intro n;unfold zm_of_nat;destruct(n mod 3)as[|[|r]];auto. Qed.
Lemma zm_of_nat_succ : forall n,zm_of_nat(S n)=zm_rot(zm_of_nat n).
Proof.
 intro n;unfold zm_of_nat.
 assert(Hr:n mod 3<3)by(apply Nat.mod_upper_bound;lia).
 replace(S n)with(n+1)by lia;rewrite Nat.add_mod by lia.
 destruct(n mod 3)as[|[|[|r]]];cbn[zm_rot];try reflexivity;lia.
Qed.
Lemma zm_value_nil_zero : forall l,zm_value(l++[S0])=zm_value l.
Proof. induction l as[|h l IH];cbn;[reflexivity|now rewrite IH]. Qed.
Lemma zm_value_increment : forall n l,
 zm_value(repeat S1 n++S2::l)=S(zm_value(repeat S2 n++S1::l)).
Proof. induction n;intro l;cbn[repeat app zm_value];[lia|rewrite IHn;lia]. Qed.
Lemma zm_value_marker_shift : forall n l,
 zm_value(repeat S1 n++S0::S2::l)=S(zm_value(repeat S2(S n)++S0::l)).
Proof.
 induction n;intro l;cbn[repeat app zm_value];[lia|].
 change(2*zm_value(repeat S1 n++S0::S2::l)=S(1+2*zm_value(repeat S2(S n)++S0::l))).
 rewrite IHn;lia.
Qed.
Lemma zm_value_max_mod : forall n,zm_value(repeat S2(2*n))mod 3=0.
Proof.
 induction n;[reflexivity|].
 replace(2*S n)with(S(S(2*n)))by lia.
 change((1+2*(1+2*zm_value(repeat S2(2*n))))mod 3=0).
 replace(1+2*(1+2*zm_value(repeat S2(2*n))))with(3+4*zm_value(repeat S2(2*n)))by lia.
 rewrite Nat.add_mod,Nat.mul_mod by lia;rewrite IHn;reflexivity.
Qed.
Lemma zm_head_max : forall n,zm_head(repeat S2(2*n))=S0.
Proof. intro n;unfold zm_head,zm_of_nat;rewrite zm_value_max_mod;reflexivity. Qed.
Lemma zm_head_marker_even : forall n,zm_head(S0::repeat S2(2*n))=S0.
Proof.
 intro n;unfold zm_head,zm_of_nat;change((match(2*zm_value(repeat S2(2*n)))mod 3 with 0=>S0|1=>S1|_=>S2 end)=S0).
 rewrite Nat.mul_mod by lia;rewrite zm_value_max_mod;reflexivity.
Qed.
Lemma zm_bits_app : forall ds es,zm_bits(ds++es)=zm_bits ds++zm_bits es.
Proof. induction ds;intro es;cbn;[reflexivity|now rewrite IHds]. Qed.
Lemma zm_bits_repeat : forall b n,zm_bits(repeat b n)=repeat(if b then S2 else S1)n.
Proof. intros b n;induction n;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma zm_bits_length : forall ds,length(zm_bits ds)=length ds.
Proof. induction ds;cbn;congruence. Qed.
Lemma zm_repeat_shift : forall (x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.

Lemma zm_left_twos : forall n l r,
 csteps zm_tm n(zm_back StB(repeat S2 n++l)r)=Some(zm_back StB l(repeat S3 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app zm_back csteps cstep zm_tm ctape_move chd ctl].
 change(csteps zm_tm n(zm_back StB(repeat S2 n++l)(S3::r))=
 Some(zm_back StB l(S3::(repeat S3 n++r)))).
 rewrite IHn,zm_repeat_shift;reflexivity.
Qed.
Lemma zm_right_threes : forall n l r,
 csteps zm_tm n(zm_front StA l(repeat S3 n++r))=Some(zm_front StA(repeat S1 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app zm_front csteps cstep zm_tm ctape_move chd ctl].
 change(csteps zm_tm n(zm_front StA(S1::l)(repeat S3 n++r))=
 Some(zm_front StA(S1::(repeat S1 n++l))r)).
 rewrite IHn,zm_repeat_shift;reflexivity.
Qed.
Lemma zm_start : forall l r h,h=S0 \/ h=S1 \/ h=S2 ->
 csteps zm_tm 1(StA,(l,h,r))=Some(zm_back StB l(zm_rot h::r)).
Proof. intros l r h[H|[H|H]];subst h;reflexivity. Qed.
Theorem zm_increment : forall n l r h,h=S0 \/ h=S1 \/ h=S2 ->
 csteps zm_tm(2*n+2)(StA,(repeat S2 n++S1::l,h,r))=
 Some(StA,(repeat S1 n++S2::l,zm_rot h,r)).
Proof.
 intros n l r h Hh;replace(2*n+2)with(1+(n+(1+n)))by lia.
 rewrite csteps_add,zm_start by exact Hh.
 rewrite csteps_add,zm_left_twos,csteps_add.
 change(csteps zm_tm n(zm_front StA(S2::l)(repeat S3 n++zm_rot h::r))=
 Some(zm_front StA(repeat S1 n++S2::l)(zm_rot h::r))).
 apply zm_right_threes.
Qed.
Theorem zm_marker_shift : forall n l r h,h=S0 \/ h=S1 \/ h=S2 ->
 csteps zm_tm(2*S n+2)(StA,(repeat S2(S n)++S0::l,h,r))=
 Some(StA,(repeat S1 n++S0::S2::l,zm_rot h,r)).
Proof.
 intros n l r h Hh;replace(2*S n+2)with(1+(S n+(2+n)))by lia.
 rewrite csteps_add,zm_start by exact Hh.
 rewrite csteps_add,zm_left_twos,csteps_add.
 change(csteps zm_tm n(zm_front StA(S0::S2::l)(repeat S3 n++zm_rot h::r))=
 Some(zm_front StA(repeat S1 n++S0::S2::l)(zm_rot h::r))).
 apply zm_right_threes.
Qed.
Theorem zm_outer_carry : forall n h,h=S0 \/ h=S1 \/ h=S2 ->
 csteps zm_tm(2*S n+2)(StA,(repeat S2(S n),h,[]))=
 Some(StA,(repeat S1 n++[S0;S2],zm_rot h,[])).
Proof.
 intros n h Hh;replace(2*S n+2)with(1+(S n+(2+n)))by lia.
 rewrite csteps_add,zm_start by exact Hh.
 rewrite <-(app_nil_r(repeat S2(S n)))at 1.
 rewrite csteps_add,zm_left_twos,csteps_add.
 change(csteps zm_tm n(zm_front StA[S0;S2](repeat S3 n++[zm_rot h]))=
 Some(zm_front StA(repeat S1 n++[S0;S2])[zm_rot h])).
 apply zm_right_threes.
Qed.
Lemma zm_expand : forall l,csteps zm_tm 3(StA,(S0::l,S0,[]))=Some(StA,(S2::S2::l,S0,[])).
Proof. reflexivity. Qed.
Example zm_entry : csteps zm_tm 3 c0=Some(zm_main[S2;S2]).
Proof. reflexivity. Qed.

Lemma zm_decompose : forall ds,
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
Theorem zm_main_next : forall l,zm_word l ->
 exists k l',0<k /\ zm_word l' /\ csteps zm_tm k(zm_main l)=Some(zm_main l').
Proof.
 intros l Hw;destruct Hw as[n|ds b e Hb He].
 - destruct n as[|n].
   + exists 3,[S2;S2];split;[lia|];split;[exact(zm_max 1)|exact zm_entry].
   + set(k:=2*S n-1).
     assert(Hlen:S k=2*S n)by(unfold k;lia).
     set(l':=repeat S1 k++[S0;S2]).
     exists(2*S k+2),l';split;[lia|];split.
     * unfold l';rewrite <-(zm_bits_repeat false k).
       apply(zm_mark(repeat false k)1(S n));[lia|rewrite repeat_length;lia].
     * unfold zm_main,l'.
       assert(Hval:zm_value(repeat S1 k++[S0;S2])=S(zm_value(repeat S2(S k)))).
       {rewrite <-(zm_value_nil_zero(repeat S2(S k))),<-zm_value_marker_shift;reflexivity. }
       unfold zm_head at 2;rewrite Hval,zm_of_nat_succ,<-Hlen.
       apply zm_outer_carry;apply zm_of_nat_good.
 - destruct(zm_decompose ds)as[(n&E)|(n&tail&E)];subst ds.
   + rewrite repeat_length in He;rewrite zm_bits_repeat.
     destruct n as[|n].
     * cbn[repeat app]in *;replace b with(2*e)in * by lia.
       exists 3,(repeat S2(2*S e));split;[lia|];split;[apply zm_max|].
       unfold zm_main;rewrite zm_head_marker_even,zm_head_max.
       replace(2*S e)with(S(S(2*e)))by lia;apply zm_expand.
     * set(l':=repeat S1 n++S0::repeat S2(S b)).
       exists(2*S n+2),l';split;[lia|];split.
       -- unfold l';rewrite <-(zm_bits_repeat false n).
          apply(zm_mark(repeat false n)(S b)e);[lia|rewrite repeat_length;lia].
       -- unfold zm_main,l'.
          change(csteps zm_tm(2*S n+2)(StA,(repeat S2(S n)++S0::repeat S2 b,zm_head(repeat S2(S n)++S0::repeat S2 b),[]))=
           Some(StA,(repeat S1 n++S0::S2::repeat S2 b,zm_head(repeat S1 n++S0::S2::repeat S2 b),[]))).
          unfold zm_head at 2;rewrite zm_value_marker_shift,zm_of_nat_succ.
          apply zm_marker_shift;apply zm_of_nat_good.
   + set(ds':=repeat false n++true::tail).
     exists(2*n+2),(zm_bits ds'++S0::repeat S2 b);split;[lia|];split.
     * apply(zm_mark ds' b e);[exact Hb|].
       unfold ds';rewrite app_length,repeat_length;rewrite app_length,repeat_length in He;cbn[length]in *;lia.
     * unfold zm_main,ds';rewrite !zm_bits_app,!zm_bits_repeat;cbn[zm_bits].
       rewrite <-!app_assoc;cbn[app].
       unfold zm_head at 2;rewrite zm_value_increment,zm_of_nat_succ.
       apply zm_increment;apply zm_of_nat_good.
Qed.

Lemma zm_marker_at_boundary_safe : forall b,zm_word(S0::repeat S2 b)->zm_head(S0::repeat S2 b)=S0.
Proof.
 intros b Hw;remember(S0::repeat S2 b)as l eqn:E.
 destruct Hw as[n|ds b' e Hb He].
 - destruct n;cbn[repeat]in E;discriminate.
 - destruct ds as[|d ds].
   + cbn[zm_bits app length]in *.
     replace b' with(2*e)by lia;apply zm_head_marker_even.
   + destruct d;cbn[zm_bits app]in E;discriminate.
Qed.

Lemma zm_returns : forall N,exists k l,N<=k /\ zm_word l /\ csteps zm_tm k c0=Some(zm_main l).
Proof.
 induction N as[|N IH].
 - exists 3,[S2;S2];split;[lia|];split;[exact(zm_max 1)|exact zm_entry].
 - destruct IH as(k&l&Hk&Hw&E).
   destruct(zm_main_next l Hw)as(j&l'&Hj&Hw'&E').
   exists(k+j),l';split;[lia|];split;[exact Hw'|];rewrite csteps_add,E;exact E'.
Qed.
Theorem zm_nonhalt : NonHalt zm_tm.
Proof.
 intros n Hnone;destruct(zm_returns n)as(k&l&Hk&_&E).
 pose proof(csteps_lift zm_tm k c0(zm_main l)E)as Hrun;rewrite lift_c0 in Hrun.
 destruct(stepn_prefix zm_tm n k InitES(lift(zm_main l))Hk Hrun)as(c&Ec&_);congruence.
Qed.
Theorem zm_A_recurrent : forall N,exists k,N<=k /\ VisitsAt zm_tm StA k.
Proof.
 intro N;destruct(zm_returns N)as(k&l&Hk&_&E).
 exists k;split;[exact Hk|];exists(lift(zm_main l));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem zm_B_recurrent : forall N,exists k,N<=k /\ VisitsAt zm_tm StB k.
Proof.
 intro N;destruct(zm_returns N)as(k&l&Hk&_&E).
 exists(k+1);split;[lia|];exists(lift(zm_back StB l[zm_rot(zm_head l)]));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;apply zm_start;apply zm_of_nat_good.
Qed.
Theorem zm_state_zero : QHBound 0 zm_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(zm_A_recurrent(S s))as(k&Hk&Hv);exfalso;apply(Hquiet k);[lia|exact Hv].
 - destruct(zm_B_recurrent(S s))as(k&Hk&Hv);exfalso;apply(Hquiet k);[lia|exact Hv].
Qed.
Theorem zm_sound : NonHalt zm_tm /\ QHBound 0 zm_tm.
Proof. split;[exact zm_nonhalt|exact zm_state_zero]. Qed.
Print Assumptions zm_sound.
