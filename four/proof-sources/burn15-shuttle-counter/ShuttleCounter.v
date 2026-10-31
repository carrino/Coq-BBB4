(** A guarded three-parameter block invariant. The first two parameters
    cannot both vanish; that condition excludes a real boundary exception. *)
From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement Spec CTape Census.
Import ListNotations.

Definition bs_tm : TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StA
 |StA,S2=>mkTrans S3 DL StB |StA,S3=>mkTrans S0 DR StB
 |StB,S0=>mkTrans S3 DR StB |StB,S1=>mkTrans S3 DR StA
 |StB,S2=>mkTrans S2 DR StA |StB,S3=>mkTrans S0 DR StA end).
Definition bs_front q l r:cconf := (q,(l,chd r,ctl r)).
Fixpoint bs_pairs n := match n with 0=>[]|S n=>S2::S0::bs_pairs n end.
Definition bs_main a m k:cconf :=
 (StA,(repeat S3(2*a)++bs_pairs m++S0::repeat S3 k,S0,[])).

Lemma bs_repeat_shift : forall (x:Sym)n l,
 repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma bs_pair_shift : forall n l,
 bs_pairs n++S2::S0::l=S2::S0::(bs_pairs n++l).
Proof. induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.

Lemma bs_carry : forall n l r,
 csteps bs_tm(3*n)(StA,(S0::(repeat S3 n++l),S1,r))=
 Some(StA,(S0::l,S1,repeat S2 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(3*S n)with(3+3*n)by lia;rewrite csteps_add.
 change(csteps bs_tm(3*n)(StA,(S0::(repeat S3 n++l),S1,S2::r))=
 Some(StA,(S0::l,S1,S2::(repeat S2 n++r)))).
 rewrite IHn,bs_repeat_shift;reflexivity.
Qed.
Lemma bs_right_twos : forall n l r,
 csteps bs_tm(3*n)(bs_front StA(S0::l)(repeat S2 n++r))=
 Some(bs_front StA(S0::(repeat S3 n++l))r).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(3*S n)with(3+3*n)by lia;rewrite csteps_add.
 change(csteps bs_tm(3*n)(bs_front StA(S0::S3::l)(repeat S2 n++r))=
 Some(bs_front StA(S0::S3::(repeat S3 n++l))r)).
 rewrite IHn,bs_repeat_shift;reflexivity.
Qed.
Lemma bs_right_pairs : forall n l r,
 csteps bs_tm(4*n)(bs_front StA(S2::l)(repeat S2(2*n)++r))=
 Some(bs_front StA(bs_pairs n++S2::l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(4*S n)with(4+4*n)by lia;rewrite csteps_add.
 replace(2*S n)with(S(S(2*n)))by lia.
 change(csteps bs_tm(4*n)(bs_front StA(S2::S0::S2::l)(repeat S2(2*n)++r))=
 Some(bs_front StA(S2::S0::(bs_pairs n++S2::l))r)).
 rewrite IHn,bs_pair_shift;reflexivity.
Qed.

Theorem bs_nonempty_start : forall a l r,
 csteps bs_tm(6*a+3)(StA,(repeat S3(2*a)++S2::S0::l,S0,r))=
 Some(bs_front StA(S0::l)(repeat S2(2*a+2)++r)).
Proof.
 intros a l r;destruct a;[reflexivity|].
 replace(6*S a+3)with(2+(3*(2*a+1)+4))by lia;rewrite csteps_add.
 replace(2*S a)with(S(2*a+1))at 1 by lia.
 change(csteps bs_tm(3*(2*a+1)+4)
   (StA,(S0::(repeat S3(2*a+1)++S2::S0::l),S1,r))=
 Some(bs_front StA(S0::l)(repeat S2(2*S a+2)++r))).
 rewrite csteps_add,bs_carry.
 replace(2*S a+2)with(S(S(S(2*a+1))))by lia;reflexivity.
Qed.
Theorem bs_empty_start : forall a l r,
 csteps bs_tm(6*S a+3)(StA,(repeat S3(2*S a)++S0::l,S0,r))=
 Some(bs_front StA(S3::S3::l)(repeat S2(2*S a)++r)).
Proof.
 intros a l r.
 replace(6*S a+3)with(2+(3*(2*a+1)+4))by lia;rewrite csteps_add.
 replace(2*S a)with(S(2*a+1))by lia.
 change(csteps bs_tm(3*(2*a+1)+4)
   (StA,(S0::(repeat S3(2*a+1)++S0::l),S1,r))=
 Some(bs_front StA(S3::S3::l)(repeat S2(S(2*a+1))++r))).
 rewrite csteps_add,bs_carry;reflexivity.
Qed.
Lemma bs_finish : forall l,
 csteps bs_tm 3(StA,(S0::l,S0,[]))=Some(StA,(S3::S3::l,S0,[])).
Proof. intro l;reflexivity. Qed.

Theorem bs_nonempty : forall a m k,
 csteps bs_tm(12*a+12)(bs_main a(S m)k)=Some(bs_main(a+2)m k).
Proof.
 intros a m k;unfold bs_main;cbn[bs_pairs app].
 replace(12*a+12)with((6*a+3)+(3*(2*a+2)+3))by lia.
 rewrite csteps_add,bs_nonempty_start,csteps_add,bs_right_twos.
 change(csteps bs_tm 3(StA,(S0::(repeat S3(2*a+2)++bs_pairs m++S0::repeat S3 k),S0,[]))=
 Some(StA,(repeat S3(2*(a+2))++bs_pairs m++S0::repeat S3 k,S0,[]))).
 rewrite bs_finish;replace(2*(a+2))with(S(S(2*a+2)))by lia;reflexivity.
Qed.
Theorem bs_empty : forall a k,
 csteps bs_tm(10*S a+3)(bs_main(S a)0 k)=Some(bs_main 0(S a)(S k)).
Proof.
 intros a k;unfold bs_main;cbn[bs_pairs app].
 replace(10*S a+3)with((6*S a+3)+(4+4*a))by lia.
 rewrite csteps_add,bs_empty_start,csteps_add.
 replace(2*S a)with(S(S(2*a)))by lia.
 change(csteps bs_tm(4*a)
   (bs_front StA(S2::S0::S0::S3::repeat S3 k)(repeat S2(2*a)++[]))=
 Some(bs_front StA(S2::S0::(bs_pairs a++S0::S3::repeat S3 k))[])).
 rewrite bs_right_pairs,bs_pair_shift;reflexivity.
Qed.

Theorem bs_main_next : forall a m k,0<a+m ->
 exists j a' m' k',0<j /\ 0<a'+m' /\
 csteps bs_tm j(bs_main a m k)=Some(bs_main a' m' k').
Proof.
 intros a m k H;destruct m.
 - destruct a;[lia|].
   exists(10*S a+3),0,(S a),(S k);split;[lia|];split;[lia|apply bs_empty].
 - exists(12*a+12),(a+2),m,k;split;[lia|];split;[lia|apply bs_nonempty].
Qed.
Example bs_entry : csteps bs_tm 16 c0=Some(bs_main 0 1 1).
Proof. reflexivity. Qed.
Lemma bs_returns : forall N,exists t a m k,N<=t /\ 0<a+m /\
 csteps bs_tm t c0=Some(bs_main a m k).
Proof.
 induction N as[|N IH].
 - exists 16,0,1,1;split;[lia|];split;[lia|exact bs_entry].
 - destruct IH as(t&a&m&k&Ht&Hgood&E).
   destruct(bs_main_next a m k Hgood)as(j&a'&m'&k'&Hj&Hgood'&E').
   exists(t+j),a',m',k';split;[lia|];split;[exact Hgood'|];rewrite csteps_add,E;exact E'.
Qed.
Theorem bs_nonhalt : NonHalt bs_tm.
Proof.
 intros n Hnone;destruct(bs_returns n)as(t&a&m&k&Ht&_&E).
 pose proof(csteps_lift bs_tm t c0(bs_main a m k)E)as Hrun;rewrite lift_c0 in Hrun.
 destruct(stepn_prefix bs_tm n t InitES(lift(bs_main a m k))Ht Hrun)as(c&Ec&_);congruence.
Qed.
Theorem bs_A_recurrent : forall N,exists t,N<=t /\ VisitsAt bs_tm StA t.
Proof.
 intro N;destruct(bs_returns N)as(t&a&m&k&Ht&_&E).
 exists t;split;[exact Ht|];exists(lift(bs_main a m k));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem bs_B_recurrent : forall N,exists t,N<=t /\ VisitsAt bs_tm StB t.
Proof.
 intro N;destruct(bs_returns N)as(t&a&m&k&Ht&_&E).
 exists(t+1);split;[lia|].
 exists(lift(StB,(ctl(repeat S3(2*a)++bs_pairs m++S0::repeat S3 k),
   chd(repeat S3(2*a)++bs_pairs m++S0::repeat S3 k),[S1])));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem bs_state_zero : QHBound 0 bs_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(bs_A_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(bs_B_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem bs_sound : NonHalt bs_tm /\ QHBound 0 bs_tm.
Proof. split;[exact bs_nonhalt|exact bs_state_zero]. Qed.
Print Assumptions bs_sound.
