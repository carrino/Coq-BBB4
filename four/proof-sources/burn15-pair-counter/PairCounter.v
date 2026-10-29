(** A two-block counter: (13)^a (32)^m, viewed nearest-first to the left
    of an A0 head with a blank right tail. *)
From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement Spec CTape Census.
Import ListNotations.

Definition bp_tm : TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StB
 |StA,S2=>mkTrans S0 DR StA |StA,S3=>mkTrans S0 DL StA
 |StB,S0=>mkTrans S2 DR StB |StB,S1=>mkTrans S3 DL StB
 |StB,S2=>mkTrans S3 DR StB |StB,S3=>mkTrans S1 DR StA end).
Definition bp_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition bp_back q l r:cconf := (q,(ctl l,chd l,r)).
Fixpoint bp_pairs (x y:Sym)n := match n with 0=>[]|S n=>x::y::bp_pairs x y n end.
Definition bp_main a m:cconf := (StA,(bp_pairs S1 S3 a++bp_pairs S3 S2 m,S0,[])).

Lemma bp_pair_shift : forall x y n l,
 bp_pairs x y n++x::y::l=x::y::(bp_pairs x y n++l).
Proof. intros x y n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma bp_rotate : forall n,bp_pairs S2 S3 n++[S2]=S2::bp_pairs S3 S2 n.
Proof. induction n;cbn;[reflexivity|now rewrite IHn]. Qed.

Lemma bp_left_pairs : forall n l r,
 csteps bp_tm(4*n)(bp_back StB(bp_pairs S1 S3 n++l)r)=
 Some(bp_back StB l(bp_pairs S2 S0 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(4*S n)with(4+4*n)by lia;rewrite csteps_add.
 change(csteps bp_tm(4*n)(bp_back StB(bp_pairs S1 S3 n++l)(S2::S0::r))=
 Some(bp_back StB l(S2::S0::(bp_pairs S2 S0 n++r)))).
 rewrite IHn,bp_pair_shift;reflexivity.
Qed.
Lemma bp_right_A : forall n l r,
 csteps bp_tm(6*n)(bp_front StA l(bp_pairs S2 S0 n++r))=
 Some(bp_front StA(bp_pairs S1 S3 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(6*S n)with(6+6*n)by lia;rewrite csteps_add.
 change(csteps bp_tm(6*n)(bp_front StA(S1::S3::l)(bp_pairs S2 S0 n++r))=
 Some(bp_front StA(S1::S3::(bp_pairs S1 S3 n++l))r)).
 rewrite IHn,bp_pair_shift;reflexivity.
Qed.
Lemma bp_right_B : forall n l r,
 csteps bp_tm(2*n)(bp_front StB l(bp_pairs S2 S0 n++r))=
 Some(bp_front StB(bp_pairs S2 S3 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(2*S n)with(2+2*n)by lia;rewrite csteps_add.
 change(csteps bp_tm(2*n)(bp_front StB(S2::S3::l)(bp_pairs S2 S0 n++r))=
 Some(bp_front StB(S2::S3::(bp_pairs S2 S3 n++l))r)).
 rewrite IHn,bp_pair_shift;reflexivity.
Qed.

Theorem bp_phase_zero : forall a l r,
 csteps bp_tm(10*a+2)(StA,(bp_pairs S1 S3 a++S3::S2::l,S0,r))=
 Some(StA,(bp_pairs S1 S3 a++S1::S2::l,S1,r)).
Proof.
 intros a l r;replace(10*a+2)with(1+(4*a+(1+6*a)))by lia.
 rewrite csteps_add.
 change(csteps bp_tm(4*a+(1+6*a))
   (bp_back StB(bp_pairs S1 S3 a++S3::S2::l)(S1::r))=
 Some(StA,(bp_pairs S1 S3 a++S1::S2::l,S1,r))).
 rewrite csteps_add,bp_left_pairs,csteps_add.
 change(csteps bp_tm(6*a)(bp_front StA(S1::S2::l)(bp_pairs S2 S0 a++S1::r))=
 Some(bp_front StA(bp_pairs S1 S3 a++S1::S2::l)(S1::r))).
 apply bp_right_A.
Qed.
Theorem bp_phase_one : forall a l r,
 csteps bp_tm(10*a+4)(StA,(bp_pairs S1 S3 a++S1::S2::l,S1,r))=
 Some(StA,(bp_pairs S1 S3(S a)++l,S2,r)).
Proof.
 intros a l r;replace(10*a+4)with(1+(4*a+(3+6*a)))by lia.
 rewrite csteps_add.
 change(csteps bp_tm(4*a+(3+6*a))
   (bp_back StB(bp_pairs S1 S3 a++S1::S2::l)(S2::r))=
 Some(StA,(bp_pairs S1 S3(S a)++l,S2,r))).
 rewrite csteps_add,bp_left_pairs,csteps_add.
 change(csteps bp_tm(6*a)(bp_front StA(S1::S3::l)(bp_pairs S2 S0 a++S2::r))=
 Some(bp_front StA(S1::S3::(bp_pairs S1 S3 a++l))(S2::r))).
 rewrite bp_right_A,bp_pair_shift;reflexivity.
Qed.
Lemma bp_finish : forall l,
 csteps bp_tm 6(StA,(l,S2,[]))=Some(StA,(S1::S3::l,S0,[])).
Proof. intro l;reflexivity. Qed.

Theorem bp_nonempty : forall a m,
 csteps bp_tm(20*a+12)(bp_main a(S m))=Some(bp_main(a+2)m).
Proof.
 intros a m;unfold bp_main;cbn[bp_pairs].
 replace(20*a+12)with((10*a+2)+((10*a+4)+6))by lia.
 rewrite csteps_add,bp_phase_zero,csteps_add,bp_phase_one,bp_finish.
 replace(a+2)with(S(S a))by lia;reflexivity.
Qed.
Theorem bp_empty : forall a,
 csteps bp_tm(6*a+5)(bp_main a 0)=Some(bp_main 1 a).
Proof.
 intro a;unfold bp_main;cbn[bp_pairs];rewrite app_nil_r.
 replace(6*a+5)with(1+(4*a+(1+(2*a+3))))by lia;rewrite csteps_add.
 change(csteps bp_tm(4*a+(1+(2*a+3)))(bp_back StB(bp_pairs S1 S3 a)[S1])=
 Some(StA,(S1::S3::bp_pairs S3 S2 a,S0,[]))).
 rewrite <-(app_nil_r(bp_pairs S1 S3 a))at 1.
 rewrite csteps_add,bp_left_pairs,csteps_add.
 change(csteps bp_tm(2*a+3)(bp_front StB[S2](bp_pairs S2 S0 a++[S1]))=
 Some(StA,(S1::S3::bp_pairs S3 S2 a,S0,[]))).
 rewrite csteps_add,bp_right_B,bp_rotate;reflexivity.
Qed.

Theorem bp_main_next : forall a m,exists k a' m',0<k /\
 csteps bp_tm k(bp_main a m)=Some(bp_main a' m').
Proof.
 intros a m;destruct m.
 - exists(6*a+5),1,a;split;[lia|apply bp_empty].
 - exists(20*a+12),(a+2),m;split;[lia|apply bp_nonempty].
Qed.
Lemma bp_returns : forall N,exists k a m,N<=k /\
 csteps bp_tm k c0=Some(bp_main a m).
Proof.
 induction N as[|N IH].
 - exists 0,0,0;split;[lia|reflexivity].
 - destruct IH as(k&a&m&Hk&E).
   destruct(bp_main_next a m)as(j&a'&m'&Hj&E').
   exists(k+j),a',m';split;[lia|];rewrite csteps_add,E;exact E'.
Qed.
Theorem bp_nonhalt : NonHalt bp_tm.
Proof.
 intros n Hnone;destruct(bp_returns n)as(k&a&m&Hk&E).
 pose proof(csteps_lift bp_tm k c0(bp_main a m)E)as Hrun;rewrite lift_c0 in Hrun.
 destruct(stepn_prefix bp_tm n k InitES(lift(bp_main a m))Hk Hrun)as(c&Ec&_);congruence.
Qed.
Theorem bp_A_recurrent : forall N,exists k,N<=k /\ VisitsAt bp_tm StA k.
Proof.
 intro N;destruct(bp_returns N)as(k&a&m&Hk&E).
 exists k;split;[exact Hk|];exists(lift(bp_main a m));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem bp_B_recurrent : forall N,exists k,N<=k /\ VisitsAt bp_tm StB k.
Proof.
 intro N;destruct(bp_returns N)as(k&a&m&Hk&E).
 exists(k+1);split;[lia|].
 exists(lift(bp_back StB(bp_pairs S1 S3 a++bp_pairs S3 S2 m)[S1]));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem bp_state_zero : QHBound 0 bp_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(bp_A_recurrent(S s))as(k&Hk&Hv);exfalso;apply(Hquiet k);[lia|exact Hv].
 - destruct(bp_B_recurrent(S s))as(k&Hk&Hv);exfalso;apply(Hquiet k);[lia|exact Hv].
Qed.
Theorem bp_sound : NonHalt bp_tm /\ QHBound 0 bp_tm.
Proof. split;[exact bp_nonhalt|exact bp_state_zero]. Qed.
Print Assumptions bp_sound.
