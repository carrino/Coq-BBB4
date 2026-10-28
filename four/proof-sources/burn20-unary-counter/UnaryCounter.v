(** S011: a unary counter with an alternating terminal bit. The selected
    blank-headed return has nearest-first left word 2 1^(2n) 2. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census OneStateReach.
Import ListNotations.
Definition uc_tm:TM:=fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S0 DL StB
 |StA,S2=>mkTrans S2 DR StA |StA,S3=>mkTrans S2 DL StA
 |StB,S0=>mkTrans S2 DR StB |StB,S1=>mkTrans S2 DR StA
 |StB,S2=>mkTrans S3 DL StB |StB,S3=>mkTrans S1 DR StB end).
Definition uc_front q l r:cconf:=(q,(l,chd r,ctl r)).
Definition uc_back q l r:cconf:=(q,(ctl l,chd l,r)).
Definition uc_bit(b:bool):=if b then S1 else S0.
Definition uc_main n:cconf:=(StA,(S2::(repeat S1(2*n)++[S2]),S0,[])).
Definition uc_cost n:=8*n*n+12*n+7.
Definition uc_drain_cost k m:=2*k*k+4*m*k+5*k.
Fixpoint uc_flip n b:=match n with 0=>b|S n=>uc_flip n(negb b)end.
Lemma uc_repeat_shift : forall (x:Sym)n l,repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma uc_flip_double : forall n b,uc_flip(2*n)b=b.
Proof.
 induction n;intro b;[reflexivity|].
 replace(2*S n)with(S(S(2*n)))by lia;cbn[uc_flip];rewrite negb_involutive;apply IHn.
Qed.
Lemma uc_flip_odd : forall n b,uc_flip(S(2*n))b=negb b.
Proof. intros n b;cbn[uc_flip];apply uc_flip_double. Qed.
Lemma uc_A_threes : forall n l r,
 csteps uc_tm(3*n)(uc_front StA(S2::l)(repeat S3 n++r))=
 Some(uc_front StA(repeat S2 n++S2::l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(3*S n)with(3+3*n)by lia;rewrite csteps_add.
 change(csteps uc_tm(3*n)(uc_front StA(S2::S2::l)(repeat S3 n++r))=
 Some(uc_front StA(S2::(repeat S2 n++S2::l))r)).
 rewrite IHn,uc_repeat_shift;reflexivity.
Qed.
Lemma uc_B_twos : forall n l r,
 csteps uc_tm n(uc_back StB(repeat S2 n++l)r)=Some(uc_back StB l(repeat S3 n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app uc_back csteps cstep uc_tm ctape_move chd ctl].
 change(csteps uc_tm n(uc_back StB(repeat S2 n++l)(S3::r))=
 Some(uc_back StB l(S3::(repeat S3 n++r)))).
 rewrite IHn,uc_repeat_shift;reflexivity.
Qed.
Lemma uc_B_threes : forall n l r,
 csteps uc_tm n(uc_front StB l(repeat S3 n++r))=Some(uc_front StB(repeat S1 n++l)r).
Proof.
 induction n;intros l r;[reflexivity|].
 cbn[repeat app uc_front csteps cstep uc_tm ctape_move chd ctl].
 change(csteps uc_tm n(uc_front StB(S1::l)(repeat S3 n++r))=
 Some(uc_front StB(S1::(repeat S1 n++l))r)).
 rewrite IHn,uc_repeat_shift;reflexivity.
Qed.
Lemma uc_phase : forall n l r b,
 csteps uc_tm(n+2)(uc_front StA(repeat S2 n++S1::l)(uc_bit b::r))=
 Some(uc_front StA(S2::l)(repeat S3 n++uc_bit(negb b)::r)).
Proof.
 intros n l r b;replace(n+2)with(1+(n+1))by lia;rewrite csteps_add.
 assert(E:cstep uc_tm(uc_front StA(repeat S2 n++S1::l)(uc_bit b::r))=
 Some(uc_back StB(repeat S2 n++S1::l)(uc_bit(negb b)::r))).
 {destruct b;reflexivity. }
 rewrite csteps_1,E.
 change(csteps uc_tm(n+1)(uc_back StB(repeat S2 n++S1::l)(uc_bit(negb b)::r))=
 Some(uc_front StA(S2::l)(repeat S3 n++uc_bit(negb b)::r))).
 rewrite csteps_add,uc_B_twos;reflexivity.
Qed.
Theorem uc_iteration : forall k m l r b,
 csteps uc_tm(4*m+7)(uc_front StA(S2::(repeat S1(S k)++l))(repeat S3(S m)++uc_bit b::r))=
 Some(uc_front StA(S2::(repeat S1 k++l))(repeat S3(S(S m))++uc_bit(negb b)::r)).
Proof.
 intros k m l r b;replace(4*m+7)with(3*S m+(S(S m)+2))by lia.
 rewrite csteps_add,uc_A_threes.
 rewrite uc_repeat_shift.
 change(csteps uc_tm(S(S m)+2)(uc_front StA(repeat S2(S(S m))++S1::(repeat S1 k++l))(uc_bit b::r))=
 Some(uc_front StA(S2::(repeat S1 k++l))(repeat S3(S(S m))++uc_bit(negb b)::r))).
 apply uc_phase.
Qed.
Theorem uc_drain : forall k m l r b,
 csteps uc_tm(uc_drain_cost k m)
 (uc_front StA(S2::(repeat S1 k++l))(repeat S3(S m)++uc_bit b::r))=
 Some(uc_front StA(S2::l)(repeat S3(S(m+k))++uc_bit(uc_flip k b)::r)).
Proof.
 induction k;intros m l r b.
 - replace(uc_drain_cost 0 m)with 0 by(unfold uc_drain_cost;lia).
   rewrite Nat.add_0_r;reflexivity.
 - replace(uc_drain_cost(S k)m)with((4*m+7)+uc_drain_cost k(S m))by(unfold uc_drain_cost;nia).
   rewrite csteps_add,uc_iteration,IHk.
   replace(S m+k)with(m+S k)by lia;reflexivity.
Qed.
Theorem uc_finish : forall m r,
 csteps uc_tm(5*m+12)(uc_front StA[S2;S2](repeat S3(S m)++S0::r))=
 Some(uc_front StA(S2::(repeat S1(m+3)++[S2]))r).
Proof.
 intros m r;replace(5*m+12)with(3*S m+(1+((m+3)+(1+((m+3)+1)))))by lia.
 rewrite csteps_add,uc_A_threes.
 rewrite !uc_repeat_shift,app_nil_r.
 assert(El:repeat S2(m+3)=S2::S2::repeat S2(S m)).
 {replace(m+3)with(S(S(S m)))by lia;reflexivity. }
 rewrite <-El.
 change(csteps uc_tm(1+((m+3)+(1+((m+3)+1))))
 (uc_front StA(repeat S2(m+3))(S0::r))=
 Some(uc_front StA(S2::(repeat S1(m+3)++[S2]))r)).
 rewrite csteps_add.
 change(csteps uc_tm((m+3)+(1+((m+3)+1)))
 (uc_back StB(repeat S2(m+3))(S1::r))=
 Some(uc_front StA(S2::(repeat S1(m+3)++[S2]))r)).
 rewrite <-(app_nil_r(repeat S2(m+3)))at 1.
 rewrite csteps_add,uc_B_twos,csteps_add.
 change(csteps uc_tm((m+3)+1)(uc_front StB[S2](repeat S3(m+3)++S1::r))=
 Some(uc_front StA(S2::(repeat S1(m+3)++[S2]))r)).
 rewrite csteps_add,uc_B_threes;reflexivity.
Qed.
Theorem uc_main_next : forall n,csteps uc_tm(uc_cost n)(uc_main n)=Some(uc_main(S n)).
Proof.
 intro n;destruct n as[|n];[reflexivity|].
 replace(uc_cost(S n))with(3+(uc_drain_cost(S(2*n))0+(5*S(2*n)+12)))by(unfold uc_cost,uc_drain_cost;nia).
 unfold uc_main at 1;replace(2*S n)with(S(S(2*n)))by lia.
 rewrite csteps_add.
 change(csteps uc_tm(uc_drain_cost(S(2*n))0+(5*S(2*n)+12))
 (uc_front StA(S2::(repeat S1(S(2*n))++[S2]))(repeat S3(S 0)++uc_bit true::[]))=
 Some(uc_main(S(S n)))).
 rewrite csteps_add,uc_drain,uc_flip_odd.
 change(csteps uc_tm(5*S(2*n)+12)(uc_front StA[S2;S2](repeat S3(S(S(2*n)))++S0::[]))=
 Some(uc_main(S(S n)))).
 rewrite uc_finish;unfold uc_main.
 replace(S(2*n)+3)with(2*S(S n))by lia;reflexivity.
Qed.
Example uc_entry : csteps uc_tm 3 c0=Some(uc_main 0).
Proof. reflexivity. Qed.
Lemma uc_returns : forall N,exists t n,N<=t /\csteps uc_tm t c0=Some(uc_main n).
Proof.
 induction N as[|N IH].
 - exists 3,0;split;[lia|exact uc_entry].
 - destruct IH as(t&n&Ht&E);exists(t+uc_cost n),(S n);split.
   + unfold uc_cost;nia.
   + rewrite csteps_add,E;apply uc_main_next.
Qed.
Theorem uc_nonhalt : NonHalt uc_tm.
Proof. apply ore_total_nonhalt;intros q h;destruct q,h;eexists;reflexivity. Qed.
Theorem uc_A_recurrent : forall N,exists t,N<=t /\VisitsAt uc_tm StA t.
Proof.
 intro N;destruct(uc_returns N)as(t&n&Ht&E).
 exists t;split;[exact Ht|];exists(lift(uc_main n));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem uc_B_recurrent : forall N,exists t,N<=t /\VisitsAt uc_tm StB t.
Proof.
 intro N;destruct(uc_returns N)as(t&n&Ht&E).
 exists(t+1);split;[lia|];exists(lift(uc_back StB(S2::(repeat S1(2*n)++[S2]))[S1]));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem uc_state_zero : QHBound 0 uc_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(uc_A_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(uc_B_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem uc_sound : NonHalt uc_tm /\QHBound 0 uc_tm.
Proof. split;[exact uc_nonhalt|exact uc_state_zero]. Qed.
Print Assumptions uc_sound.
