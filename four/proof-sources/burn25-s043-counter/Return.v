(** The even-one-run family has the closed return n -> 3n+3. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census.
From BBB24Burn25S043Counter Require Import Core.
Import ListNotations.
Lemma sg_drain : forall b a r,
 csteps sg_tm(3*b*b+(2*a+5)*b)(sg_left a(repeat S1 b++r))=
 Some(sg_left(a+3*b)r).
Proof.
 induction b as[|b IH];intros a r.
 - replace(3*0*0+(2*a+5)*0)with 0 by lia;replace(a+3*0)with a by lia;reflexivity.
 - replace(3*S b*S b+(2*a+5)*S b)with
   ((2*a+8)+(3*b*b+(2*(a+3)+5)*b))by nia.
   cbn[repeat app];rewrite csteps_add,sg_consume_one,IH.
   replace(a+3+3*b)with(a+3*S b)by lia;reflexivity.
Qed.
Theorem sg_main_next : forall n,
 csteps sg_tm(12*n*n+66*n+84)(sg_M n)=Some(sg_M(3*n+3)).
Proof.
 intro n;replace(12*n*n+66*n+84)with
 ((3*(2*n)*(2*n)+(2*5+5)*(2*n))+(12*(3*n+2)+60))by nia.
 unfold sg_M,sg_C;rewrite csteps_add,sg_drain.
 replace(5+3*(2*n))with(2*(3*n+2)+1)by lia.
 change(csteps sg_tm(12*(3*n+2)+60)(sg_C(2*(3*n+2)+1)0)=
 Some(sg_C 5(2*(3*n+3)))).
 rewrite sg_odd_reset;replace(2*(3*n+2)+2)with(2*(3*n+3))by lia;reflexivity.
Qed.
Lemma sg_entry : csteps sg_tm 100852 c0=Some(sg_M 254).
Proof. vm_compute;reflexivity. Qed.
Lemma sg_returns : forall N,exists t n,N<=t /\csteps sg_tm t c0=Some(sg_M n).
Proof.
 intro N;induction N as[|N IH].
 - exists 100852,254;split;[lia|exact sg_entry].
 - destruct IH as(t&n&Ht&E);exists(t+(12*n*n+66*n+84)),(3*n+3);split;[nia|].
   rewrite csteps_add,E;apply sg_main_next.
Qed.
Theorem sg_A_recurrent : forall N,exists t,N<=t /\VisitsAt sg_tm StA t.
Proof.
 intro N;destruct(sg_returns N)as(t&n&Ht&E);exists t;split;[exact Ht|].
 exists(lift(sg_M n));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem sg_B_recurrent : forall N,exists t,N<=t /\VisitsAt sg_tm StB t.
Proof.
 intro N;destruct(sg_returns N)as(t&n&Ht&E);exists(t+1);split;[lia|].
 exists(lift(StB,([],S0,S1::(repeat S2 5++repeat S1(2*n)++[S0;S1]))));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem sg_nonhalt : NonHalt sg_tm.
Proof.
 intros n Hnone;destruct(sg_returns n)as(t&k&Ht&E).
 pose proof(csteps_lift sg_tm t c0(sg_M k)E)as Er;rewrite lift_c0 in Er.
 destruct(stepn_prefix sg_tm n t InitES(lift(sg_M k))Ht Er)as(c&Ec&_);congruence.
Qed.
Theorem sg_state_zero : QHBound 0 sg_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(sg_A_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(sg_B_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem sg_sound : NonHalt sg_tm /\QHBound 0 sg_tm.
Proof. split;[exact sg_nonhalt|exact sg_state_zero]. Qed.
Print Assumptions sg_sound.
