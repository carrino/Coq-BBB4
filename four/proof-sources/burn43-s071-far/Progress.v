(** Finite B episodes and recurrence from exclusion of right blank spinout.
    ActualNoSpinout discharges that exclusion using the checked FAR certificate. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census TotalCompletion OneStateReach.
From BBB24Burn43S071FAR Require Import Programs.
Import ListNotations.
Theorem s71_B1_progress : forall l r,exists n c,0<n/\fst c=StA/\
 csteps s71_tm n(StB,(l,S1,r))=Some c.
Proof.
 induction l as[|h l IH];intro r.
 - exists 3,(s71_front StA[S1;S0]r);repeat split;try lia;reflexivity.
 - destruct h.
   + exists 3,(s71_front StA(S1::S0::l)r);repeat split;try lia;reflexivity.
   + destruct(IH(S3::r))as(n&c&Hn&Hc&E).
     exists(S n),c;split;[lia|];split;[exact Hc|].
     change(csteps s71_tm n(StB,(l,S1,S3::r))=Some c);exact E.
   + exists 2,(StA,(ctl l,chd l,S0::S3::r));repeat split;try lia;reflexivity.
   + exists 2,(StA,(S1::l,S3,r));repeat split;try lia;reflexivity.
Qed.
Theorem s71_B0_progress : forall r,all_blank r=false->forall l,exists n c,0<n/\fst c=StA/\
 csteps s71_tm n(StB,(l,S0,r))=Some c.
Proof.
 induction r as[|h r IH];intros H l;[discriminate|];destruct h.
 - change(all_blank r=false)in H;destruct(IH H(S0::l))as(n&c&Hn&Hc&E).
   exists(S n),c;split;[lia|];split;[exact Hc|].
   change(csteps s71_tm n(StB,(S0::l,S0,r))=Some c);exact E.
 - destruct(s71_B1_progress(S0::l)r)as(n&c&Hn&Hc&E).
   exists(S n),c;split;[lia|];split;[exact Hc|].
   change(csteps s71_tm n(StB,(S0::l,S1,r))=Some c);exact E.
 - exists 2,(StA,(l,S0,S0::r));repeat split;try lia;reflexivity.
 - exists 2,(s71_front StA(S1::S0::l)r);repeat split;try lia;reflexivity.
Qed.
Theorem s71_B_progress : forall l h r,(h=S0->all_blank r=false)->
 exists n c,0<n/\fst c=StA/\csteps s71_tm n(StB,(l,h,r))=Some c.
Proof.
 intros l h r H;destruct h.
 - apply s71_B0_progress,H;reflexivity.
 - apply s71_B1_progress.
 - exists 1,(StA,(ctl l,chd l,S0::r));repeat split;try lia;reflexivity.
 - exists 1,(s71_front StA(S1::l)r);repeat split;try lia;reflexivity.
Qed.
Lemma s71_total : Total s71_tm.
Proof. intros q h;unfold s71_tm;eexists;reflexivity. Qed.
Theorem s71_nonhalt : NonHalt s71_tm.
Proof. apply ore_total_nonhalt;exact s71_total. Qed.
Lemma s71_B_checked : ore_auto_goal s71_tm StB=true.
Proof. vm_compute;reflexivity. Qed.
Theorem s71_B_recurrent : forall N,exists n,N<=n/\VisitsAt s71_tm StB n.
Proof.
 apply(ore_reaches_recurs s71_tm StB s71_total).
 apply ore_auto_goal_sound;exact s71_B_checked.
Qed.
Lemma s71_B_drift : forall n l,csteps s71_tm n(StB,(l,S0,[]))=
 Some(StB,(repeat S0 n++l,S0,[])).
Proof.
 induction n;intro l;[reflexivity|].
 change(csteps s71_tm n(StB,(S0::l,S0,[]))=Some(StB,(S0::(repeat S0 n++l),S0,[]))).
 rewrite IHn,s71_shift;reflexivity.
Qed.
Example s71_unsafe_1010 : forall n,csteps s71_tm(173+n)(StA,([S1;S0;S1;S0],S0,[]))=
 Some(StB,(repeat S0 n++[S2;S2;S1;S0;S2;S1;S0;S2;S1;S2;S2;S0],S0,[])).
Proof.
 intro n;rewrite csteps_add.
 change(csteps s71_tm n(StB,([S2;S2;S1;S0;S2;S1;S0;S2;S1;S2;S2;S0],S0,[]))=
 Some(StB,(repeat S0 n++[S2;S2;S1;S0;S2;S1;S0;S2;S1;S2;S2;S0],S0,[]))).
 apply s71_B_drift.
Qed.
Example s71_entry48 : csteps s71_tm 48 c0=Some(StA,([S2;S2;S1;S0;S2;S1;S0],S0,[])).
Proof. vm_compute;reflexivity. Qed.
Print Assumptions s71_B_progress.
Print Assumptions s71_unsafe_1010.

(** A future invariant may start at any rigorously checked entry, so it
    need not encode the startup.  The premise below is deliberately open. *)
Definition s71_guard_from entry:=forall n l r,
 csteps s71_tm n entry=Some(StB,(l,S0,r))->all_blank r=false.
Theorem s71_A_recurrent_from_guard : forall entry d,
 csteps s71_tm d c0=Some entry->s71_guard_from entry->
 forall N,exists n,N<=n/\VisitsAt s71_tm StA n.
Proof.
 intros entry d Ed G N;destruct(ore_total_csteps s71_tm s71_total N entry)as(c&Ec).
 destruct c as[q[[l h]r]];destruct q.
 - exists(d+N);split;[lia|].
   exists(lift(StA,(l,h,r)));split;[|reflexivity].
   rewrite <-lift_c0;apply csteps_lift;now rewrite csteps_add,Ed.
 - destruct(s71_B_progress l h r)as(k&v&Hk&Hv&Ev).
   {intro H;subst h;exact(G N l r Ec). }
   exists(d+(N+k));split;[lia|].
   exists(lift v);split;[|exact Hv].
   rewrite <-lift_c0;apply csteps_lift;now rewrite csteps_add,Ed,csteps_add,Ec.
Qed.
Theorem s71_state_zero_from_guard : forall entry d,
 csteps s71_tm d c0=Some entry->s71_guard_from entry->QHBound 0 s71_tm.
Proof.
 intros entry d Ed G q s[Hv Hquiet];exfalso;destruct q.
 - destruct(s71_A_recurrent_from_guard entry d Ed G(S s))as(k&Hk&Hv').
   apply(Hquiet k);[lia|exact Hv'].
 - destruct(s71_B_recurrent(S s))as(k&Hk&Hv').
   apply(Hquiet k);[lia|exact Hv'].
Qed.
Definition s71_entry70:cconf:=(StA,([S2;S1;S0],S0,[S3;S0;S1;S0;S1;S1])).
Example s71_entry70_checked : csteps s71_tm 70 c0=Some s71_entry70.
Proof. vm_compute;reflexivity. Qed.
Definition s71_entry300:cconf:=(StA,([S2;S2;S1;S0;S2;S1;S0;S2;S1;S2;S1;S2;S2;S0;S2;S2;S2;S2;S1;S0],S0,[])).
Example s71_entry300_checked : csteps s71_tm 300 c0=Some s71_entry300.
Proof. vm_compute;reflexivity. Qed.
Print Assumptions s71_state_zero_from_guard.
