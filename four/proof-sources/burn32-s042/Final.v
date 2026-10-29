(** Universal positive returns from an exact blank entry give both-state
    recurrence, hence the state bound zero for this original machine. *)
From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement Spec CTape Census TotalCompletion OneStateReach.
From BBB24Burn32S042 Require Import Programs Symbolic Counter.
Import ListNotations.
Theorem s42_late_cuts : forall N n,exists k v,N<=k /\
 csteps s42_tm k(s42_family n)=Some(s42_family v).
Proof.
 induction N;intro n.
 - exists 0,n;split;[lia|reflexivity].
 - destruct(s42_return n)as(d&Hd&Ed).
   destruct(IHN(3*n+27))as(k&v&Hk&Ek).
   exists(d+k),v;split;[lia|];now rewrite csteps_add,Ed.
Qed.
Definition s42_after n:cconf:=(StB,(s42_word n 0(tl(sl s42_start)),S2,[S1])).
Lemma s42_B_after : forall n,csteps s42_tm 1(s42_family n)=Some(s42_after n).
Proof. reflexivity. Qed.
Theorem s42_A_late : forall N,exists k,N<=k /\VisitsAt s42_tm StA k.
Proof.
 intro N;destruct(s42_late_cuts N 42)as(k&v&Hk&Ek).
 exists(12565+k);split;[lia|].
 exists(lift(s42_family v));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;now rewrite csteps_add,s42_boot.
Qed.
Theorem s42_B_late : forall N,exists k,N<=k /\VisitsAt s42_tm StB k.
Proof.
 intro N;destruct(s42_late_cuts N 42)as(k&v&Hk&Ek).
 exists(12565+(k+1));split;[lia|].
 exists(lift(s42_after v));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift.
 now rewrite csteps_add,s42_boot,csteps_add,Ek,s42_B_after.
Qed.
Theorem s42_state_zero : QHBound 0 s42_tm.
Proof.
 intros q s[Hv Hquiet];exfalso;destruct q.
 - destruct(s42_A_late(S s))as(k&Hk&Hv');apply(Hquiet k);[lia|exact Hv'].
 - destruct(s42_B_late(S s))as(k&Hk&Hv');apply(Hquiet k);[lia|exact Hv'].
Qed.
Lemma s42_total : Total s42_tm.
Proof. intros q h;unfold s42_tm;eexists;reflexivity. Qed.
Theorem s42_nonhalt : NonHalt s42_tm.
Proof. apply ore_total_nonhalt;exact s42_total. Qed.
Theorem s42_sound : NonHalt s42_tm /\QHBound 0 s42_tm.
Proof. split;[exact s42_nonhalt|exact s42_state_zero]. Qed.
Theorem s42_below_champion : QHBound score s42_tm.
Proof. intros q s H;pose proof(s42_state_zero q s H);lia. Qed.
Print Assumptions s42_sound.
