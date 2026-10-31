(** Close the accepted finite-word family and derive both-state recurrence. *)
From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement Spec CTape Census.
From BBB24Burn35S070 Require Import Core Grammar.
Import ListNotations.
Theorem st_main_next : forall w,st_valid w ->exists out t,
 0<t /\ st_valid out /\
 csteps st_tm t(st_main(st_odd++w)[])=Some(st_main(st_odd++out)[]).
Proof.
 intros w H;destruct(st_G_closed w H)as(out&HG&Hv).
 destruct(st_G_sound w out HG)as(t&Ht&Et);exists out,t;auto.
Qed.
Lemma st_returns : forall N,exists t w,N<=t /\st_valid w /\
 csteps st_tm t c0=Some(st_main(st_odd++w)[]).
Proof.
 intro N;induction N as[|N IH].
 - exists 35,[S1];split;[lia|split;[exact st_seed_valid|exact st_entry]].
 - destruct IH as(t&w&Ht&Hw&E).
   destruct(st_main_next w Hw)as(out&k&Hk&Hout&Eout).
   exists(t+k),out;split;[lia|split;[exact Hout|]].
   rewrite csteps_add,E;exact Eout.
Qed.
Theorem st_A_recurrent : forall N,exists t,N<=t /\VisitsAt st_tm StA t.
Proof.
 intro N;destruct(st_returns N)as(t&w&Ht&Hw&E);exists t;split;[exact Ht|].
 exists(lift(st_main(st_odd++w)[]));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem st_B_recurrent : forall N,exists t,N<=t /\VisitsAt st_tm StB t.
Proof.
 intro N;destruct(st_returns N)as(t&w&Ht&Hw&E);exists(t+1);split;[lia|].
 exists(lift(st_back StB(st_odd++w)[S1]));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem st_nonhalt : NonHalt st_tm.
Proof.
 intros n Hnone;destruct(st_returns n)as(t&w&Ht&Hw&E).
 pose proof(csteps_lift st_tm t c0(st_main(st_odd++w)[])E)as Er;rewrite lift_c0 in Er.
 destruct(stepn_prefix st_tm n t InitES(lift(st_main(st_odd++w)[]))Ht Er)as(c&Ec&_);congruence.
Qed.
Theorem st_state_zero : QHBound 0 st_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(st_A_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(st_B_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem st_sound : NonHalt st_tm /\QHBound 0 st_tm.
Proof. split;[exact st_nonhalt|exact st_state_zero]. Qed.
Print Assumptions st_main_next.
Print Assumptions st_sound.
