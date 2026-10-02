(** * Positive recurrence from a finite left drain and a return theorem.

    No choice principle is needed: induction on the requested time bound
    composes one existential positive return at a time. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
Import ListNotations.

Section DyadicRecurrence.
Variable tm : TM.
Variable ka : nat.
Hypothesis Hka_pos : 0<ka.
Hypothesis Hka : forall L R,
 csteps tm ka (StA,(L,S1,S0::R)) =
 Some (StA,(ctl L,chd L,S0::S0::R)).
Hypothesis HA0hit : forall L R, exists k L' R',
 stepn tm k (lift(StA,(L,S0,R))) = Some(lift(StA,(L',S1,S0::R'))).

Lemma dr_drain : forall L R, exists k L' R', 0<k /\
 csteps tm k (StA,(L,S1,S0::R)) = Some(StA,(L',S0,R')).
Proof.
 induction L as [|h L IH];intro R.
 - exists ka,[],(S0::S0::R). split;[exact Hka_pos|apply Hka].
 - destruct h.
   + exists ka,L,(S0::S0::R). split;[exact Hka_pos|apply Hka].
   + destruct (IH (S0::R)) as (k&L'&R'&Hk&Ek).
     exists (ka+k),L',R'. split;[lia|].
     rewrite csteps_add,Hka. exact Ek.
Qed.

Lemma dr_positive_return : forall L R, exists k L' R', 0<k /\
 stepn tm k (lift(StA,(L,S1,S0::R))) = Some(lift(StA,(L',S1,S0::R'))).
Proof.
 intros L R. destruct (dr_drain L R) as (n&U&V&Hn&En).
 destruct (HA0hit U V) as (m&U'&V'&Em).
 exists (n+m),U',V'. split;[lia|].
 rewrite stepn_add,(csteps_lift _ _ _ _ En). exact Em.
Qed.

Theorem dyadic_A1_recurrent :
 (exists t L R, stepn tm t InitES=Some(lift(StA,(L,S1,S0::R)))) ->
 forall N, exists j e, N<=j /\ stepn tm j InitES=Some e /\ instr_of e=(StA,S1).
Proof.
 intro Boot.
 assert (Reach : forall N, exists t L R, N<=t /\
   stepn tm t InitES=Some(lift(StA,(L,S1,S0::R)))).
 { induction N as [|N IH].
   - destruct Boot as (t&L&R&Et). exists t,L,R. split;[lia|exact Et].
   - destruct IH as (t&L&R&Ht&Et).
     destruct (dr_positive_return L R) as (k&L'&R'&Hk&Ek).
     exists (t+k),L',R'. split;[lia|]. rewrite stepn_add,Et. exact Ek. }
 intro N. destruct (Reach N) as (t&L&R&Ht&Et).
 exists t,(lift(StA,(L,S1,S0::R))). repeat split;assumption || reflexivity.
Qed.
End DyadicRecurrence.
