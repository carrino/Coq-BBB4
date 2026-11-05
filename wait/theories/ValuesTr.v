(** Exact instruction waiting times; the cutoff configuration is included. *)
From Coq Require Import List Arith Lia Bool.
From SmallBB Require Import Statement StatementTr CTape ClosureTr Size Bounds Value12 Value22.
From BBBWait Require Import SpecTr CheckerTr Values.
Import ListNotations.

(** Right-hand form: 1RB0LB_1LA0RA; target B1. *)
Definition wait22_tr_champion := machine_of_codes 2 2 [7;1;4;2].
Lemma wait22_tr_champion_admissible : Admissible 2 2 wait22_tr_champion.
Proof.
 split.
 - intros q s tr E;destruct q,s;cbn in E;try discriminate;
   injection E as <-;unfold output_ok;cbn;lia.
 - intros q s H;destruct q,s;cbn in H;try lia;reflexivity.
Qed.
Lemma wait22_tr_champion_beeps : FiresAt wait22_tr_champion(StB,S1)17.
Proof.
 assert(E:exists c,csteps wait22_tr_champion 17 c0=Some c /\ cinstr c=(StB,S1)).
 {vm_compute;eexists;split;reflexivity. }
 destruct E as(c&Ec&Hc);exists(lift c);split;[|rewrite cinstr_lift;exact Hc].
 rewrite <-lift_c0;apply csteps_lift;exact Ec.
Qed.
Lemma wait22_tr_champion_silent : forall t,8<=t->t<=16->
 ~FiresAt wait22_tr_champion(StB,S1)t.
Proof.
 intros t Hlo Hhi Hv.
 destruct(fires_computable wait22_tr_champion t(StB,S1)Hv)as(c&Ec&Hc).
 assert(Hcheck:cfires wait22_tr_champion
   (match csteps wait22_tr_champion 8 c0 with Some c=>c|None=>c0 end)9(StB,S1)=false)
   by(vm_compute;reflexivity).
 destruct(csteps_prefix wait22_tr_champion 8 t c0 c Hlo Ec)as(cb&Eb&Ebt).
 rewrite Eb in Hcheck.
 pose proof(cfires_complete wait22_tr_champion 9 cb(StB,S1)(t-8)c ltac:(lia) Ebt Hc)as Hyes.
 rewrite Hyes in Hcheck;discriminate.
Qed.
Theorem wait22_tr_minimal : forall w,WaitBoundTr 2 2 8 w->9<=w.
Proof.
 intros w H.
 assert(Hfuture:FutureBeepTr wait22_tr_champion(StB,S1)8).
 {exists 17;split;[lia|exact wait22_tr_champion_beeps]. }
 destruct(H wait22_tr_champion wait22_tr_champion_admissible(StB,S1)Hfuture)
 as(t&Hlo&Hhi&Hv).
 destruct(le_lt_dec 9 w);[assumption|].
 exfalso;exact(wait22_tr_champion_silent t Hlo ltac:(lia) Hv).
Qed.

Lemma all12_tr_checked :
 forallb(fun a=>forallb(fun b=>machine_tr_check(table12 a b)1 0)choices12)choices12=true.
Proof. vm_compute;reflexivity. Qed.
Theorem wait12_tr_upper : WaitBoundTr 1 2 1 0.
Proof.
 intros tm Had q;apply machine_tr_sound.
 pose proof all12_tr_checked as H.
 apply forallb_forall with(x:=tm StA S0)in H;[|now apply choice12_complete].
 apply forallb_forall with(x:=tm StA S1)in H;[|now apply choice12_complete].
 rewrite <-(table12_complete tm Had)in H;exact H.
Qed.
Theorem BBB_wait12_tr_value : BBBWaitTr_is 1 2 1 0.
Proof. split;[exact(proj2 BBB12_value)|];split;[exact wait12_tr_upper|intros;lia]. Qed.
Print Assumptions BBB_wait12_tr_value.

From BBBWait Require Import Tail.

(** Failed cheap checks are discharged by translated-cycle certificates.
    Short-circuiting avoids evaluating every candidate after a success. *)
Fixpoint any_candidate {A:Type}(f:A->bool)(xs:list A):bool :=
 match xs with []=>false|x::rest=>if f x then true else any_candidate f rest end.
Lemma any_candidate_sound : forall A(f:A->bool)xs,
 any_candidate f xs=true->exists x,f x=true.
Proof.
 intros A f xs;induction xs as[|x xs IH];intros H;[discriminate|].
 cbn[any_candidate]in H;destruct(f x)eqn:E;[exists x;exact E|now apply IH].
Qed.
Definition cycle22_profiles := flat_map(fun m=>flat_map(fun p=>
 map(fun W=>(m,p,W))(seq 0 6))(seq 1 12))[false;true].
Definition small22_tr_check tm := if machine_tr_check tm 8 9 then true else
 any_candidate(fun '(m,p,W)=>tc_wait_check_tr tm 8 9 m 17 p W)cycle22_profiles.
Lemma small22_tr_sound : forall tm,small22_tr_check tm=true->
 forall tg,FutureBeepTr tm tg 8->BeepWindowTr tm tg 8 9.
Proof.
 intros tm H;unfold small22_tr_check in H.
 destruct(machine_tr_check tm 8 9)eqn:E;[now apply machine_tr_sound|].
 apply any_candidate_sound in H as([[m p]W]&H).
 now apply(tc_wait_check_tr_sound tm 8 9 m 17 p W).
Qed.
Lemma all22_tr_checked :
 forallb(fun a=>forallb(fun b=>forallb(fun c=>forallb(fun d=>
 small22_tr_check(table22 a b c d))choices22)choices22)choices22)choices22=true.
Proof. vm_compute;reflexivity. Qed.
Theorem wait22_tr_upper : WaitBoundTr 2 2 8 9.
Proof.
 intros tm Had tg;apply small22_tr_sound.
 pose proof all22_tr_checked as H.
 apply forallb_forall with(x:=tm StA S0)in H;[|now apply choice22_complete].
 apply forallb_forall with(x:=tm StA S1)in H;[|now apply choice22_complete].
 apply forallb_forall with(x:=tm StB S0)in H;[|now apply choice22_complete].
 apply forallb_forall with(x:=tm StB S1)in H;[|now apply choice22_complete].
 rewrite <-(table22_complete tm Had)in H;exact H.
Qed.
Theorem BBB_wait22_tr_value : BBBWaitTr_is 2 2 8 9.
Proof.
 split;[exact(proj2 BBB22_value)|];split;[exact wait22_tr_upper|exact wait22_tr_minimal].
Qed.
Print Assumptions BBB_wait22_tr_value.
