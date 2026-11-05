(** Exact state-based waiting times for one- and two-state binary machines.
    The already-observed configuration at the BBB cutoff is included. *)
From Coq Require Import List Arith Lia Bool FunctionalExtensionality.
From SmallBB Require Import Statement CTape Size Bounds Value12 Value22.
From BBBWait Require Import Spec Checker.
Import ListNotations.

Definition choices12 : list (option Trans) :=
 [None; Some (mkTrans S0 DL StA); Some (mkTrans S0 DR StA);
        Some (mkTrans S1 DL StA); Some (mkTrans S1 DR StA)].
Definition choices22 : list (option Trans) :=
 [None; Some (mkTrans S0 DL StA); Some (mkTrans S0 DL StB);
        Some (mkTrans S0 DR StA); Some (mkTrans S0 DR StB);
        Some (mkTrans S1 DL StA); Some (mkTrans S1 DL StB);
        Some (mkTrans S1 DR StA); Some (mkTrans S1 DR StB)].

Definition table12 a b : TM := fun q s => match q,s with
 | StA,S0 => a | StA,S1 => b | _,_ => None end.
Definition table22 a b c d : TM := fun q s => match q,s with
 | StA,S0 => a | StA,S1 => b | StB,S0 => c | StB,S1 => d
 | _,_ => None end.

Lemma choice12_complete : forall tm, Admissible 1 2 tm ->
 forall q s, In (tm q s) choices12.
Proof.
 intros tm Had q s;destruct(tm q s)as[[w dr p]|]eqn:E;[|cbn;auto].
 pose proof(admissible_output 1 2 tm Had q s _ E)as H.
 unfold output_ok in H;destruct w,dr,p;cbn in H;try lia;cbn;tauto.
Qed.
Lemma choice22_complete : forall tm, Admissible 2 2 tm ->
 forall q s, In (tm q s) choices22.
Proof.
 intros tm Had q s;destruct(tm q s)as[[w dr p]|]eqn:E;[|cbn;auto].
 pose proof(admissible_output 2 2 tm Had q s _ E)as H.
 unfold output_ok in H;destruct w,dr,p;cbn in H;try lia;cbn;tauto.
Qed.
Lemma table12_complete : forall tm, Admissible 1 2 tm ->
 tm=table12 (tm StA S0)(tm StA S1).
Proof.
 intros tm Had;extensionality q;extensionality s;destruct q,s;
 unfold table12;try reflexivity;apply(proj2 Had);cbn;lia.
Qed.
Lemma table22_complete : forall tm, Admissible 2 2 tm ->
 tm=table22 (tm StA S0)(tm StA S1)(tm StB S0)(tm StB S1).
Proof.
 intros tm Had;extensionality q;extensionality s;destruct q,s;
 unfold table22;try reflexivity;apply(proj2 Had);cbn;lia.
Qed.

(** These checks cover every partial table: 5^2 = 25 and 9^4 = 6561.
    The sound checker proves permanent silence whenever the window has
    no beep; no bounded simulation is mistaken for non-recurrence. *)
Lemma all12_checked :
 forallb(fun a=>forallb(fun b=>machine_check(table12 a b)1 0)choices12)choices12=true.
Proof. vm_compute;reflexivity. Qed.
Lemma all22_checked :
 forallb(fun a=>forallb(fun b=>forallb(fun c=>forallb(fun d=>
 machine_check(table22 a b c d)6 3)choices22)choices22)choices22)choices22=true.
Proof. vm_compute;reflexivity. Qed.

Theorem wait12_upper : WaitBound 1 2 1 0.
Proof.
 intros tm Had q;apply machine_sound.
 pose proof all12_checked as H.
 apply forallb_forall with(x:=tm StA S0)in H;[|now apply choice12_complete].
 apply forallb_forall with(x:=tm StA S1)in H;[|now apply choice12_complete].
 rewrite <-(table12_complete tm Had)in H;exact H.
Qed.
Theorem wait22_upper : WaitBound 2 2 6 3.
Proof.
 intros tm Had q;apply machine_sound.
 pose proof all22_checked as H.
 apply forallb_forall with(x:=tm StA S0)in H;[|now apply choice22_complete].
 apply forallb_forall with(x:=tm StA S1)in H;[|now apply choice22_complete].
 apply forallb_forall with(x:=tm StB S0)in H;[|now apply choice22_complete].
 apply forallb_forall with(x:=tm StB S1)in H;[|now apply choice22_complete].
 rewrite <-(table22_complete tm Had)in H;exact H.
Qed.

(** Right-hand form: 1RB0RB_1LA1LB.  State A occurs at indices
    0,2,5,9,... and is absent throughout the shorter window [6,8]. *)
Definition wait22_champion := machine_of_codes 2 2 [7;3;4;5].
Lemma wait22_champion_admissible : Admissible 2 2 wait22_champion.
Proof.
 split.
 - intros q s tr E;destruct q,s;cbn in E;try discriminate;
   injection E as <-;unfold output_ok;cbn;lia.
 - intros q s H;destruct q,s;cbn in H;try lia;reflexivity.
Qed.
Lemma wait22_champion_beeps : VisitsAt wait22_champion StA 9.
Proof.
 assert(E:exists c,csteps wait22_champion 9 c0=Some c /\ fst c=StA).
 {vm_compute;eexists;split;reflexivity. }
 destruct E as(c&Ec&Hc);exists(lift c);split;[|exact Hc].
 rewrite <-lift_c0;apply csteps_lift;exact Ec.
Qed.
Lemma wait22_champion_silent : forall t,6<=t->t<=8->
 ~VisitsAt wait22_champion StA t.
Proof.
 intros t Hlo Hhi Hv.
 destruct(visits_computable wait22_champion t StA Hv)as(c&Ec&Hc).
 assert(t=6\/t=7\/t=8)by lia;destruct H as [-> | [-> | ->]];
 vm_compute in Ec;injection Ec as <-;discriminate.
Qed.
Theorem wait22_minimal : forall w,WaitBound 2 2 6 w->3<=w.
Proof.
 intros w H.
 assert(Hfuture:FutureBeep wait22_champion StA 6).
 {exists 9;split;[lia|exact wait22_champion_beeps]. }
 destruct(H wait22_champion wait22_champion_admissible StA Hfuture)
 as(t&Hlo&Hhi&Hv).
 destruct(le_lt_dec 3 w);[assumption|].
 exfalso;exact(wait22_champion_silent t Hlo ltac:(lia) Hv).
Qed.

Theorem BBB_wait12_value : BBBWait_is 1 2 1 0.
Proof. split;[exact(proj1 BBB12_value)|];split;[exact wait12_upper|intros;lia]. Qed.
Theorem BBB_wait22_value : BBBWait_is 2 2 6 3.
Proof. split;[exact(proj1 BBB22_value)|];split;[exact wait22_upper|exact wait22_minimal]. Qed.

Print Assumptions BBB_wait12_value.
Print Assumptions BBB_wait22_value.
