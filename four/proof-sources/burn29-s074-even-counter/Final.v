(** Positive finite returns give unbounded visits to both states. *)
From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement Spec CTape Census TotalCompletion OneStateReach.
From BBB24Burn29S074EvenCounter Require Import Programs Grammar.
Import ListNotations.
Theorem s74_A_late : forall N,exists k,N<=k /\VisitsAt s74_tm StA k.
Proof.
 intro N;destruct(s74_late_cuts N[]eq_refl)as(k&v&Hk&Hv&Ec).
 exists k;split;[exact Hk|].
 exists(lift(s74_cut v));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact Ec.
Qed.
Theorem s74_B_late : forall N,exists k,N<=k /\VisitsAt s74_tm StB k.
Proof.
 intro N;destruct(s74_late_cuts N[]eq_refl)as(k&v&Hk&Hv&Ec).
 exists(k+1);split;[lia|].
 exists(lift(StB,([],S0,S1::v)));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift.
 change(csteps s74_tm(k+1)(s74_cut[])=Some(StB,([],S0,S1::v))).
 rewrite csteps_add,Ec;reflexivity.
Qed.
Theorem s74_state_zero : QHBound 0 s74_tm.
Proof.
 intros q s[Hv Hquiet];exfalso;destruct q.
 - destruct(s74_A_late(S s))as(k&Hk&Hv');apply(Hquiet k);[lia|exact Hv'].
 - destruct(s74_B_late(S s))as(k&Hk&Hv');apply(Hquiet k);[lia|exact Hv'].
Qed.
Lemma s74_total : Total s74_tm.
Proof. intros q h;unfold s74_tm;eexists;reflexivity. Qed.
Theorem s74_nonhalt : NonHalt s74_tm.
Proof. apply ore_total_nonhalt;exact s74_total. Qed.
Theorem s74_sound : NonHalt s74_tm /\QHBound 0 s74_tm.
Proof. split;[exact s74_nonhalt|exact s74_state_zero]. Qed.
Theorem s74_below_champion : QHBound score s74_tm.
Proof. intros q s H;pose proof(s74_state_zero q s H);lia. Qed.
Print Assumptions s74_sound.
