(** * PairTransferTr: a finite pair transfer and a doubling reset.

    The anchor is A0 with empty left tape and right [(10)^m 11], m>0.
    Three uniform sweeps reach [(10) 11 (10)^(m+3) 11].  Each inner
    round consumes one block after the marker and adds two before it:
    [(10)^k 11 (10)^(l+1) 11] -> [(10)^(k+2) 11 (10)^l 11].
    The finite drain and terminal sweep return to the anchor with
    [m'=2*m+10].  All eight instructions have explicit firing witnesses.
    The boot is a separate hypothesis so exact state conjugates may
    enter the same invariant at different counter values. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import ValueLapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Fixpoint pt10(k:nat):list Sym:=match k with 0=>[]|S k=>S1::S0::pt10 k end.
Fixpoint pt01(k:nat):list Sym:=match k with 0=>[]|S k=>S0::S1::pt01 k end.
Lemma pt10_push:forall k L,pt10 k++S1::S0::L=pt10(S k)++L.
Proof. induction k;intro L;cbn[pt10 app];[reflexivity|now rewrite IHk]. Qed.
Lemma pt01_push:forall k L,pt01 k++S0::S1::L=pt01(S k)++L.
Proof. induction k;intro L;cbn[pt01 app];[reflexivity|now rewrite IHk]. Qed.
Lemma pt_shift1:forall k L,S1::pt01 k++L=pt10 k++S1::L.
Proof. induction k;intro L;cbn[pt10 pt01 app];[reflexivity|now rewrite IHk]. Qed.
Lemma pt_shift0:forall k L,S0::pt10 k++L=pt01 k++S0::L.
Proof. induction k;intro L;cbn[pt10 pt01 app];[reflexivity|now rewrite IHk]. Qed.
Section Machine.
Variable tm:TM.
Hypothesis HA0:tm StA S0=Some(mkTrans S1 DR StB).
Hypothesis HA1:tm StA S1=Some(mkTrans S0 DL StC).
Hypothesis HB0:tm StB S0=Some(mkTrans S1 DL StC).
Hypothesis HB1:tm StB S1=Some(mkTrans S1 DR StD).
Hypothesis HC0:tm StC S0=Some(mkTrans S1 DL StA).
Hypothesis HC1:tm StC S1=Some(mkTrans S0 DL StB).
Hypothesis HD0:tm StD S0=Some(mkTrans S0 DR StB).
Hypothesis HD1:tm StD S1=Some(mkTrans S0 DR StC).
Local Ltac pt_compute:=
 cbn[Nat.add Nat.mul csteps cstep ctape_move chd ctl t_next t_dir t_write pt10 pt01 app];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[Nat.add Nat.mul csteps cstep ctape_move chd ctl t_next t_dir t_write pt10 pt01 app]);repeat rewrite app_nil_r;reflexivity.
Definition pt_run(c d:cconf):Prop:=exists k,csteps tm k c=Some d.
Lemma pt_trans:forall c d e,pt_run c d->pt_run d e->pt_run c e.
Proof. intros c d e(k&Hk)(j&Hj). exists(k+j). now rewrite csteps_add,Hk. Qed.
Lemma pt_B1_sweep:forall k L R,
 csteps tm(2*k)(StB,(L,S1,pt01 k++R))=
 Some(StB,(pt01 k++L,S1,R)).
Proof.
 induction k as[|k IH];intros L R;[reflexivity|].
 replace(2*S k)with(2+2*k)by lia. rewrite csteps_add.
 assert(E:csteps tm 2(StB,(L,S1,pt01(S k)++R))=
 Some(StB,(S0::S1::L,S1,pt01 k++R)))by pt_compute.
 now rewrite E,IH,pt01_push.
Qed.
Lemma pt_A1_sweep:forall k L R,
 csteps tm(2*k)(StA,(pt01 k++L,S1,R))=
 Some(StA,(L,S1,pt10 k++R)).
Proof.
 induction k as[|k IH];intros L R;[reflexivity|].
 replace(2*S k)with(2+2*k)by lia. rewrite csteps_add.
 assert(E:csteps tm 2(StA,(pt01(S k)++L,S1,R))=
 Some(StA,(pt01 k++L,S1,S1::S0::R)))by pt_compute.
 now rewrite E,IH,pt10_push.
Qed.
Lemma pt_B0_sweep:forall k L R,
 csteps tm(2*k)(StB,(pt10 k++L,S0,R))=
 Some(StB,(L,S0,pt01 k++R)).
Proof.
 induction k as[|k IH];intros L R;[reflexivity|].
 replace(2*S k)with(2+2*k)by lia. rewrite csteps_add.
 assert(E:csteps tm 2(StB,(pt10(S k)++L,S0,R))=
 Some(StB,(pt10 k++L,S0,S0::S1::R)))by pt_compute.
 now rewrite E,IH,pt01_push.
Qed.
Lemma pt_A_enter:forall k R,
 csteps tm 1(StA,([],S0,pt10(S k)++S1::R))=
 Some(StB,([S1],S1,pt01(S k)++R)).
Proof. intros. cbn[pt10 pt01 app]. rewrite <-pt_shift1. pt_compute. Qed.
Lemma pt_B_exit:forall k,
 pt_run(StB,(S0::pt10 k++[S1],S0,[]))
       (StA,([],S0,pt10(S k)++[S1;S1])).
Proof.
 intro k. exists(2+(2*k+2)). rewrite csteps_add.
 assert(E:csteps tm 2(StB,(S0::pt10 k++[S1],S0,[]))=
 Some(StA,(pt01 k,S1,[S1;S1]))).
 { rewrite <- (app_nil_r(pt01 k)),<-pt_shift1. pt_compute. }
 rewrite E,csteps_add,<- (app_nil_r(pt01 k)),pt_A1_sweep.
 pt_compute.
Qed.
Lemma pt_outer1:forall k,
 pt_run(StA,([],S0,pt10(S k)++[S1;S1]))
       (StA,([],S0,S1::S1::S0::S0::pt10(S k)++[S1;S1;S1;S1])).
Proof.
 intro k. eapply pt_trans;[exists 1;apply pt_A_enter|].
 eapply pt_trans;[exists(2*S k);apply pt_B1_sweep|].
 eapply pt_trans with(d:=(StA,(pt01(S k)++[S1],S1,[S1;S1;S1;S1]))).
 { exists 14. pt_compute. }
 eapply pt_trans;[exists(2*S k);apply pt_A1_sweep|].
 exists 4. pt_compute.
Qed.
Lemma pt_outer2:forall k,
 pt_run(StA,([],S0,S1::S1::S0::S0::pt10 k++[S1;S1;S1;S1]))
       (StB,(S0::pt10(k+3)++[S1;S1;S1],S0,[])).
Proof.
 intro k.
 eapply pt_trans with(d:=(StB,([S1;S1;S1],S1,pt01(S k)++[S1;S1;S1]))).
 { exists 5. rewrite <-pt_shift1. pt_compute. }
 eapply pt_trans;[exists(2*S k);apply pt_B1_sweep|].
 eapply pt_trans with(d:=(StB,(pt10(S k)++[S1;S1;S1;S1],S0,[S0;S1]))).
 { exists 3. rewrite <-pt_shift1. pt_compute. }
 eapply pt_trans;[exists(2*S k);apply pt_B0_sweep|].
 rewrite pt01_push.
 eapply pt_trans with(d:=(StB,([S1;S1],S1,pt01(S(S(S k)))))).
 { exists 2. change(pt01(S(S(S k))))with(S0::S1::pt01(S(S k))). pt_compute. }
 rewrite <- (app_nil_r(pt01(S(S(S k))))).
 eapply pt_trans;[exists(2*S(S(S k)));apply pt_B1_sweep|].
 exists 2. replace(k+3)with(S(S(S k)))by lia. rewrite <-pt_shift1. pt_compute.
Qed.
Lemma pt_outer3:forall k,
 pt_run(StB,(S0::pt10 k++[S1;S1;S1],S0,[]))
       (StA,([],S0,pt10 1++S1::S1::pt10 k++[S1;S1])).
Proof.
 intro k.
 eapply pt_trans with(d:=(StA,(pt01 k++[S1;S1],S1,[S1;S1]))).
 { exists 2. rewrite <-pt_shift1. pt_compute. }
 eapply pt_trans;[exists(2*k);apply pt_A1_sweep|].
 exists 8. pt_compute.
Qed.
Lemma pt_inner:forall k R,
 pt_run(StA,([],S0,pt10(S k)++S1::S1::S1::S0::R))
       (StA,([],S0,pt10(S(S(S k)))++S1::S1::R)).
Proof.
 intros k R. eapply pt_trans;[exists 1;apply pt_A_enter|].
 eapply pt_trans;[exists(2*S k);apply pt_B1_sweep|].
 eapply pt_trans with(d:=(StB,(pt10(S k)++[S1;S1],S0,S0::S0::R))).
 { exists 3. rewrite <-pt_shift1. pt_compute. }
 eapply pt_trans;[exists(2*S k);apply pt_B0_sweep|].
 eapply pt_trans with(d:=(StB,([],S1,pt01(S(S k))++S0::S0::R))).
 { exists 2. pt_compute. }
 eapply pt_trans;[exists(2*S(S k));apply pt_B1_sweep|].
 eapply pt_trans with(d:=(StA,(pt01(S(S k)),S1,S1::S1::R))).
 { exists 4. pt_compute. }
 rewrite <- (app_nil_r(pt01(S(S k)))).
 eapply pt_trans;[exists(2*S(S k));apply pt_A1_sweep|].
 exists 2. pt_compute.
Qed.
Lemma pt_drain:forall l k,
 pt_run(StA,([],S0,pt10(S k)++S1::S1::pt10 l++[S1;S1]))
       (StA,([],S0,pt10(S k+2*l)++[S1;S1;S1;S1])).
Proof.
 induction l as[|l IH];intro k.
 - replace(S k+2*0)with(S k)by lia. exists 0. reflexivity.
 - cbn[pt10]. eapply pt_trans;[apply pt_inner|].
   replace(S k+2*S l)with(S(S(S k))+2*l)by lia. apply IH.
Qed.
Lemma pt_terminal:forall k,
 pt_run(StA,([],S0,pt10(S k)++[S1;S1;S1;S1]))
       (StA,([],S0,pt10(S k+3)++[S1;S1])).
Proof.
 intro k. eapply pt_trans;[exists 1;apply pt_A_enter|].
 eapply pt_trans;[exists(2*S k);apply pt_B1_sweep|].
 eapply pt_trans with(d:=(StB,(pt10(S k)++[S1;S1],S0,[S0;S1]))).
 { exists 3. rewrite <-pt_shift1. pt_compute. }
 eapply pt_trans;[exists(2*S k);apply pt_B0_sweep|].
 rewrite pt01_push.
 eapply pt_trans with(d:=(StB,([],S1,pt01(S(S(S k)))))).
 { exists 2. pt_compute. }
 rewrite <- (app_nil_r(pt01(S(S(S k))))).
 eapply pt_trans;[exists(2*S(S(S k)));apply pt_B1_sweep|].
 eapply pt_trans with(d:=(StB,(S0::pt10(S(S(S k)))++[S1],S0,[]))).
 { exists 2. rewrite <-pt_shift1. pt_compute. }
 replace(S k+3)with(S(S(S(S k))))by lia. apply pt_B_exit.
Qed.
Definition pt_anchor(n k:nat):cconf:=(StA,([],S0,pt10(S k)++[S1;S1])).
Lemma pt_lap:forall n k,exists j,
 csteps tm j(pt_anchor n k)=Some(pt_anchor(S n)(2*k+11))/\0<j.
Proof.
 intros n k.
 assert(H:pt_run(pt_anchor n k)(pt_anchor(S n)(2*k+11))).
 { unfold pt_anchor. eapply pt_trans;[apply pt_outer1|].
   eapply pt_trans;[apply pt_outer2|].
   eapply pt_trans;[apply pt_outer3|].
   eapply pt_trans;[apply(pt_drain(S k+3)0)|].
   replace(1+2*(S k+3))with(S(2*(S k+3)))by lia.
   replace(S(2*k+11))with(S(2*(S k+3))+3)by lia. apply pt_terminal.
 }
 destruct H as(j&Ej). exists j. split;[exact Ej|].
 destruct j;[|lia]. cbn[csteps]in Ej. unfold pt_anchor in Ej.
 assert(L:forall k,length(pt10 k)=2*k).
 { induction k0;[reflexivity|cbn[pt10 length];lia]. }
 injection Ej as E. apply(f_equal(@length Sym))in E.
 repeat rewrite app_length in E. repeat rewrite L in E. cbn[length]in E. lia.
Qed.
Lemma pt_outer_fires:forall k t,exists j c,
 csteps tm j(StA,([],S0,S1::S1::S0::S0::pt10(S k)++[S1;S1;S1;S1]))=Some c /\cinstr c=t.
Proof.
 intros k[q s].
 assert(E:csteps tm(5+2*S(S k))
   (StA,([],S0,S1::S1::S0::S0::pt10(S k)++[S1;S1;S1;S1]))=
   Some(StB,(pt01(S(S k))++[S1;S1;S1],S1,[S1;S1;S1]))).
 { rewrite csteps_add.
   assert(E0:csteps tm 5(StA,([],S0,S1::S1::S0::S0::pt10(S k)++[S1;S1;S1;S1]))=
     Some(StB,([S1;S1;S1],S1,pt01(S(S k))++[S1;S1;S1]))).
   { rewrite <-pt_shift1. pt_compute. }
   now rewrite E0,pt_B1_sweep.
 }
 destruct q,s.
 - exists 0. eexists. split;[pt_compute|reflexivity].
 - destruct(pt_outer2(S k))as(j&Hj). exists(j+2). eexists. split.
   + rewrite csteps_add,Hj. pt_compute.
   + reflexivity.
 - exists((5+2*S(S k))+3). eexists. split;[rewrite csteps_add,E;pt_compute|reflexivity].
 - exists 1. eexists. split;[pt_compute|reflexivity].
 - exists 3. eexists. split;[pt_compute|reflexivity].
 - exists((5+2*S(S k))+2). eexists. split;[rewrite csteps_add,E;pt_compute|reflexivity].
 - exists 6. eexists. split;[pt_compute|reflexivity].
 - exists 2. eexists. split;[pt_compute|reflexivity].
Qed.
Lemma pt_fires:forall n k t,exists j c,
 csteps tm j(pt_anchor n k)=Some c/\cinstr c=t.
Proof.
 intros n k t. destruct(pt_outer1 k)as(i&Ei).
 destruct(pt_outer_fires k t)as(j&c&Ej&Ht).
 exists(i+j),c. split;[|exact Ht]. unfold pt_anchor. now rewrite csteps_add,Ei.
Qed.
Theorem pt_neverqhtr:forall k0,
 (exists b,stepn tm b InitES=Some(lift(pt_anchor 0 k0)))->NeverQuasiHaltsTr tm.
Proof.
 intros k0 Boot. apply(value_lap_neverqhtr tm nat(fun k=>2*k+11)pt_anchor k0).
 - exact Boot.
 - intros n k. destruct(pt_lap n k)as(j&Ej&Hj).
   exists j,(pt_anchor(S n)(2*k+11)). split;[exact Ej|]. split;[reflexivity|exact Hj].
 - apply pt_fires.
Qed.
End Machine.
