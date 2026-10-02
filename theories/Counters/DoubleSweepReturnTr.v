(** Positive A0 returns for a doubling pair sweep.  The inner round consumes
    two left-hand 10 blocks and adds four to the right-hand block. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import ValueLapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Fixpoint ds10 (k:nat) : list Sym := match k with 0=>[]|S k=>S1::S0::ds10 k end.
Fixpoint ds01 (k:nat) : list Sym := match k with 0=>[]|S k=>S0::S1::ds01 k end.
Lemma ds10_push : forall k L, ds10 k++S1::S0::L=ds10(S k)++L.
Proof. induction k;intro L;cbn[ds10 app];[reflexivity|now rewrite IHk]. Qed.
Lemma ds01_push : forall k L, ds01 k++S0::S1::L=ds01(S k)++L.
Proof. induction k;intro L;cbn[ds01 app];[reflexivity|now rewrite IHk]. Qed.
Lemma ds_shift1 : forall k L, S1::ds01 k++L=ds10 k++S1::L.
Proof. induction k;intro L;cbn[ds10 ds01 app];[reflexivity|now rewrite IHk]. Qed.
Lemma ds_shift0 : forall k L, S0::ds10 k++L=ds01 k++S0::L.
Proof. induction k;intro L;cbn[ds10 ds01 app];[reflexivity|now rewrite IHk]. Qed.
Section Machine.
Variable tm : TM.
Hypothesis HA0 : tm StA S0=Some(mkTrans S1 DR StB).
Hypothesis HA1 : tm StA S1=Some(mkTrans S0 DL StD).
Hypothesis HB0 : tm StB S0=Some(mkTrans S1 DR StC).
Hypothesis HB1 : tm StB S1=Some(mkTrans S0 DR StA).
Hypothesis HC0 : tm StC S0=Some(mkTrans S1 DL StD).
Hypothesis HC1 : tm StC S1=Some(mkTrans S0 DR StB).
Hypothesis HD0 : tm StD S0=Some(mkTrans S1 DL StB).
Hypothesis HD1 : tm StD S1=Some(mkTrans S0 DL StC).
Local Ltac ds_compute :=
 cbn[Nat.add Nat.mul csteps cstep ctape_move chd ctl t_next t_dir t_write ds10 ds01 app];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[Nat.add Nat.mul csteps cstep ctape_move chd ctl t_next t_dir t_write ds10 ds01 app]);repeat rewrite app_nil_r;reflexivity.
Definition ds_run (c d:cconf):Prop:=exists k,csteps tm k c=Some d.
Lemma ds_trans : forall c d e,ds_run c d -> ds_run d e -> ds_run c e.
Proof. intros c d e(k&Hk)(j&Hj). exists(k+j). now rewrite csteps_add,Hk. Qed.
Lemma ds_A_sweep : forall k L,
 csteps tm(2*S k)(StA,(L,S0,ds10 k++[S1]))=
 Some(StA,(ds01(S k)++L,S0,[])).
Proof.
 induction k as[|k IH];intro L.
 - ds_compute.
 - replace(2*S(S k))with(2+2*S k)by lia. rewrite csteps_add.
   assert(E:csteps tm 2(StA,(L,S0,ds10(S k)++[S1]))=
     Some(StA,(S0::S1::L,S0,ds10 k++[S1])))by ds_compute.
   rewrite E,IH,ds01_push. reflexivity.
Qed.
Lemma ds_B_sweep : forall k L,
 csteps tm(2*k+3)(StB,(L,S0,ds10 k++[S1]))=
 Some(StC,(S1::ds01(S k)++L,S0,[])).
Proof.
 induction k as[|k IH];intro L.
 - ds_compute.
 - replace(2*S k+3)with(2+(2*k+3))by lia. rewrite csteps_add.
   assert(E:csteps tm 2(StB,(L,S0,ds10(S k)++[S1]))=
     Some(StB,(S0::S1::L,S0,ds10 k++[S1])))by ds_compute.
   rewrite E,IH,ds01_push. reflexivity.
Qed.
Lemma ds_C_sweep : forall k L R,
 csteps tm(2*k)(StC,(ds10 k++L,S0,R))=
 Some(StC,(L,S0,ds01 k++R)).
Proof.
 induction k as[|k IH];intros L R.
 - reflexivity.
 - replace(2*S k)with(2+2*k)by lia. rewrite csteps_add.
   assert(E:csteps tm 2(StC,(ds10(S k)++L,S0,R))=
     Some(StC,(ds10 k++L,S0,S0::S1::R)))by ds_compute.
   rewrite E,IH,ds01_push. reflexivity.
Qed.
Lemma ds_B_round : forall k L,
 ds_run(StB,(L,S0,ds10 k++[S1]))(StC,(S1::L,S0,ds01(S k))).
Proof.
 intros k L. exists((2*k+3)+2*S k). rewrite csteps_add,ds_B_sweep,ds_shift1.
 rewrite ds_C_sweep,app_nil_r. reflexivity.
Qed.
Lemma ds_inner : forall k m L,
 ds_run(StD,(ds10(S(S k))++S0::L,S0,ds10 m++[S1]))
       (StD,(ds10 k++S0::L,S0,ds10(m+4)++[S1])).
Proof.
 intros k m L.
 eapply ds_trans with(d:=(StB,(S0::S1::ds10(S k)++S0::L,S0,ds10 m++[S1]))).
 { exists 6. ds_compute. }
 eapply ds_trans;[apply ds_B_round|].
 eapply ds_trans with(d:=(StB,(S0::S0::ds10 k++S0::L,S0,ds10(S(S m))++[S1]))).
 { exists 5. rewrite <- (app_nil_r(ds01(S m))). rewrite <-ds_shift1.
   ds_compute. }
 eapply ds_trans;[apply ds_B_round|].
 exists 3.
 replace(m+4)with(S(S(S(S m))))by lia.
 rewrite <-ds_shift1. ds_compute.
Qed.
Lemma ds_drain : forall k m L,
 ds_run(StD,(ds10(2*k)++S0::L,S0,ds10 m++[S1]))
       (StD,(S0::L,S0,ds10(m+4*k)++[S1])).
Proof.
 induction k as[|k IH];intros m L.
 - replace(m+4*0)with m by lia. exists 0. reflexivity.
 - replace(2*S k)with(S(S(2*k)))by lia.
   eapply ds_trans;[apply ds_inner|].
   replace(m+4*S k)with((m+4)+4*k)by lia. apply IH.
Qed.
Lemma ds_frontier : forall L,
 csteps tm 13(StA,(S0::L,S0,[]))=
 Some(StD,(L,S0,ds10 2++[S1])).
Proof. intro L. ds_compute. Qed.
Lemma ds_exit : forall m L,
 csteps tm 4(StD,(S0::L,S0,ds10(S m)++[S1]))=
 Some(StA,(S0::S0::S1::L,S0,ds10 m++[S1])).
Proof. intros. ds_compute. Qed.
Lemma ds_A_return : forall k L,
 exists j,0<j /\ csteps tm j(StA,(S0::S0::L,S0,ds10(2*k+1)++[S1]))=
 Some(StA,(S0::S0::S1::L,S0,ds10(4*k+5)++[S1])).
Proof.
 intros k L.
 assert(H:ds_run(StA,(ds01(S(2*k+1))++S0::S0::L,S0,[]))
  (StA,(S0::S0::S1::L,S0,ds10(4*k+5)++[S1]))).
 { cbn[ds01 app]. rewrite ds_shift1.
   rewrite ds10_push.
   eapply ds_trans;[exists 13;apply ds_frontier|].
   replace(S(2*k+1))with(2*S k)by lia.
   eapply ds_trans;[apply ds_drain|].
   replace(2+4*S k)with(S(4*k+5))by lia.
   exists 4. apply ds_exit.
 }
 destruct H as(j&Hj). exists(2*S(2*k+1)+j). split;[lia|].
 now rewrite csteps_add,ds_A_sweep.
Qed.
Theorem ds_A0_recurrent : forall N,exists j,N<=j /\ FiresAt tm(StA,S0)j.
Proof.
 assert(H:forall N,exists t k L,N<=t /\
  csteps tm t c0=Some(StA,(S0::S0::L,S0,ds10(2*k+1)++[S1]))).
 { induction N as[|N IH].
   - exists 17,0,[S1]. split;[lia|]. unfold c0. ds_compute.
   - destruct IH as(t&k&L&Ht&Et).
     destruct(ds_A_return k L)as(j&Hj&Ej).
     exists(t+j),(2*k+2),(S1::L). split;[lia|].
     replace(2*(2*k+2)+1)with(4*k+5)by lia.
     now rewrite csteps_add,Et.
 }
 intro N. destruct(H N)as(t&k&L&Ht&Et). exists t. split;[exact Ht|].
 exists(lift(StA,(S0::S0::L,S0,ds10(2*k+1)++[S1]))).
 split;[rewrite <-lift_c0;apply csteps_lift;exact Et|reflexivity].
Qed.
Lemma ds_frontier_fires : forall L q s,
 exists j c,csteps tm j(StA,(S0::S1::S0::S1::L,S0,[]))=Some c /\
   cinstr c=(q,s).
Proof.
 intros L q s. destruct q,s.
 - exists 0. eexists. split;[ds_compute|reflexivity].
 - exists 15. eexists. split;[ds_compute|reflexivity].
 - exists 1. eexists. split;[ds_compute|reflexivity].
 - exists 14. eexists. split;[ds_compute|reflexivity].
 - exists 2. eexists. split;[ds_compute|reflexivity].
 - exists 4. eexists. split;[ds_compute|reflexivity].
 - exists 13. eexists. split;[ds_compute|reflexivity].
 - exists 3. eexists. split;[ds_compute|reflexivity].
Qed.
Definition ds_anchor (n k:nat):cconf:=
 (StA,(S0::S0::repeat S1(S n),S0,ds10(2*k+1)++[S1])).
Lemma ds_anchor_lap : forall n k, exists j,
 csteps tm j(ds_anchor n k)=Some(ds_anchor(S n)(2*k+2)) /\ 0<j.
Proof.
 intros n k. destruct(ds_A_return k(repeat S1(S n)))as(j&Hj&Ej).
 exists j. split;[|exact Hj]. unfold ds_anchor.
 replace(2*(2*k+2)+1)with(4*k+5)by lia. exact Ej.
Qed.
Lemma ds_anchor_fires : forall n k t, exists j c,
 csteps tm j(ds_anchor n k)=Some c /\ cinstr c=t.
Proof.
 intros n k [q s].
 assert(E:ds01(S(2*k+1))++S0::S0::repeat S1(S n)=
    S0::S1::S0::S1::(ds01(2*k)++S0::S0::repeat S1(S n))).
 { replace(S(2*k+1))with(S(S(2*k)))by lia. reflexivity. }
 destruct(ds_frontier_fires(ds01(2*k)++S0::S0::repeat S1(S n))q s)
   as(j&c&Hc&Hins).
 exists(2*S(2*k+1)+j),c. split.
 - unfold ds_anchor. now rewrite csteps_add,ds_A_sweep,E.
 - exact Hins.
Qed.
Theorem ds_neverqhtr : NeverQuasiHaltsTr tm.
Proof.
 apply(value_lap_neverqhtr tm nat(fun k=>2*k+2)ds_anchor 0).
 - exists 17. rewrite <-lift_c0. apply csteps_lift.
   unfold c0,ds_anchor. ds_compute.
 - intros n k. destruct(ds_anchor_lap n k)as(j&Ej&Hj).
   exists j,(ds_anchor(S n)(2*k+2)). split;[exact Ej|].
   split;[reflexivity|exact Hj].
 - apply ds_anchor_fires.
Qed.
End Machine.
