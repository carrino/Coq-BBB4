(** * UnaryFrontierTr: finite unary transfers with a doubling reset.

    At a right frontier in D0, the left tape is [0^a 1^b 0 L].
    A short turn changes [(a,b)=(0,3k+2)] to [(4,3k+1)].
    Each inner round then changes [(a,b)] to [(a+6,b-3)].
    After exactly [k] rounds, [b=1]; the reset replaces the left tape
    by [1^(a+4) 0 1 L].  Thus the anchor parameters change as
    [(n,k) -> (n+1,2k+2)].  All eight instructions have explicit
    witnesses during the reset.  The three local sweep inductions and
    the finite drain are independent of the unread suffix [L]. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import ValueLapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Lemma uf_repeat_push : forall (s:Sym) k L,
 repeat s k++s::L=repeat s(S k)++L.
Proof. induction k;intro L;cbn[repeat app];[reflexivity|now rewrite IHk]. Qed.
Section Machine.
Variable tm:TM.
Hypothesis HA0:tm StA S0=Some(mkTrans S1 DR StB).
Hypothesis HA1:tm StA S1=Some(mkTrans S0 DL StB).
Hypothesis HB0:tm StB S0=Some(mkTrans S0 DR StC).
Hypothesis HB1:tm StB S1=Some(mkTrans S0 DR StD).
Hypothesis HC0:tm StC S0=Some(mkTrans S1 DL StC).
Hypothesis HC1:tm StC S1=Some(mkTrans S1 DL StA).
Hypothesis HD0:tm StD S0=Some(mkTrans S1 DR StA).
Hypothesis HD1:tm StD S1=Some(mkTrans S1 DR StD).
Local Ltac uf_compute:=
 cbn[Nat.add Nat.mul csteps cstep ctape_move chd ctl t_next t_dir t_write repeat app];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[Nat.add Nat.mul csteps cstep ctape_move chd ctl t_next t_dir t_write repeat app]);
 repeat rewrite app_nil_r;reflexivity.
Definition uf_run(c d:cconf):Prop:=exists k,csteps tm k c=Some d.
Lemma uf_trans:forall c d e,uf_run c d->uf_run d e->uf_run c e.
Proof. intros c d e(k&Hk)(j&Hj). exists(k+j). now rewrite csteps_add,Hk. Qed.
Lemma uf_D0_sweep:forall k L,
 csteps tm(3*k)(StD,(L,S0,repeat S1 k))=
 Some(StD,(repeat S0 k++L,S0,[])).
Proof.
 induction k as[|k IH];intro L;[reflexivity|].
 replace(3*S k)with(3+3*k)by lia. rewrite csteps_add.
 assert(E:csteps tm 3(StD,(L,S0,repeat S1(S k)))=
 Some(StD,(S0::L,S0,repeat S1 k)))by uf_compute.
 now rewrite E,IH,uf_repeat_push.
Qed.
Lemma uf_C0_sweep:forall k L R,
 csteps tm(S k)(StC,(repeat S0 k++S1::L,S0,R))=
 Some(StC,(L,S1,repeat S1(S k)++R)).
Proof.
 induction k as[|k IH];intros L R.
 - uf_compute.
 - replace(S(S k))with(1+S k)by lia. rewrite csteps_add.
   assert(E:csteps tm 1(StC,(repeat S0(S k)++S1::L,S0,R))=
   Some(StC,(repeat S0 k++S1::L,S0,S1::R)))by uf_compute.
   now rewrite E,IH,uf_repeat_push.
Qed.
Lemma uf_D1_sweep:forall k L,
 csteps tm(S k)(StD,(L,S1,repeat S1 k))=
 Some(StD,(repeat S1(S k)++L,S0,[])).
Proof.
 induction k as[|k IH];intro L.
 - uf_compute.
 - replace(S(S k))with(1+S k)by lia. rewrite csteps_add.
   assert(E:csteps tm 1(StD,(L,S1,repeat S1(S k)))=
    Some(StD,(S1::L,S1,repeat S1 k)))by uf_compute.
   now rewrite E,IH,uf_repeat_push.
Qed.
Lemma uf_short:forall L,
 csteps tm 17(StD,(S1::L,S0,[]))=
 Some(StD,(repeat S0 4++L,S0,[])).
Proof.
 intro L. change 17 with(8+3*3). rewrite csteps_add.
 assert(E:csteps tm 8(StD,(S1::L,S0,[]))=
 Some(StD,(S0::L,S0,repeat S1 3)))by uf_compute.
 rewrite E,uf_D0_sweep. reflexivity.
Qed.
Lemma uf_enter:forall a L,
 csteps tm 8(StD,(repeat S0(S a)++L,S0,[]))=
 Some(StC,(repeat S0(S a)++L,S0,[S1;S1;S1])).
Proof. intros. uf_compute. Qed.
Lemma uf_inner:forall a L,
 uf_run(StD,(repeat S0(S a)++S1::S1::S1::S1::L,S0,[]))
       (StD,(repeat S0(S a+6)++S1::L,S0,[])).
Proof.
 intros a L. exists(8+(S(S a)+(3+3*(S a+5)))).
 rewrite csteps_add,uf_enter,csteps_add,uf_C0_sweep.
 replace(repeat S1(S(S a))++[S1;S1;S1])with(repeat S1(S a+4)).
 2:{ change[S1;S1;S1]with(repeat S1 3). rewrite <-repeat_app. f_equal;lia. }
 rewrite csteps_add.
 assert(E:csteps tm 3(StC,(S1::S1::S1::L,S1,repeat S1(S a+4)))=
   Some(StD,(S0::S1::L,S0,repeat S1(S a+5)))).
 { replace(S a+5)with(S(S a+4))by lia. uf_compute. }
 rewrite E,uf_D0_sweep,uf_repeat_push.
 replace(S(S a+5))with(S a+6)by lia. reflexivity.
Qed.
Lemma uf_reset:forall a L,
 uf_run(StD,(repeat S0(S a)++S1::S0::L,S0,[]))
       (StD,(repeat S1(S a+4)++S0::S1::L,S0,[])).
Proof.
 intros a L. exists(8+(S(S a)+(3+S(S a+3)))).
 rewrite csteps_add,uf_enter,csteps_add,uf_C0_sweep.
 replace(repeat S1(S(S a))++[S1;S1;S1])with(repeat S1(S a+4)).
 2:{ change[S1;S1;S1]with(repeat S1 3). rewrite <-repeat_app. f_equal;lia. }
 rewrite csteps_add.
 assert(E:csteps tm 3(StC,(S0::L,S1,repeat S1(S a+4)))=
   Some(StD,(S0::S1::L,S1,repeat S1(S a+3)))).
 { replace(S a+4)with(S(S a+3))by lia. uf_compute. }
 rewrite E,uf_D1_sweep. replace(S(S a+3))with(S a+4)by lia. reflexivity.
Qed.
Lemma uf_drain:forall k a L,
 uf_run(StD,(repeat S0(S a)++repeat S1(3*k+1)++L,S0,[]))
       (StD,(repeat S0(S a+6*k)++S1::L,S0,[])).
Proof.
 induction k as[|k IH];intros a L.
 - replace(S a+6*0)with(S a)by lia. exists 0. reflexivity.
 - replace(3*S k+1)with(S(S(S(S(3*k)))))by lia.
   cbn[repeat].
   eapply uf_trans;[apply uf_inner|].
   replace(S a+6)with(S(a+6))by lia.
   replace(S a+6*S k)with(S(a+6)+6*k)by lia.
   specialize(IH(a+6)L). replace(3*k+1)with(S(3*k))in IH by lia. exact IH.
Qed.
Definition uf_anchor(n k:nat):cconf:=
 (StD,(repeat S1(3*k+2)++S0::repeat S1(S n),S0,[])).
Lemma uf_reach_reset:forall n k,
 uf_run(uf_anchor n k)(StD,(repeat S0(4+6*k)++S1::S0::repeat S1(S n),S0,[])).
Proof.
 intros n k. unfold uf_anchor.
 replace(3*k+2)with(S(3*k+1))by lia. cbn[repeat app].
 eapply uf_trans;[exists 17;apply uf_short|]. apply(uf_drain k 3).
Qed.
Lemma uf_lap:forall n k,exists j,
 csteps tm j(uf_anchor n k)=Some(uf_anchor(S n)(2*k+2))/\0<j.
Proof.
 intros n k. unfold uf_anchor at 1.
 replace(3*k+2)with(S(3*k+1))by lia. cbn[repeat app].
 destruct(uf_drain k 3(S0::repeat S1(S n)))as(i&Ei).
 destruct(uf_reset(3+6*k)(repeat S1(S n)))as(j&Ej).
 exists(17+(i+j)). split;[|lia].
 rewrite csteps_add,uf_short,csteps_add.
 change(S1::repeat S1 n)with(repeat S1(S n)). rewrite Ei.
 replace(4+6*k)with(S(3+6*k))by lia. rewrite Ej.
 unfold uf_anchor. replace(3*(2*k+2)+2)with(S(3+6*k)+4)by lia. reflexivity.
Qed.
Lemma uf_reset_fires:forall a L t,
 exists j c,csteps tm j(StD,(repeat S0(S a)++S1::S0::L,S0,[]))=Some c /\cinstr c=t.
Proof.
 intros a L [q s].
 assert(HC: csteps tm(8+S(S a))(StD,(repeat S0(S a)++S1::S0::L,S0,[]))=
   Some(StC,(S0::L,S1,repeat S1(S a+4)))).
 { rewrite csteps_add,uf_enter,uf_C0_sweep.
   change[S1;S1;S1]with(repeat S1 3). rewrite <-repeat_app.
   replace(S(S a)+3)with(S a+4)by lia. reflexivity. }
 destruct q,s.
 - exists 1. eexists. split;[uf_compute|reflexivity].
 - exists 6. eexists. split;[uf_compute|reflexivity].
 - exists 2. eexists. split;[uf_compute|reflexivity].
 - exists((8+S(S a))+2). eexists. split.
   + rewrite csteps_add,HC. uf_compute.
   + reflexivity.
 - exists 3. eexists. split;[uf_compute|reflexivity].
 - exists 5. eexists. split;[uf_compute|reflexivity].
 - exists 0. eexists. split;[uf_compute|reflexivity].
 - exists((8+S(S a))+3). eexists. split.
   + rewrite csteps_add,HC. replace(S a+4)with(S(S a+3))by lia. uf_compute.
   + reflexivity.
Qed.
Lemma uf_fires:forall n k t,exists j c,
 csteps tm j(uf_anchor n k)=Some c /\cinstr c=t.
Proof.
 intros n k t. destruct(uf_reach_reset n k)as(i&Ei).
 destruct(uf_reset_fires(3+6*k)(repeat S1(S n))t)as(j&c&Ej&Ht).
 exists(i+j),c. split;[|exact Ht]. rewrite csteps_add,Ei.
 replace(4+6*k)with(S(3+6*k))by lia. exact Ej.
Qed.
Theorem uf_neverqhtr:NeverQuasiHaltsTr tm.
Proof.
 apply(value_lap_neverqhtr tm nat(fun k=>2*k+2)uf_anchor 0).
 - exists 9. rewrite <-lift_c0. apply csteps_lift. unfold c0,uf_anchor. uf_compute.
 - intros n k. destruct(uf_lap n k)as(j&Ej&Hj).
   exists j,(uf_anchor(S n)(2*k+2)). split;[exact Ej| ]. split;[reflexivity|exact Hj].
 - apply uf_fires.
Qed.
End Machine.
