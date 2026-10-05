(** The productive run grammar instantiates the exact word carries. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr BlockCoreLWordsTr.
From BBB4.Counters Require Import BlockCoreLReturnTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Lemma bl_runs_head:forall xs,Forall(fun a=>1<=a)xs->xs<>[]->
 exists w,bl_runs xs=S1::w.
Proof.
 intros[|a xs]HP HN;[contradiction|]. inversion HP;subst.
 destruct a;[lia|]. destruct xs;cbn[bl_runs repeat app];eexists;reflexivity.
Qed.
Theorem bl_run_map:forall xs ys,bl_tr xs ys->Forall(fun a=>1<=a)xs->
 bl_word_map(bl_runs xs)(bl_runs ys).
Proof.
 intros xs ys H;induction H;intro HP.
 - change(bl_word_map[S1][S1;S1;S0;S1]);constructor.
 - destruct b;[lia|]. replace(S b+3)with(S(S(S(S b))))by lia.
   destruct xs;cbn[bl_runs repeat app];apply blw_stop.
 - assert(HN:ys<>[])by(exact(proj2(bl_tr_nonempty _ _ H0))).
   assert(HPP:Forall(fun a=>1<=a)(a::xs)).
   { inversion HP;subst;constructor;assumption. }
   specialize(IHbl_tr HPP).
   destruct a;[lia|]. destruct ys as[|b ys];[contradiction|].
   destruct xs;cbn[bl_runs repeat app]in*;apply blw_carry11;exact IHbl_tr.
 - destruct(bl_tr_nonempty _ _ H)as[HX HY].
   assert(HPP:Forall(fun a=>1<=a)xs)by(inversion HP;assumption).
   specialize(IHbl_tr HPP).
   destruct(bl_runs_head xs HPP HX)as(w&HW).
   assert(HI:bl_inc ys<>[])by(destruct ys;cbn[bl_inc];congruence).
   change(bl_word_map(repeat S1 2++match xs with[]=>[]|_::_=>S0::bl_runs xs end)
     (repeat S1 1++match bl_inc ys with[]=>[]|_::_=>S0::bl_runs(bl_inc ys)end)).
   destruct xs as[|a xs];[contradiction|].
   destruct ys as[|b ys];[contradiction|].
   cbn[repeat app bl_inc].
   change(bl_word_map(S1::S1::S0::bl_runs(a::xs))(S1::S0::bl_runs(bl_inc(b::ys)))).
   rewrite bl_runs_inc by discriminate. rewrite HW in*.
   apply blw_carry110;exact IHbl_tr.
Qed.
Inductive bl_mark:cconf->Prop:=
| bl_mark_runs:forall xs,bl_good xs->bl_mark(bl_anchor(bl_runs(4::xs))).
Section Machine.
Variable tm:TM.
Hypotheses
 (HA0:tm StA S0=Some(mkTrans S1 DR StB))
 (HA1:tm StA S1=Some(mkTrans S1 DR StA))
 (HB0:tm StB S0=Some(mkTrans S0 DL StC))
 (HB1:tm StB S1=Some(mkTrans S0 DR StA))
 (HC0:tm StC S0=Some(mkTrans S1 DL StC))
 (HC1:tm StC S1=Some(mkTrans S1 DL StD))
 (HD0:tm StD S0=Some(mkTrans S1 DL StA))
 (HD1:tm StD S1=Some(mkTrans S0 DL StC)).
Lemma bl_mark_step:forall xs,bl_good xs->exists ys,bl_good ys/\
 Reach1 tm(bl_anchor(bl_runs(4::xs)))(bl_anchor(bl_runs(4::ys))).
Proof.
 intros xs HG;destruct(bl_good_step _ HG)as(ys&HU&HY).
 destruct(bl_pair_step _ _ HU)as(z&HT&HT').
 assert(HP:Forall(fun a=>1<=a)(4::xs))by(constructor;[lia|apply bl_good_positive;exact HG]).
 exists ys;split;[exact HY|].
 eapply reach10 with(b:=bl_anchor(bl_runs z)).
 - apply bl_lap;try assumption. exact(bl_run_map _ _ HT HP).
 - apply reach1_0,bl_lap;try assumption. apply bl_run_map;[exact HT'|].
   eapply bl_tr_positive;eassumption.
Qed.
Theorem bl_mark_return:forall c,bl_mark c->exists d,bl_mark d/\Reach1 tm c d.
Proof.
 intros c H;inversion H;subst;destruct(bl_mark_step _ H0)as(ys&HY&HR).
 exists(bl_anchor(bl_runs(4::ys)));split;[constructor;exact HY|exact HR].
Qed.
Theorem bl_mark_fires:forall c,bl_mark c->forall q,Fires tm c q.
Proof.
 intros c H q;inversion H;subst.
 destruct(bl_good_step _ H0)as(ys&HU&HY);destruct(bl_pair_step _ _ HU)as(z&HT&HT').
 assert(HP:Forall(fun a=>1<=a)(4::xs))by(constructor;[lia|apply bl_good_positive;exact H0]).
 pose proof(bl_run_map _ _ HT HP)as HM.
 destruct xs as[|a xs];[exfalso;exact(bl_good_nonempty _ H0 eq_refl)|].
 cbn[bl_runs repeat app]in HM|-*.
 eapply bl_anchor_fires;try eassumption.
Qed.
End Machine.
