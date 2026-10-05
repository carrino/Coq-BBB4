(** * Transition witnesses for the M block-list core.

    The positive binary-fold rank terminates every B1-avoiding run
    inside the protected wall. Its continuation form retains the broad
    invariant at B1, giving C1 as well. The stronger frontier invariant
    connects both permitted empty-right frontier phases to that wall.
    A separate finite A1 rank supplies A1, D0, and D1 witnesses.

    Together with marked B0 returns, these prove all six instructions
    unresolved by the existing partial fuel certificate (A0/C0).
*)
From Coq Require Import Arith Lia List Bool.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr BlockCoreMRankTr BlockCoreMReturnTr BlockCoreMStrongTr BlockCoreMWallTr BlockCoreMFireRankTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Lemma mg_wall_broad:forall L,bm_inv(cL StD L (mw_guard++[S0])).
Proof. intros L;unfold bm_inv,cL;destruct(chd L),(chd(ctl L)),(chd(ctl(ctl L))),(chd(ctl(ctl(ctl L))));reflexivity. Qed.
From BBB4.Counters Require Import BlockCoreMB1FoldTr.
Lemma mg_wall_seed:forall L,mw_inv(cL StD L(mw_guard++[S0])).
Proof. intro L;unfold mw_inv,cL;destruct(chd L);reflexivity. Qed.
Definition mg_wall(c:cconf):Prop:=bm_inv c /\ mw_inv c.
Section Machine.
Variable tm:TM.
Hypothesis Htm:forall q h,tm q h=bm_tm q h.
Lemma mg_wall_fires:forall t,
 (forall c,bm_inv c->cinstr c=(StB,S1)->Fires tm c t)->
 forall c,mg_wall c->Fires tm c t.
Proof.
 intros t HT. apply(bmf_fires_after tm Htm mg_wall t).
 - intros c d[HB HW]HN HD HS;split.
   + eapply bm_step;eauto.
   + eapply mw_step;eauto.
 - intros c[HB _]HE;apply HT;assumption.
 - intros q L h[_ HW]HN HD;exfalso;apply HN;apply mw_empty with L;exact HW.
Qed.
Lemma mg_guard_fires:forall t,
 (forall c,bm_inv c->cinstr c=(StB,S1)->Fires tm c t)->
 forall U,Fires tm(cL StD U mw_guard)t.
Proof.
 intros t HT U;eapply(fire_back tm _ (cL StD U(mw_guard++[S0])));[|apply mg_wall_fires;[exact HT|split;[apply mg_wall_broad|apply mg_wall_seed]]].
 eapply reach0_lift_r;[|apply reach0_refl]. unfold cL.
 change(lift(StD,(ctl U,chd U,mw_guard++rep[S0]1))=lift(StD,(ctl U,chd U,mw_guard))).
 apply lift_padR.
Qed.
Lemma mg_frontier_fires:forall t,
 (forall c,bm_inv c->cinstr c=(StB,S1)->Fires tm c t)->
 forall L,ms_inv(StB,(L,S0,[]))->Fires tm(StB,(L,S0,[]))t.
Proof.
 intros t HT L HI. apply ms_frontier,ms_guard_shape in HI.
 destruct HI as[[U ->]|[U ->]].
 - eapply fire_back;[apply mw_phase0;exact Htm|].
   eapply fire_back;[apply mw_phase1;exact Htm|apply mg_guard_fires;exact HT].
 - eapply fire_back;[apply mw_phase1;exact Htm|apply mg_guard_fires;exact HT].
Qed.
Lemma mg_full_fires:forall t,
 (forall c,bm_inv c->cinstr c=(StB,S1)->Fires tm c t)->
 forall c,ms_full c->Fires tm c t.
Proof.
 intros t HT. apply(bmf_fires_after tm Htm ms_full t).
 - intros c d HI HN HD HS;eapply ms_full_step;eauto.
 - intros c[HB _]HE;apply HT;assumption.
 - intros q L h HI HN HD.
   pose proof(proj1 HI)as HB;apply bm_empty in HB.
   destruct HB as[[-> ->]|[[-> ->]|[-> ->]]].
   + set(d:=(StB,(S0::L,S0,[])):cconf).
     assert(HS:cstep tm(StA,(L,S0,[]))=Some d)by(cbn[cstep];rewrite Htm;reflexivity).
     assert(HI':ms_full d)by(eapply ms_full_step;[exact Htm|exact HS|exact HI|left;discriminate]).
     eapply(fire_back tm _ d).
     * eapply(r0_run _ 1);[cbn[csteps];rewrite HS;reflexivity|apply reach0_refl].
     * apply mg_frontier_fires;[exact HT|exact(proj2 HI')].
   + apply mg_frontier_fires;[exact HT|exact(proj2 HI)].
   + discriminate HD.
Qed.
Lemma mg_B1:forall c,ms_full c->Fires tm c(StB,S1).
Proof. apply mg_full_fires;intros;apply fires_here;assumption. Qed.
Lemma mg_C1:forall c,ms_full c->Fires tm c(StC,S1).
Proof.
 apply mg_full_fires;intros[q[[L h]R]]HI HE;cbn[cinstr]in HE;injection HE as -> ->.
 apply bm_B1_C1;assumption.
Qed.
Lemma mg_A1:forall c,ms_full c->Fires tm c(StA,S1).
Proof.
 intros c[HI _]. destruct(bmfr_A1 tm Htm c HI)as(d&HD&HT&HR).
 eapply fire_back;[exact HR|apply fires_here;exact HT].
Qed.
Lemma mg_D0:forall c,ms_full c->Fires tm c(StD,S0).
Proof.
 intros c[HI _]. destruct(bmfr_A1 tm Htm c HI)as([q[[L h]R]]&HD&HT&HR).
 cbn[cinstr]in HT;injection HT as -> ->.
 eapply fire_back;[exact HR|apply bm_A1_D0;exact Htm].
Qed.
Lemma mg_D1:forall c,ms_full c->Fires tm c(StD,S1).
Proof.
 intros c[HI _]. destruct(bmfr_A1 tm Htm c HI)as([q[[L h]R]]&HD&HT&HR).
 cbn[cinstr]in HT;injection HT as -> ->.
 eapply fire_back;[exact HR|apply bm_A1_D1;exact Htm].
Qed.
Theorem mg_mark_fires:forall c t,ms_mark c->t<>(StA,S0)->t<>(StC,S0)->Fires tm c t.
Proof.
 intros c[q h][HI HT]HA HC;destruct q,h;try contradiction;
 [apply mg_A1|apply fires_here|apply mg_B1|apply mg_C1|apply mg_D0|apply mg_D1];assumption.
Qed.
End Machine.
