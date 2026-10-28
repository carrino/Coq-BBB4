(** Lexicographic rankings whose local tests need only preserve signs.
    Unlike additive count rankings, place-value rankings change scale when
    the head moves.  Their concrete values are still natural numbers. *)
From Coq Require Import Arith Lia Bool List.
From BBB24 Require Import Statement StatementTr CTape Closure ClosureTr.
Import ListNotations.

Record wlcomp := mkWL {
 wl_value : cconf -> nat;
 wl_strict : cconf -> cconf -> bool;
 wl_noninc : cconf -> cconf -> bool
}.
Definition wl_tuple cs c := map (fun k=>wl_value k c) cs.
Fixpoint wl_edge cs a b := match cs with
 | []=>false
 | k::ks=>if wl_strict k a b then true
           else if wl_noninc k a b then wl_edge ks a b else false
 end.

Section Sound.
Variable tm:TM.
Variable succs:cconf->option(list cconf).
Variable covers:cconf->cconf->Prop.
Variable Inv:cconf->Prop.
Variable target:Instr.
Variable Sl:list cconf.
Hypothesis Hlabel:forall a c,covers a c->cinstr a=cinstr c.
Hypothesis Hclosed:forall a c,In a Sl->covers a c->
 exists d l b,cstep tm c=Some d /\ succs a=Some l /\ In b l /\ In b Sl /\ covers b d.
Hypothesis Hinv:forall c d,Inv c->cinstr c<>target->cstep tm c=Some d->Inv d.
Definition wl_sound k := forall a c b d l,
 In a Sl->In b Sl->covers a c->covers b d->Inv c->Inv d->
 cinstr c<>target->cinstr d<>target->
 cstep tm c=Some d->succs a=Some l->In b l->
 (wl_strict k a b=true -> wl_value k d<wl_value k c) /\
 (wl_noninc k a b=true -> wl_value k d<=wl_value k c).

Lemma wl_decrease:forall ks a c b d l,
 Forall wl_sound ks->In a Sl->In b Sl->covers a c->covers b d->Inv c->Inv d->
 cinstr c<>target->cinstr d<>target->
 cstep tm c=Some d->succs a=Some l->In b l->wl_edge ks a b=true->
 lexlt(wl_tuple ks d)(wl_tuple ks c).
Proof.
 induction ks as[|k ks IH];intros a c b d l HK HA HB HC HD HI HJ HN HM HS HE HL E;
 cbn [wl_edge] in E;[discriminate|].
 inversion HK as[|? ? Hk Hks];subst.
 destruct(Hk a c b d l HA HB HC HD HI HJ HN HM HS HE HL)as[Ht Hle].
 assert(L:length(wl_tuple ks d)=length(wl_tuple ks c))by(unfold wl_tuple;now rewrite !map_length).
 cbn [wl_tuple map lexlt].
 destruct(wl_strict k a b)eqn:Et.
 - left;split;[now apply Ht|exact L].
 - destruct(wl_noninc k a b)eqn:El;[|discriminate].
   specialize(Hle eq_refl). destruct(Nat.lt_ge_cases(wl_value k d)(wl_value k c)).
   + left;auto.
   + right;split;[lia|]. exact(IH a c b d l Hks HA HB HC HD HI HJ HN HM HS HE HL E).
Qed.

Definition wl_ok ks := forallb(fun a=>
 if instr_eqb(cinstr a)target then true else
 match succs a with None=>false|Some l=>
 forallb(fun b=>if instr_eqb(cinstr b)target then true else wl_edge ks a b)l end)Sl.

Theorem wl_reach:forall ks,Forall wl_sound ks->wl_ok ks=true->
 forall c a,Inv c->In a Sl->covers a c->
 exists j d,csteps tm j c=Some d /\ cinstr d=target.
Proof.
 intros ks HK HO.
 assert(H:forall tuple,Acc lexlt tuple->forall c a,tuple=wl_tuple ks c->
 Inv c->In a Sl->covers a c->exists j d,csteps tm j c=Some d /\ cinstr d=target).
 { intros tuple HA;induction HA as[tuple HA IH];intros c a -> HI Hin HC.
   destruct(instr_eqb(cinstr a)target)eqn:Et.
   - apply instr_eqb_spec in Et. exists 0,c;split;[reflexivity|rewrite <-(Hlabel a c HC);exact Et].
   - assert(HN:cinstr c<>target)by(intro E;rewrite <-(Hlabel a c HC)in E;apply instr_eqb_spec in E;congruence).
     destruct(Hclosed a c Hin HC)as(d&l&b&HS&HE&HL&HB&HD).
     destruct(instr_eqb(cinstr b)target)eqn:Eu.
     + apply instr_eqb_spec in Eu. exists 1,d;split;[cbn [csteps];rewrite HS;reflexivity|rewrite <-(Hlabel b d HD);exact Eu].
     + assert(HM:cinstr d<>target)by(intro E;rewrite <-(Hlabel b d HD)in E;apply instr_eqb_spec in E;congruence).
       assert(HJ:Inv d)by(eapply Hinv;eauto).
       assert(E:wl_edge ks a b=true).
       { unfold wl_ok in HO;rewrite forallb_forall in HO.
         specialize(HO a Hin);rewrite Et,HE in HO.
         rewrite forallb_forall in HO;specialize(HO b HL);now rewrite Eu in HO. }
       destruct(IH(wl_tuple ks d)(wl_decrease ks a c b d l HK Hin HB HC HD HI HJ HN HM HS HE HL E)
         d b eq_refl HJ HB HD)as(j&e&Hr&Ht).
       exists(S j),e;split;[cbn [csteps];now rewrite HS|exact Ht]. }
 intros c a HI HA HC. eapply H;[apply(lexlt_wf_len(length(wl_tuple ks c)));reflexivity|reflexivity|exact HI|exact HA|exact HC].
Qed.
End Sound.
