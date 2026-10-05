(** Positive binary-fold descent for core M until B1 or a right boundary. *)
From Coq Require Import Arith Lia List ZArith Bool.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr FiniteWallTr BinaryStackRankTr BlockCoreMRankTr BlockCoreMReturnTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Local Open Scope Z_scope.
From BBB4.Counters Require Import BlockCoreMB1FoldDataTr.
Lemma bmf_fl_bound:forall L,2*bmf_vl L<=bmf_fl L+bmf_vl(ctl L).
Proof.
 intro L;pose proof bmf_fl_checked as HC;unfold bmf_fl_check in HC.
 pose proof(bmf_allW_sound 7 _ HC(bmf_pref 7 L)(bmf_pref_length 7 L))as H.
 apply Z.leb_le in H.
 change(2*bmf_get bmf_vl_data(bmf_pref 7 L)<=
 bmf_get bmf_ls_data(bmf_pref 7 L)+bmf_get bmf_vl_data(bmf_pref 6(ctl L)))in H.
 rewrite !bmf_get_pref in H by lia;exact H.
Qed.
Lemma bmf_fr_bound:forall R,bmf_vr R<=bmf_fr R+2*bmf_vr(ctl R).
Proof.
 intro R;pose proof bmf_fr_checked as HC;unfold bmf_fr_check in HC.
 pose proof(bmf_allW_sound 7 _ HC(bmf_pref 7 R)(bmf_pref_length 7 R))as H.
 apply Z.leb_le in H.
 change(bmf_get bmf_vr_data(bmf_pref 7 R)<=
 bmf_get bmf_rs_data(bmf_pref 7 R)+2*bmf_get bmf_vr_data(bmf_pref 6(ctl R)))in H.
 rewrite !bmf_get_pref in H by lia;exact H.
Qed.
Lemma bmf_bias_bound:forall q L h R,(q,h)<>(StB,S1)->
 0<=bmf_vl L+bmf_vr R+bmf_bias(q,(L,h,R)).
Proof.
 intros q L h R HN.
 pose proof bmf_positive_checked as HC;unfold bmf_positive_check in HC.
 pose proof(bmf_allQ_sound _ HC q)as H.
 pose proof(bmf_allS_sound _ H h)as Hh.
 pose proof(bmf_allW_sound 6 _ Hh(bmf_pref 6 L)(bmf_pref_length 6 L))as HL.
 pose proof(bmf_allW_sound 6 _ HL(bmf_pref 6 R)(bmf_pref_length 6 R))as HR.
 destruct(instr_eqb(q,h)(StB,S1))eqn:E.
 - apply instr_eqb_spec in E;contradiction.
 - apply Z.leb_le in HR. unfold bmf_vl,bmf_vr,bmf_bias in HR|-*.
   rewrite !bmf_get_pref in HR by lia;exact HR.
Qed.
Lemma bmf_get_cons_pref:forall A n(t:bmf_tree A n)m a w,(n<=S m)%nat->
 bmf_get t(a::bmf_pref m w)=bmf_get t(a::w).
Proof.
 intros A n t;destruct t as[z|n l r];intros m a w H;[reflexivity|].
 cbn[bmf_get chd ctl];destruct a;apply bmf_get_pref;lia.
Qed.
Lemma bmf_pref_hd:forall n w,chd(bmf_pref(S n)w)=chd w.
Proof. reflexivity. Qed.
Lemma bmf_pref_tl:forall n w,ctl(bmf_pref(S n)w)=bmf_pref n(ctl w).
Proof. reflexivity. Qed.
Lemma bmf_delta_pref:forall q L h R tr,
 bsr_delta bmf_fl bmf_fr bmf_bias(q,(bmf_pref 7 L,h,bmf_pref 7 R))tr=
 bsr_delta bmf_fl bmf_fr bmf_bias(q,(L,h,R))tr.
Proof.
 intros q L h R[w dir p];destruct dir;
 unfold bsr_delta,bmf_fl,bmf_fr,bmf_bias;
 cbn[t_dir t_next t_write ctape_move];
 rewrite ?bmf_pref_hd,?bmf_pref_tl;
 repeat rewrite bmf_get_pref by lia;
 repeat rewrite bmf_get_cons_pref by lia;reflexivity.
Qed.
Lemma bmf_delta_negative:forall q L h R tr,bmf_tm q h=Some tr->
 (q,h)<>(StB,S1)->cinstr(t_next tr,ctape_move(t_dir tr)(t_write tr)(L,h,R))<>(StB,S1)->
 bsr_delta bmf_fl bmf_fr bmf_bias(q,(L,h,R))tr<0.
Proof.
 intros q L h R tr HT HC HD.
 pose proof bmf_delta_checked as H;unfold bmf_delta_check in H.
 pose proof(bmf_allQ_sound _ H q)as Hq.
 pose proof(bmf_allS_sound _ Hq h)as Hh.
 pose proof(bmf_allW_sound 7 _ Hh(bmf_pref 7 L)(bmf_pref_length 7 L))as HL.
 pose proof(bmf_allW_sound 7 _ HL(bmf_pref 7 R)(bmf_pref_length 7 R))as HR.
 rewrite HT in HR;cbn beta iota zeta in HR.
 assert(EC:instr_eqb(q,h)(StB,S1)=false).
 { destruct(instr_eqb(q,h)(StB,S1))eqn:E;[apply instr_eqb_spec in E;contradiction|reflexivity]. }
 assert(ED:instr_eqb(cinstr(t_next tr,ctape_move(t_dir tr)(t_write tr)
   (bmf_pref 7 L,h,bmf_pref 7 R)))(StB,S1)=false).
 { assert(E:cinstr(t_next tr,ctape_move(t_dir tr)(t_write tr)
   (bmf_pref 7 L,h,bmf_pref 7 R))=
   cinstr(t_next tr,ctape_move(t_dir tr)(t_write tr)(L,h,R))).
   { destruct tr as[w[]p];cbn[ctape_move t_next t_dir t_write];unfold cinstr;cbn;reflexivity. }
   rewrite E;destruct(instr_eqb(cinstr(t_next tr,ctape_move(t_dir tr)(t_write tr)(L,h,R)))(StB,S1))eqn:F;[apply instr_eqb_spec in F;contradiction|reflexivity]. }
 rewrite EC,ED in HR;cbn[orb]in HR;apply Z.ltb_lt in HR.
 rewrite bmf_delta_pref in HR;exact HR.
Qed.
Lemma bmf_positive:forall c,cinstr c<>(StB,S1)->0<=bsr_potential bmf_fl bmf_fr bmf_bias c.
Proof.
 intros[q[[L h]R]] H;apply(bsr_prefix_positive bmf_fl bmf_fr bmf_bias bmf_vl bmf_vr).
 - vm_compute;discriminate.
 - vm_compute;discriminate.
 - intros;apply Z.le_ge;apply bmf_fl_bound.
 - intros;apply Z.le_ge;apply bmf_fr_bound.
 - apply bmf_bias_bound;exact H.
Qed.
Definition bmf_mirror(c:cconf):cconf:=let '(q,(L,h,R)):=c in(q,(R,h,L)).
Definition bmf_integer(c:cconf):Z:=bsr_potential bmf_fl bmf_fr bmf_bias(bmf_mirror c).
Definition bmf_rank(c:cconf):nat:=Z.to_nat(bmf_integer c).
Lemma bmf_integer_nonneg:forall c,cinstr c<>(StB,S1)->0<=bmf_integer c.
Proof. intros[q[[L h]R]] H;apply bmf_positive;exact H. Qed.
Section Machine.
Variable tm:TM.
Hypothesis Htm:forall q h,tm q h=bm_tm q h.
Lemma bmf_step:forall c d,cstep tm c=Some d->
 cinstr c<>(StB,S1)->cinstr d<>(StB,S1)->
 (snd(snd c)<>[]\/bmr_delta(fst c)(snd(fst(snd c)))= -1)->
 bmf_integer d<bmf_integer c.
Proof.
 intros[q[[L h]R]] d HS HC HD HB.
 unfold cstep in HS;rewrite Htm in HS.
 destruct q,h;try(exfalso;apply HC;reflexivity);
 cbn[bm_tm]in HS;injection HS as <-;
 unfold bmf_integer,bmf_mirror;cbn[ctape_move t_next t_dir t_write];
 cbn[fst snd bmr_delta]in HB.
 - apply(bsr_potential_step bmf_fl bmf_fr bmf_bias eq_refl StA R S0 L(mkTrans S0 DL StB)).
   + apply bmf_delta_negative;[reflexivity|exact HC|exact HD].
   + intros _;destruct HB as[H|H];[exact H|discriminate].
 - apply(bsr_potential_step bmf_fl bmf_fr bmf_bias eq_refl StA R S1 L(mkTrans S1 DR StD)).
   + apply bmf_delta_negative;[reflexivity|exact HC|exact HD].
   + discriminate.
 - apply(bsr_potential_step bmf_fl bmf_fr bmf_bias eq_refl StB R S0 L(mkTrans S1 DL StC)).
   + apply bmf_delta_negative;[reflexivity|exact HC|exact HD].
   + intros _;destruct HB as[H|H];[exact H|discriminate].
 - apply(bsr_potential_step bmf_fl bmf_fr bmf_bias eq_refl StC R S0 L(mkTrans S1 DR StA)).
   + apply bmf_delta_negative;[reflexivity|exact HC|exact HD].
   + discriminate.
 - apply(bsr_potential_step bmf_fl bmf_fr bmf_bias eq_refl StC R S1 L(mkTrans S1 DL StA)).
   + apply bmf_delta_negative;[reflexivity|exact HC|exact HD].
   + intros _;destruct HB as[H|H];[exact H|discriminate].
 - apply(bsr_potential_step bmf_fl bmf_fr bmf_bias eq_refl StD R S0 L(mkTrans S1 DL StA)).
   + apply bmf_delta_negative;[reflexivity|exact HC|exact HD].
   + intros _;destruct HB as[H|H];[exact H|discriminate].
 - apply(bsr_potential_step bmf_fl bmf_fr bmf_bias eq_refl StD R S1 L(mkTrans S0 DR StD)).
   + apply bmf_delta_negative;[reflexivity|exact HC|exact HD].
   + discriminate.
Qed.
Theorem bmf_fires_after:forall(Inv:cconf->Prop)(target:Instr),
 (forall c d,Inv c->cinstr c<>(StB,S1)->
   (cinstr c<>(StB,S0)\/snd(snd c)<>[])->cstep tm c=Some d->Inv d)->
 (forall c,Inv c->cinstr c=(StB,S1)->Fires tm c target)->
 (forall q L h,Inv(q,(L,h,[]))->(q,h)<>(StB,S1)->bmr_delta q h=1->
   Fires tm(q,(L,h,[]))target)->
 forall c,Inv c->Fires tm c target.
Proof.
 intros Inv target Hclosed Htarget Hboundary.
 refine(well_founded_induction_type(well_founded_ltof cconf bmf_rank)
  (fun c=>Inv c->Fires tm c target) _).
 intros[q[[L h]R]] IH HI.
 destruct(instr_eqb(q,h)(StB,S1))eqn:E.
 - apply instr_eqb_spec in E;apply Htarget;assumption.
 - assert(HN:(q,h)<>(StB,S1)).
   { intro F;rewrite F,fw_instr_refl in E;discriminate. }
   assert(Cases:(R=[]/\bmr_delta q h=1)\/(R<>[]\/bmr_delta q h= -1)).
   { destruct R as[|r R];[destruct q,h;cbn[bmr_delta];intuition congruence|right;left;discriminate]. }
   destruct Cases as[[-> HP]|HB];[apply Hboundary;assumption|].
   assert(Next:exists d,cstep tm(q,(L,h,R))=Some d).
   { unfold cstep;rewrite Htm;destruct q,h;eexists;reflexivity. }
   destruct Next as[d HS].
   assert(HB':cinstr(q,(L,h,R))<>(StB,S0)\/snd(snd(q,(L,h,R)))<>[]).
   { destruct HB as[H|H];[right;exact H|left;destruct q,h;try discriminate]. }
   assert(HID:Inv d)by(eapply Hclosed;eauto).
   destruct(instr_eqb(cinstr d)(StB,S1))eqn:F.
   + apply instr_eqb_spec in F. eapply(fire_back tm _ d).
     * eapply(r0_run _ 1);[rewrite csteps_1;exact HS|apply reach0_refl].
     * apply Htarget;assumption.
   + assert(HD:cinstr d<>(StB,S1))by(intro H;rewrite H,fw_instr_refl in F;discriminate).
     eapply(fire_back tm _ d).
     * eapply(r0_run _ 1);[rewrite csteps_1;exact HS|apply reach0_refl].
     * apply IH;[|exact HID]. unfold ltof,bmf_rank.
       apply Z2Nat.inj_lt;try(apply bmf_integer_nonneg;assumption).
       eapply bmf_step;eassumption.
Qed.
Theorem bmf_fires:forall(Inv:cconf->Prop),
 (forall c d,Inv c->cinstr c<>(StB,S1)->
   (cinstr c<>(StB,S0)\/snd(snd c)<>[])->cstep tm c=Some d->Inv d)->
 (forall q L h,Inv(q,(L,h,[]))->(q,h)<>(StB,S1)->bmr_delta q h=1->
   Fires tm(q,(L,h,[]))(StB,S1))->
 forall c,Inv c->Fires tm c(StB,S1).
Proof.
 intros Inv Hclosed Hboundary.
 apply(bmf_fires_after Inv(StB,S1));try assumption.
 intros c _ HC;apply fires_here;exact HC.
Qed.

End Machine.
