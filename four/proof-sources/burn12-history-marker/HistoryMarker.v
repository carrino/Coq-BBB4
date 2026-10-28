(** Historical-cell right markers. The invariant belongs to the actual
    augmented configuration, not an existential witness of [hcovers]. *)
From Coq Require Import List Arith Lia Bool Wf_nat NArith.
From BBB24 Require Import Statement Spec CTape PosEnc Closure HistCensus HistRankSearch
 OneStateReach OneStateConditional MarkerState MarkerPotential.
From BBB24.Checkers Require Import NGram NGramHist.
Import ListNotations.

Definition hm_mark (mask:N)(cell:hsym) := match snd cell with
 |[]=>false
 |(q,s)::_=>N.testbit mask
   ((match q with StA=>0|StB=>4 end)+(match s with S0=>0|S1=>1|S2=>2|S3=>3 end))%N
 end.
Definition hm_has (mark:hsym->bool)(cells:list hsym) :=
 exists cell,In cell cells /\ mark cell=true.
Definition hm_inv (mark:hsym->bool)(cc:hcconf) :=
 let '(q,(_,h,r)):=cc in match q with StA=>True|StB=>hm_has mark(h::r)end.
Definition hm_initial (mark:hsym->bool)(cc:hcconf) :=
 let '(q,(_,h,r)):=cc in match q with StA=>true|StB=>existsb mark(h::r)end.
Definition hm_head (a:hcconf) := let '(_,(_,h,_)):=a in h.
Definition hm_known (mark:hsym->bool)(a:hcconf) :=
 let '(_,(_,h,r)):=a in existsb mark(h::r).
Definition hm_edge mark a a' :=
 st_eqb(fst a')StA || (hm_known mark a' ||
 (st_eqb(fst a)StB && negb(mark(hm_head a)))).
Definition hm_edges tm k n ls rs mark Sl :=
 forallb(fun a=>match hng_succs tm k n ls rs a with
 |None=>false|Some xs=>forallb(hm_edge mark a)xs end)Sl.
Definition hm_pad n(cc:hcconf) := let '(q,(l,h,r)):=cc in
 (q,(l++repeat hblank n,h,r)).

Lemma hm_initial_sound : forall mark cc,
 hm_initial mark cc=true -> hm_inv mark cc.
Proof.
 intros mark[q[[l h]r]]H;destruct q;[exact I|].
 apply existsb_exists in H as(x&Hin&Hm);exists x;auto.
Qed.
Lemma hm_has_split : forall mark h r,
 hm_has mark(h::r) -> mark h=true \/ hm_has mark r.
Proof.
 intros mark h r(x&[Hx|Hin]&Hm).
 - subst x;left;exact Hm.
 - right;exists x;auto.
Qed.
Lemma hm_has_right : forall mark r,
 hm_has mark r -> hm_has mark(hchd r::hctl r).
Proof. intros mark[|h r]H;[destruct H as(x&H&_);contradiction|exact H]. Qed.
Lemma hm_has_left : forall mark l w r,
 hm_has mark r -> hm_has mark(hchd l::w::r).
Proof. intros mark l w r(x&Hin&Hm);exists x;split;[right;right;exact Hin|exact Hm]. Qed.
Lemma hm_has_single : forall mark h,hm_has mark[h] -> mark h=true.
Proof. intros mark h H;apply hm_has_split in H as[H|(x&H&_)];[exact H|contradiction]. Qed.
Lemma hm_nth_marker : forall mark r i,
 mark hblank=false -> mark(hnthb r i)=true -> hm_has mark r.
Proof.
 intros mark r i Hz Hm;unfold hnthb in Hm.
 destruct(lt_dec i(length r))as[Hlt|Hge].
 - exists(nth i r hblank);split;[apply nth_In;exact Hlt|exact Hm].
 - rewrite nth_overflow in Hm;[congruence|lia].
Qed.
Lemma hm_known_sound : forall mark n ls rs a cc,
 mark hblank=false -> hng_covers n ls rs a cc -> hm_known mark a=true ->
 let '(_,(_,h,r)):=cc in hm_has mark(h::r).
Proof.
 intros mark n ls rs[q[[lw s]rw]][qc[[l h]r]]Hz Hcov Hknown.
 destruct Hcov as(Hq&Hh&Hl&Hr&HL&HR).
 cbn[hm_known]in Hknown;rewrite <-Hh,Hr in Hknown.
 apply existsb_exists in Hknown as(x&[Hx|Hin]&Hm).
 - subst x;exists h;split;[left;reflexivity|exact Hm].
 - unfold hwin in Hin;apply in_map_iff in Hin as(i&Hi&_);subst x.
   destruct(hm_nth_marker mark r i Hz Hm)as(y&Hy&Hmy).
   exists y;split;[right;exact Hy|exact Hmy].
Qed.
Lemma hm_head_sound : forall n ls rs a cc,
 hng_covers n ls rs a cc -> hm_head a=(let '(_,(_,h,_)):=cc in h).
Proof.
 intros n ls rs[q[[lw s]rw]][qc[[l h]r]](_&H&_).
 cbn[hm_head];symmetry;exact H.
Qed.
Lemma hm_unmarked_step : forall tm k mark cc cc',
 hm_inv mark cc -> fst cc=StB -> mark(hm_head cc)=false ->
 hcstep tm k cc=Some cc' -> hm_inv mark cc'.
Proof.
 intros tm k mark[q[[l h]r]]cc' Hi Hq Hh E;cbn in Hq;subst q;cbn[hm_head]in Hh.
 cbn[hcstep]in E;destruct(tm StB(hbit h))as[tr|]eqn:Et;[|discriminate].
 injection E as <-;destruct(t_next tr);[destruct(t_dir tr);exact I|].
 change(hm_has mark(h::r))in Hi;apply hm_has_split in Hi as[Hm|Ht];[congruence|].
 destruct(t_dir tr);unfold hm_inv;cbn[hctape_move].
 - apply hm_has_left;exact Ht.
 - apply hm_has_right;exact Ht.
Qed.

Lemma hm_nth_repeat : forall i n,nth i(repeat hblank n)hblank=hblank.
Proof. induction i;destruct n;cbn;auto. Qed.
Lemma hm_nth_pad : forall l i n,hnthb(l++repeat hblank n)i=hnthb l i.
Proof.
 induction l as[|a l IH];intros i n.
 - unfold hnthb;cbn[app];rewrite hm_nth_repeat;destruct i;reflexivity.
 - destruct i;cbn[hnthb app nth];[reflexivity|apply IH].
Qed.
Lemma hm_win_pad : forall l padding d n,
 hwin(hlift_side(l++repeat hblank padding))d n=hwin(hlift_side l)d n.
Proof.
 intros;unfold hwin;apply map_ext;intro i;unfold hlift_side;apply hm_nth_pad.
Qed.
Lemma hm_pad_covers : forall n ls rs a cc padding,
 hng_covers n ls rs a cc -> hng_covers n ls rs a(hm_pad padding cc).
Proof.
 intros n ls rs[q[[lw s]rw]][qc[[l h]r]]padding H.
 destruct H as(Hq&Hh&Hl&Hr&HL&HR);unfold hm_pad,hng_covers;cbn.
 repeat split;try assumption.
 - rewrite hm_win_pad;exact Hl.
 - intros d Hd;rewrite hm_win_pad;apply HL;exact Hd.
Qed.
Lemma hm_pad_inv : forall mark n cc,hm_inv mark cc -> hm_inv mark(hm_pad n cc).
Proof. intros mark n[q[[l h]r]]H;exact H. Qed.
Lemma hm_pad_projection : forall n cc,hproj(hm_pad n cc)=mp_pad n(hproj cc).
Proof.
 intros n[q[[l h]r]];unfold hm_pad,hproj,mp_pad,hproj_side;cbn.
 rewrite map_app,map_repeat;reflexivity.
Qed.
Lemma hm_B_defined : forall tm weight h,
 mp_rank_check tm weight=true -> exists tr,tm StB h=Some tr.
Proof.
 intros tm weight h H;unfold mp_rank_check in H;apply andb_true_iff in H as[_ H].
 apply forallb_forall with(x:=h)in H;[|apply ore_symbols_complete].
 unfold mp_cell in H;destruct(tm StB h)as[tr|]eqn:E;[eauto|discriminate].
Qed.

Section Graph.
Variables (tm:TM)(k n:nat)(ls rs:hgset)(Sl:list hcconf)(mark:hsym->bool).
Hypothesis Hn:1<=n.
Hypothesis Hz:mark hblank=false.
Hypothesis Hclosed:closed_b hcconf hctx_enc(hng_succs tm k n ls rs)Sl=true.
Hypothesis Hedges:hm_edges tm k n ls rs mark Sl=true.

Lemma hm_closed_step : forall a cc,
 In a Sl -> hng_covers n ls rs a cc ->
 exists cc' xs a',hcstep tm k cc=Some cc' /\ hng_succs tm k n ls rs a=Some xs /\
 In a' xs /\ In a' Sl /\ hng_covers n ls rs a' cc'.
Proof.
 intros a cc Hin Hcov.
 assert(Hnode:node_ok hcconf hctx_enc(hng_succs tm k n ls rs)(apool hcconf hctx_enc Sl)a=true).
 {unfold closed_b in Hclosed;apply forallb_forall with(x:=a)in Hclosed;assumption. }
 unfold node_ok in Hnode;destruct(hng_succs tm k n ls rs a)as[xs|]eqn:Ex;[|discriminate].
 assert(Hstep:exists cc',hcstep tm k cc=Some cc').
 {destruct a as[q[[lw s]rw]],cc as[qc[[l h]r]].
  destruct Hcov as(Hq&Hh&_);cbn in Hq,Hh;subst qc s.
  cbn[hng_succs]in Ex;cbn[hcstep];destruct(tm q(hbit h))as[tr|];[eauto|discriminate]. }
 destruct Hstep as(cc'&E).
 destruct(hng_succs_sound_some tm k n ls rs a cc xs cc' Hn Hcov Ex E)as(a'&Ha&Hc').
 exists cc',xs,a';repeat split;try assumption.
 apply mem_In with(a_enc:=hctx_enc);[exact hctx_enc_inj|].
 unfold mem,apool;apply forallb_forall with(x:=a')in Hnode;assumption.
Qed.

Lemma hm_preserve_step : forall a cc cc',
 In a Sl -> hng_covers n ls rs a cc -> hm_inv mark cc ->
 hcstep tm k cc=Some cc' ->
 exists a',In a' Sl /\ hng_covers n ls rs a' cc' /\ hm_inv mark cc'.
Proof.
 intros a cc cc' Hin Hcov Hi E.
 destruct(hm_closed_step a cc Hin Hcov)as(c'&xs&a'&Es&Ex&Hix&Hin'&Hcov').
 rewrite E in Es;injection Es as <-.
 exists a';split;[exact Hin'|];split;[exact Hcov'|].
 assert(He:hm_edge mark a a'=true).
 {unfold hm_edges in Hedges;apply forallb_forall with(x:=a)in Hedges;[|exact Hin].
  rewrite Ex in Hedges;apply forallb_forall with(x:=a')in Hedges;assumption. }
 unfold hm_edge in He;apply orb_true_iff in He as[HA|He].
 - apply st_eqb_spec in HA;pose proof(hng_covers_state _ _ _ _ _ Hcov')as Hs.
   unfold ha_state in Hs;rewrite HA in Hs.
   destruct cc' as[q[[l h]r]];cbn in Hs;subst q;exact I.
 - apply orb_true_iff in He as[Hk|He].
   + pose proof(hm_known_sound _ _ _ _ _ _ Hz Hcov' Hk)as Hhas.
     destruct cc' as[q[[l h]r]];destruct q;[exact I|exact Hhas].
   + apply andb_true_iff in He as[Hq Hm];apply st_eqb_spec in Hq;apply negb_true_iff in Hm.
     rewrite(hm_head_sound _ _ _ _ _ Hcov)in Hm.
     pose proof(hng_covers_state _ _ _ _ _ Hcov)as Hs;unfold ha_state in Hs;rewrite Hq in Hs.
     eapply hm_unmarked_step;eauto;congruence.
Qed.

Lemma hm_run : forall t cc a,
 In a Sl -> hng_covers n ls rs a cc -> hm_inv mark cc ->
 exists cc' a',hcsteps tm k t cc=Some cc' /\ In a' Sl /\
 hng_covers n ls rs a' cc' /\ hm_inv mark cc'.
Proof.
 induction t;intros cc a Hin Hcov Hi.
 - exists cc,a;repeat split;try assumption;reflexivity.
 - destruct(hm_closed_step a cc Hin Hcov)as(c1&xs&a1&E&_).
   destruct(hm_preserve_step a cc c1 Hin Hcov Hi E)as(b&Hb&Hcb&Hib).
   destruct(IHt c1 b Hb Hcb Hib)as(c2&b2&E2&Hb2&Hcb2&Hib2).
   exists c2,b2;repeat split;try assumption;cbn[hcsteps];rewrite E;exact E2.
Qed.

Lemma hm_reaches_A : forall weight,
 weight S0=0 -> mp_rank_check tm weight=true ->
 forall cc a,In a Sl -> hng_covers n ls rs a cc -> hm_inv mark cc ->
 mp_capacity weight(hproj cc) -> ore_reaches tm StA(hproj cc).
Proof.
 intros weight Hzero Hr.
 apply(well_founded_induction_type(well_founded_ltof hcconf(fun cc=>mp_measure weight(hproj cc)))
  (fun cc=>forall a,In a Sl -> hng_covers n ls rs a cc -> hm_inv mark cc ->
   mp_capacity weight(hproj cc) -> ore_reaches tm StA(hproj cc))).
 intros[q[[l h]r]]IH a Hin Hcov Hi Hcap;destruct q.
 - exists 0,(hproj(StA,(l,h,r)));split;reflexivity.
 - destruct(hm_B_defined tm weight(hbit h)Hr)as(tr&Et).
   set(w:=(t_write tr,firstn k((StB,hbit h)::snd h)):hsym).
   assert(E:hcstep tm k(StB,(l,h,r))=Some(t_next tr,hctape_move(t_dir tr)w(l,h,r))).
   {cbn[hcstep];rewrite Et;reflexivity. }
   pose proof(hcstep_proj_some tm k _ _ E)as Ep.
   destruct(t_next tr)eqn:En.
   + eapply ore_reaches_step;[exact Ep|];exists 0;eexists;split;
     [reflexivity|rewrite hproj_state;reflexivity].
   + destruct(hm_preserve_step _ _ _ Hin Hcov Hi E)as(a'&Hin'&Hcov'&Hi').
     pose proof(mp_checked_delta tm weight(hbit h)tr Hr Et En)as Hd.
     pose proof(mp_capacity_move weight StB StB(hproj_side l)(hbit h)(hproj_side r)
       (t_dir tr)(t_write tr)Hzero Hcap Hd)as Hcap'.
     destruct(t_dir tr)eqn:Ed;cbn[hctape_move]in E,Ep,Hcov',Hi'.
     * destruct l as[|b l];cbn[hchd hctl]in E,Ep,Hcov',Hi'.
       -- unfold mp_capacity,mp_left_length,hproj,hproj_side in Hcap;cbn in Hcap;lia.
       -- eapply ore_reaches_step;[exact Ep|];eapply IH with(a:=a');try assumption.
          ++ unfold ltof,mp_measure,ore_mirror_cc;cbn[hproj hproj_side hbit w].
             apply ore_right_drop;change(weight(t_write tr)<weight(hbit h));lia.
     * destruct r as[|b r];cbn[hchd hctl]in E,Ep,Hcov',Hi'.
       -- change(hm_has mark[hblank])in Hi'.
          pose proof(hm_has_single mark hblank Hi');congruence.
       -- eapply ore_reaches_step;[exact Ep|];eapply IH with(a:=a');try assumption.
          ++ unfold ltof,mp_measure,ore_mirror_cc;cbn[hproj hproj_side hbit w].
             apply ore_left_drop;eapply mp_checked_bound;exact Hr.
Qed.
End Graph.

Definition hm_check tm mask w1 w2 w3 k n t fuel rounds :=
 let mark:=hm_mark mask in let weight:=mp_weights w1 w2 w3 in
 negb(mark hblank) && (mp_rank_check tm weight &&
 (ore_auto_goal(orc_fill_goal tm StB)StB && ((1<=?n) &&
 match hcsteps tm k t hcconf0 with
 |None=>false
 |Some cc=>let '(_, (l,_,r)):=cc in
  let a0:=hng_start n cc in
  let '(ls,rs):=hn_grow tm k n a0 fuel rounds(hseed_side n l)(hseed_side n r)in
  let Sl:=hn_explore tm k n ls rs fuel [] PositiveSet.empty[a0]in
  hm_initial mark cc && (hseed_ok n ls rs cc &&
  (closed_b hcconf hctx_enc(hng_succs tm k n ls rs)Sl &&
  (mem hcconf hctx_enc a0 Sl && hm_edges tm k n ls rs mark Sl)))
 end))).

Theorem hm_check_sound : forall tm mask w1 w2 w3 k n t fuel rounds,
 hm_check tm mask w1 w2 w3 k n t fuel rounds=true -> NonHalt tm /\ QHBound 0 tm.
Proof.
 intros tm mask w1 w2 w3 k n t fuel rounds H;unfold hm_check in H;cbv zeta in H.
 repeat rewrite andb_true_iff in H;destruct H as[Hz[Hr[HB[Hn H]]]].
 apply negb_true_iff in Hz;apply Nat.leb_le in Hn.
 destruct(hcsteps tm k t hcconf0)as[cc0|]eqn:Et;[|discriminate].
 destruct cc0 as[q[[l h]r]].
 match type of H with(let '(_,_) := ?G in _)=true=>destruct G as[ls rs]end.
 cbv beta iota zeta in H;repeat rewrite andb_true_iff in H.
 destruct H as[Hi[Hseed[Hclosed[Hmem Hedges]]]].
 set(cc0:=(q,(l,h,r)))in *;set(a0:=hng_start n cc0)in *.
 set(Sl:=hn_explore tm k n ls rs fuel [] PositiveSet.empty[a0])in *.
 assert(Hin:In a0 Sl)by(eapply mem_In;[exact hctx_enc_inj|exact Hmem]).
 assert(Hcov:hng_covers n ls rs a0 cc0)by(apply hng_start_covers;exact Hseed).
 apply hm_initial_sound in Hi.
 assert(Eprefix:stepn tm t InitES=Some(lift(hproj cc0))).
 {rewrite <-lift_c0;eapply csteps_lift;rewrite <-hproj_hcconf0;eapply hcsteps_proj;exact Et. }
 assert(Hinv:forall N,exists cc a,hcsteps tm k N cc0=Some cc /\ In a Sl /\
   hng_covers n ls rs a cc /\ hm_inv(hm_mark mask)cc).
 {intro N;eapply hm_run;eauto. }
 assert(Hnh:NonHalt tm).
 {intros j Hj;destruct(le_lt_dec t j).
  - destruct(Hinv(j-t))as(cc&a&EN&_).
    replace j with(t+(j-t))in Hj by lia;rewrite stepn_add,Eprefix in Hj.
    rewrite(csteps_lift tm(j-t)(hproj cc0)(hproj cc)(hcsteps_proj tm k(j-t)cc0 cc EN))in Hj;discriminate.
  - destruct(stepn_prefix tm j t InitES(lift(hproj cc0))ltac:(lia)Eprefix)as(c&E&_);congruence. }
 assert(HAr:forall N,exists j,N<=j /\ VisitsAt tm StA j).
 {intro N;destruct(Hinv N)as(cc&a&EN&Ha&Hca&Hia).
  set(weight:=mp_weights w1 w2 w3);assert(Hw:weight S0=0)by reflexivity.
  set(padded:=hm_pad(S(mp_weight weight(hproj cc)))cc).
  assert(Hcp:hng_covers n ls rs a padded)by(apply hm_pad_covers;exact Hca).
  assert(Hip:hm_inv(hm_mark mask)padded)by(apply hm_pad_inv;exact Hia).
  assert(Hcapacity:mp_capacity weight(hproj padded)).
  {unfold padded;rewrite hm_pad_projection;apply mp_padded_capacity;exact Hw. }
  destruct(hm_reaches_A tm k n ls rs Sl(hm_mark mask)Hn Hz Hclosed Hedges
    weight Hw Hr padded a Ha Hcp Hip Hcapacity)as(j&cc'&Ej&Hstate).
  exists(t+N+j);split;[lia|];exists(lift cc');split;[|exact Hstate].
  rewrite !stepn_add,Eprefix.
  rewrite(csteps_lift tm N(hproj cc0)(hproj cc)(hcsteps_proj tm k N cc0 cc EN)).
  pose proof(csteps_lift tm j(hproj padded)cc' Ej)as Htail.
  unfold padded in Htail;rewrite hm_pad_projection,mp_pad_lift in Htail;exact Htail. }
 pose proof(orc_goal_recurs tm StB Hnh HB)as HBr.
 split;[exact Hnh|].
 intros state s[_ Hquiet];destruct state.
 - destruct(HAr(S s))as(j&Hj&Hv);exfalso;apply(Hquiet j);[lia|exact Hv].
 - destruct(HBr(S s))as(j&Hj&Hv);exfalso;apply(Hquiet j);[lia|exact Hv].
Qed.
Print Assumptions hm_check_sound.
