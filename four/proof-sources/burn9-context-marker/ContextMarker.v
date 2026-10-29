(** History contexts justify marker creation at entries into B. A marker may
    also survive beyond the visible window; it is required only in state B. *)
From Coq Require Import List Arith Lia Bool Wf_nat NArith.
From BBB24 Require Import Statement Spec CTape PosEnc Closure HistCensus HistRankSearch
  OneStateReach MarkerState MarkerPotential TotalCompletion.
From BBB24.Checkers Require Import NGram NGramHist.
From BBB24Burn4EntryMarker Require Import EntryMarker.
Import ListNotations.

Definition cm_head (a:hcconf) := let '(_,(_,h,_)):=a in hbit h.
Definition cm_known (mark:Sym->bool)(a:hcconf) :=
 let '(_,(_,h,r)):=hproj a in existsb mark(h::r).
Definition cm_edge mark a a' :=
 st_eqb(fst a')StA || (cm_known mark a' ||
 (st_eqb(fst a)StB && negb(mark(cm_head a)))).
Definition cm_edges tm k n ls rs mark Sl :=
 forallb(fun a=>match hng_succs tm k n ls rs a with
 |None=>false |Some xs=>forallb(cm_edge mark a)xs end)Sl.
Definition cm_initial mark (cc:cconf) :=
 let '(q,(_,h,r)):=cc in match q with StA=>true|StB=>existsb mark(h::r)end.
Definition cm_total (tm:TM) := forallb(fun q=>forallb(fun h=>
 match tm q h with None=>false|Some _=>true end)ore_symbols)all_St.

Lemma cm_total_sound : forall tm,cm_total tm=true -> Total tm.
Proof.
 intros tm H q h;unfold cm_total in H.
 apply forallb_forall with(x:=q)in H;[|apply all_St_complete].
 apply forallb_forall with(x:=h)in H;[|apply ore_symbols_complete].
 destruct(tm q h)as[tr|]eqn:E;[eauto|discriminate].
Qed.
Lemma cm_initial_sound : forall mark cc,
 cm_initial mark cc=true -> em_inv mark cc.
Proof.
 intros mark[q[[l h]r]]H;destruct q;[exact I|].
 apply existsb_exists in H as(x&Hin&Hm). exists x;auto.
Qed.
Lemma cm_nth_marker : forall mark r i,
 mark S0=false -> mark(nthb r i)=true -> em_has mark r.
Proof.
 intros mark r i Hz Hm;unfold nthb in Hm.
 destruct(lt_dec i(length r))as[Hlt|Hge].
 - exists(nth i r S0);split;[apply nth_In;exact Hlt|exact Hm].
 - rewrite nth_overflow in Hm;[congruence|lia].
Qed.
Lemma cm_known_start : forall mark n cc,
 mark S0=false -> (let '(_,(_,h,r)):=ng_start n cc in existsb mark(h::r))=true ->
 let '(_,(_,h,r)):=cc in em_has mark(h::r).
Proof.
 intros mark n[q[[l h]r]]Hz H;cbn[ng_start]in H.
 apply existsb_exists in H as(x&[Hx|Hin]&Hm).
 - subst x;apply em_has_head;exact Hm.
 - unfold win in Hin;apply in_map_iff in Hin as(i&Hi&_).
   subst x. destruct(cm_nth_marker mark r i Hz Hm)as(y&Hy&Hmy).
   exists y;split;[right;exact Hy|exact Hmy].
Qed.
Lemma cm_projection : forall n ls rs a cc,
 hcovers n ls rs a(lift cc) -> hproj a=ng_start n cc.
Proof. intros n ls rs a cc(hc&E&H);eapply hproj_eq_ngstart;eauto. Qed.
Lemma cm_known_sound : forall mark n ls rs a cc,
 mark S0=false -> hcovers n ls rs a(lift cc) -> cm_known mark a=true ->
 let '(_,(_,h,r)):=cc in em_has mark(h::r).
Proof.
 intros mark n ls rs a cc Hz Hc Hk;unfold cm_known in Hk.
 rewrite(cm_projection _ _ _ _ _ Hc)in Hk;eapply cm_known_start;eauto.
Qed.
Lemma cm_head_sound : forall n ls rs a cc,
 hcovers n ls rs a(lift cc) -> cm_head a=(let '(_,(_,h,_)):=cc in h).
Proof.
 intros n ls rs[q[[l h]r]][q'[[l' h']r']]H.
 pose proof(cm_projection _ _ _ _ _ H)as E.
 cbn[hproj ng_start]in E;cbn[cm_head];congruence.
Qed.
Lemma cm_unmarked_step : forall tm mark cc cc',
 em_inv mark cc -> fst cc=StB ->
 mark(let '(_,(_,h,_)):=cc in h)=false ->
 cstep tm cc=Some cc' -> em_inv mark cc'.
Proof.
 intros tm mark[q[[l h]r]]cc' Hi Hq Hh E;cbn in Hq;subst q.
 cbn[cstep]in E;destruct(tm StB h)as[tr|]eqn:Et;[|discriminate].
 injection E as <-. destruct(t_next tr);[destruct(t_dir tr);exact I|].
 change(em_has mark(h::r))in Hi;apply em_has_split in Hi as[Hm|Ht];[congruence|].
 destruct(t_dir tr);unfold em_inv;cbn[ctape_move].
 - apply em_has_left;exact Ht.
 - apply em_has_right;exact Ht.
Qed.

Section Graph.
Variables (tm:TM)(k n:nat)(ls rs:hgset)(Sl:list hcconf)(mark:Sym->bool).
Hypothesis Hn:1<=n.
Hypothesis Hz:mark S0=false.
Hypothesis Hclosed:closed_b hcconf hctx_enc(hng_succs tm k n ls rs)Sl=true.
Hypothesis Hedges:cm_edges tm k n ls rs mark Sl=true.

Lemma cm_successors_sound : forall a c,hcovers n ls rs a c ->
 match hng_succs tm k n ls rs a with
 |Some xs=>match step tm c with
   |Some c'=>exists a',In a' xs /\ hcovers n ls rs a' c'|None=>False end
 |None=>True end.
Proof. intros;apply hng_succs_sound;assumption. Qed.

Lemma cm_preserve_step : forall a cc cc',
 In a Sl -> hcovers n ls rs a(lift cc) -> em_inv mark cc ->
 cstep tm cc=Some cc' ->
 exists a',In a' Sl /\ hcovers n ls rs a'(lift cc') /\ em_inv mark cc'.
Proof.
 intros a cc cc' Hin Hcov Hi E.
 destruct(closed_step tm hcconf hctx_enc(hng_succs tm k n ls rs)
  (hcovers n ls rs)hctx_enc_inj cm_successors_sound Sl a(lift cc)Hclosed Hin Hcov)
  as(c'&xs&a'&Es&Ex&Hix&Hin'&Hcov').
 pose proof(cstep_lift tm cc cc' E)as El;rewrite El in Es;injection Es as <-.
 exists a';split;[exact Hin'|];split;[exact Hcov'|].
 assert(He:cm_edge mark a a'=true).
 {unfold cm_edges in Hedges.
  apply forallb_forall with(x:=a)in Hedges;[|exact Hin].
  rewrite Ex in Hedges;apply forallb_forall with(x:=a')in Hedges;assumption. }
 unfold cm_edge in He;apply orb_true_iff in He as[HA|He].
 - apply st_eqb_spec in HA.
   pose proof(hcovers_state _ _ _ _ _ Hcov')as Hs.
   unfold ha_state in Hs;rewrite HA,lift_state in Hs.
   destruct cc' as[q[[l h]r]];cbn in Hs;subst q;exact I.
 - apply orb_true_iff in He as[Hk|He].
   + pose proof(cm_known_sound _ _ _ _ _ _ Hz Hcov' Hk)as Hhas.
     destruct cc' as[q[[l h]r]];destruct q;[exact I|exact Hhas].
   + apply andb_true_iff in He as[Hq Hm].
     apply st_eqb_spec in Hq;apply negb_true_iff in Hm.
     rewrite(cm_head_sound _ _ _ _ _ Hcov)in Hm.
     pose proof(hcovers_state _ _ _ _ _ Hcov)as Hs.
     unfold ha_state in Hs;rewrite Hq,lift_state in Hs.
     eapply cm_unmarked_step;eauto;congruence.
Qed.

Lemma cm_preserve_steps : forall t cc cc' a,
 In a Sl -> hcovers n ls rs a(lift cc) -> em_inv mark cc ->
 csteps tm t cc=Some cc' ->
 exists a',In a' Sl /\ hcovers n ls rs a'(lift cc') /\ em_inv mark cc'.
Proof.
 induction t;intros cc cc' a Hin Hc Hi E;cbn[csteps]in E.
 - injection E as <-;eauto.
 - destruct(cstep tm cc)as[c1|]eqn:E1;[|discriminate].
   destruct(cm_preserve_step a cc c1 Hin Hc Hi E1)as(a1&H1&Hc1&Hi1).
   eapply IHt;eauto.
Qed.

Lemma cm_reaches_A : forall weight,
 weight S0=0 -> mp_rank_check tm weight=true -> Total tm ->
 forall cc a,In a Sl -> hcovers n ls rs a(lift cc) -> em_inv mark cc ->
 mp_capacity weight cc -> ore_reaches tm StA cc.
Proof.
 intros weight Hzero Hr Htotal.
 apply(well_founded_induction_type(well_founded_ltof cconf(mp_measure weight))
  (fun cc=>forall a,In a Sl -> hcovers n ls rs a(lift cc) -> em_inv mark cc ->
   mp_capacity weight cc -> ore_reaches tm StA cc)).
 intros[q[[l h]r]]IH a Hin Hcov Hi Hcap;destruct q.
 - exists 0,(StA,(l,h,r));split;reflexivity.
 - destruct(Htotal StB h)as(tr&Et).
   assert(E:cstep tm(StB,(l,h,r))=Some(t_next tr,ctape_move(t_dir tr)(t_write tr)(l,h,r))).
   {cbn[cstep];rewrite Et;reflexivity. }
   destruct(t_next tr)eqn:En.
   + eapply ore_reaches_step;[exact E|];exists 0;eexists;split;reflexivity.
   + destruct(cm_preserve_step _ _ _ Hin Hcov Hi E)as(a'&Hin'&Hcov'&Hi').
     pose proof(mp_checked_delta tm weight h tr Hr Et En)as Hd.
     pose proof(mp_capacity_move weight StB StB l h r(t_dir tr)(t_write tr)Hzero Hcap Hd)as Hcap'.
     destruct(t_dir tr)eqn:Ed;cbn[ctape_move]in E,Hcov',Hi',Hcap'.
     * destruct l as[|b l];cbn[chd ctl]in E,Hcov',Hi',Hcap'.
       -- unfold mp_capacity,mp_left_length in Hcap;cbn in Hcap;lia.
       -- eapply ore_reaches_step;[exact E|];eapply IH with(a:=a');try assumption.
          unfold ltof,mp_measure,ore_mirror_cc;apply ore_right_drop;lia.
     * destruct r as[|b r];cbn[chd ctl]in E,Hcov',Hi',Hcap'.
       -- change(em_has mark[S0])in Hi'.
          pose proof(em_has_single mark S0 Hi');congruence.
       -- eapply ore_reaches_step;[exact E|];eapply IH with(a:=a');try assumption.
          unfold ltof,mp_measure,ore_mirror_cc;apply ore_left_drop.
          eapply mp_checked_bound;exact Hr.
Qed.
End Graph.

Definition cm_check tm mask w1 w2 w3 k n t fuel rounds :=
 let mark:=ms_mark mask in let weight:=mp_weights w1 w2 w3 in
 negb(mark S0) && (cm_total tm && (mp_rank_check tm weight &&
 (ore_auto_goal tm StB && ((1<=?n) &&
 match hcsteps tm k t hcconf0 with
 |None=>false
 |Some cc=>let '(_, (l,_,r)):=cc in
  let a0:=hng_start n cc in
  let '(ls,rs):=hn_grow tm k n a0 fuel rounds(hseed_side n l)(hseed_side n r)in
  let Sl:=hn_explore tm k n ls rs fuel [] PositiveSet.empty[a0]in
  cm_initial mark(hproj cc) && (hseed_ok n ls rs cc &&
  (closed_b hcconf hctx_enc(hng_succs tm k n ls rs)Sl &&
  (mem hcconf hctx_enc a0 Sl && cm_edges tm k n ls rs mark Sl)))
 end)))).

Theorem cm_check_sound : forall tm mask w1 w2 w3 k n t fuel rounds,
 cm_check tm mask w1 w2 w3 k n t fuel rounds=true -> NonHalt tm /\ QHBound 0 tm.
Proof.
 intros tm mask w1 w2 w3 k n t fuel rounds H;unfold cm_check in H;cbv zeta in H.
 repeat rewrite andb_true_iff in H.
 destruct H as[Hz[Ht[Hr[HB[Hn H]]]]].
 apply negb_true_iff in Hz;apply Nat.leb_le in Hn.
 pose proof(cm_total_sound tm Ht)as Htotal.
 destruct(hcsteps tm k t hcconf0)as[[q[[l h]r]]|]eqn:Et;[|discriminate].
 match type of H with(let '(_,_) := ?G in _)=true=>destruct G as[ls rs]end.
 cbv beta iota zeta in H;repeat rewrite andb_true_iff in H.
 destruct H as[Hi[Hseed[Hclosed[Hmem Hedges]]]].
 set(cc0:=hproj(q,(l,h,r)))in *.
 set(a0:=hng_start n(q,(l,h,r)))in *.
 set(Sl:=hn_explore tm k n ls rs fuel [] PositiveSet.empty[a0])in *.
 assert(Hin:In a0 Sl)by(eapply mem_In;[exact hctx_enc_inj|exact Hmem]).
 assert(Hcov:hcovers n ls rs a0(lift cc0)).
 {exists(q,(l,h,r));split;[reflexivity|];apply hng_start_covers;exact Hseed. }
 apply cm_initial_sound in Hi.
 assert(Eprefix:stepn tm t InitES=Some(lift cc0)).
 {rewrite <-lift_c0;eapply csteps_lift;rewrite <-hproj_hcconf0;eapply hcsteps_proj;exact Et. }
 assert(HAr:forall N,exists j,N<=j /\ VisitsAt tm StA j).
 {intro N;destruct(ore_total_csteps tm Htotal N cc0)as(cc&EN).
  destruct(cm_preserve_steps tm k n ls rs Sl(ms_mark mask)Hn Hz Hclosed Hedges
    N cc0 cc a0 Hin Hcov Hi EN)as(a&Ha&Hca&Hia).
  set(weight:=mp_weights w1 w2 w3).
  assert(Hw:weight S0=0)by reflexivity.
  set(padded:=mp_pad(S(mp_weight weight cc))cc).
  assert(Hcp:hcovers n ls rs a(lift padded)).
  {unfold padded;rewrite mp_pad_lift;exact Hca. }
  assert(Hip:em_inv(ms_mark mask)padded)by(apply em_pad_inv;exact Hia).
  assert(Hcapacity:mp_capacity weight padded)by(apply mp_padded_capacity;exact Hw).
  destruct(cm_reaches_A tm k n ls rs Sl(ms_mark mask)Hn Hz Hclosed Hedges
    weight Hw Hr Htotal padded a Ha Hcp Hip Hcapacity)as(j&cc'&Ej&Hstate).
  exists(t+N+j);split;[lia|];exists(lift cc');split;[|exact Hstate].
  rewrite !stepn_add,Eprefix.
  rewrite(csteps_lift tm N cc0 cc EN).
  pose proof(csteps_lift tm j padded cc' Ej)as Htail.
  unfold padded in Htail;rewrite mp_pad_lift in Htail;exact Htail. }
 assert(HBr:forall N,exists j,N<=j /\ VisitsAt tm StB j).
 {apply(ore_reaches_recurs tm StB Htotal);apply ore_auto_goal_sound;exact HB. }
 split;[apply ore_total_nonhalt;exact Htotal|].
 intros state s[_ Hquiet];destruct state.
 - destruct(HAr(S s))as(j&Hj&Hv);exfalso;apply(Hquiet j);[lia|exact Hv].
 - destruct(HBr(S s))as(j&Hj&Hv);exfalso;apply(Hquiet j);[lia|exact Hv].
Qed.
Print Assumptions cm_check_sound.
