(** Preserve a right marker in both states. This retains evidence across A
    episodes where the marker is beyond the finite history window. *)
From Coq Require Import List Arith Lia Bool Wf_nat NArith.
From BBB24 Require Import Statement Spec CTape PosEnc Closure HistCensus HistRankSearch
 OneStateReach OneStateConditional MarkerState MarkerPotential TotalCompletion.
From BBB24.Checkers Require Import NGram NGramHist.
From BBB24Burn4EntryMarker Require Import EntryMarker.
From BBB24Burn9ContextMarker Require Import ContextMarker.
From BBB24Burn10MarkerHistory Require Import PartialContextMarker.
Import ListNotations.

Definition gm_inv (mark:Sym->bool)(cc:cconf) :=
 let '(_,(_,h,r)):=cc in em_has mark(h::r).
Definition gm_initial (mark:Sym->bool)(cc:cconf) :=
 let '(_,(_,h,r)):=cc in existsb mark(h::r).
Definition gm_edge mark a a' :=
 cm_known mark a' || negb(mark(cm_head a)).
Definition gm_edges tm k n ls rs mark Sl :=
 forallb(fun a=>match hng_succs tm k n ls rs a with
 |None=>false |Some xs=>forallb(gm_edge mark a)xs end)Sl.

Lemma gm_initial_sound : forall mark cc,
 gm_initial mark cc=true -> gm_inv mark cc.
Proof.
 intros mark[q[[l h]r]]H;apply existsb_exists in H as(x&Hin&Hm).
 exists x;auto.
Qed.
Lemma gm_pad_inv : forall mark n cc,
 gm_inv mark cc -> gm_inv mark(mp_pad n cc).
Proof. intros mark n[q[[l h]r]]H;exact H. Qed.
Lemma gm_unmarked_step : forall tm mark cc cc',
 gm_inv mark cc -> mark(let '(_,(_,h,_)):=cc in h)=false ->
 cstep tm cc=Some cc' -> gm_inv mark cc'.
Proof.
 intros tm mark[q[[l h]r]]cc' Hi Hh E.
 cbn[cstep]in E;destruct(tm q h)as[tr|]eqn:Et;[|discriminate].
 injection E as <-.
 change(em_has mark(h::r))in Hi;apply em_has_split in Hi as[Hm|Ht];[congruence|].
 destruct(t_dir tr);unfold gm_inv;cbn[ctape_move].
 - apply em_has_left;exact Ht.
 - apply em_has_right;exact Ht.
Qed.

Section Graph.
Variables (tm:TM)(k n:nat)(ls rs:hgset)(Sl:list hcconf)(mark:Sym->bool).
Hypothesis Hn:1<=n.
Hypothesis Hz:mark S0=false.
Hypothesis Hclosed:closed_b hcconf hctx_enc(hng_succs tm k n ls rs)Sl=true.
Hypothesis Hedges:gm_edges tm k n ls rs mark Sl=true.

Lemma gm_preserve_step : forall a cc cc',
 In a Sl -> hcovers n ls rs a(lift cc) -> gm_inv mark cc ->
 cstep tm cc=Some cc' ->
 exists a',In a' Sl /\ hcovers n ls rs a'(lift cc') /\ gm_inv mark cc'.
Proof.
 intros a cc cc' Hin Hcov Hi E.
 assert(Hsucc:forall a c,hcovers n ls rs a c ->
  match hng_succs tm k n ls rs a with
  |Some xs=>match step tm c with
   |Some c'=>exists a',In a' xs /\ hcovers n ls rs a' c'|None=>False end
  |None=>True end).
 {intros;apply hng_succs_sound;assumption. }
 destruct(closed_step tm hcconf hctx_enc(hng_succs tm k n ls rs)
  (hcovers n ls rs)hctx_enc_inj Hsucc Sl a(lift cc)Hclosed Hin Hcov)
  as(c'&xs&a'&Es&Ex&Hix&Hin'&Hcov').
 pose proof(cstep_lift tm cc cc' E)as El;rewrite El in Es;injection Es as <-.
 exists a';split;[exact Hin'|];split;[exact Hcov'|].
 assert(He:gm_edge mark a a'=true).
 {unfold gm_edges in Hedges.
  apply forallb_forall with(x:=a)in Hedges;[|exact Hin].
  rewrite Ex in Hedges;apply forallb_forall with(x:=a')in Hedges;assumption. }
 unfold gm_edge in He;apply orb_true_iff in He as[Hk|Hm].
 - exact(cm_known_sound _ _ _ _ _ _ Hz Hcov' Hk).
 - apply negb_true_iff in Hm;rewrite(cm_head_sound _ _ _ _ _ Hcov)in Hm.
   eapply gm_unmarked_step;eauto.
Qed.

Lemma gm_preserve_steps : forall t cc cc' a,
 In a Sl -> hcovers n ls rs a(lift cc) -> gm_inv mark cc ->
 csteps tm t cc=Some cc' ->
 exists a',In a' Sl /\ hcovers n ls rs a'(lift cc') /\ gm_inv mark cc'.
Proof.
 induction t;intros cc cc' a Hin Hc Hi E;cbn[csteps]in E.
 - injection E as <-;eauto.
 - destruct(cstep tm cc)as[c1|]eqn:E1;[|discriminate].
   destruct(gm_preserve_step a cc c1 Hin Hc Hi E1)as(a1&H1&Hc1&Hi1).
   eapply IHt;eauto.
Qed.

Lemma gm_reaches_A : forall weight,
 weight S0=0 -> mp_rank_check tm weight=true ->
 forall cc a,In a Sl -> hcovers n ls rs a(lift cc) -> gm_inv mark cc ->
 mp_capacity weight cc -> ore_reaches tm StA cc.
Proof.
 intros weight Hzero Hr.
 apply(well_founded_induction_type(well_founded_ltof cconf(mp_measure weight))
  (fun cc=>forall a,In a Sl -> hcovers n ls rs a(lift cc) -> gm_inv mark cc ->
   mp_capacity weight cc -> ore_reaches tm StA cc)).
 intros[q[[l h]r]]IH a Hin Hcov Hi Hcap;destruct q.
 - exists 0,(StA,(l,h,r));split;reflexivity.
 - destruct(pm_B_defined tm weight h Hr)as(tr&Et).
   assert(E:cstep tm(StB,(l,h,r))=Some(t_next tr,ctape_move(t_dir tr)(t_write tr)(l,h,r))).
   {cbn[cstep];rewrite Et;reflexivity. }
   destruct(t_next tr)eqn:En.
   + eapply ore_reaches_step;[exact E|];exists 0;eexists;split;reflexivity.
   + destruct(gm_preserve_step _ _ _ Hin Hcov Hi E)as(a'&Hin'&Hcov'&Hi').
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

Definition gm_check tm mask w1 w2 w3 k n t fuel rounds :=
 let mark:=ms_mark mask in let weight:=mp_weights w1 w2 w3 in
 negb(mark S0) && (mp_rank_check tm weight &&
 (ore_auto_goal(orc_fill_goal tm StB)StB && ((1<=?n) &&
 match hcsteps tm k t hcconf0 with
 |None=>false
 |Some cc=>let '(_, (l,_,r)):=cc in
  let a0:=hng_start n cc in
  let '(ls,rs):=hn_grow tm k n a0 fuel rounds(hseed_side n l)(hseed_side n r)in
  let Sl:=hn_explore tm k n ls rs fuel [] PositiveSet.empty[a0]in
  gm_initial mark(hproj cc) && (hseed_ok n ls rs cc &&
  (closed_b hcconf hctx_enc(hng_succs tm k n ls rs)Sl &&
  (mem hcconf hctx_enc a0 Sl && gm_edges tm k n ls rs mark Sl)))
 end))).

Theorem gm_check_sound : forall tm mask w1 w2 w3 k n t fuel rounds,
 gm_check tm mask w1 w2 w3 k n t fuel rounds=true -> NonHalt tm /\ QHBound 0 tm.
Proof.
 intros tm mask w1 w2 w3 k n t fuel rounds H;unfold gm_check in H;cbv zeta in H.
 repeat rewrite andb_true_iff in H.
 destruct H as[Hz[Hr[HB[Hn H]]]].
 apply negb_true_iff in Hz;apply Nat.leb_le in Hn.
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
 apply gm_initial_sound in Hi.
 assert(Eprefix:stepn tm t InitES=Some(lift cc0)).
 {rewrite <-lift_c0;eapply csteps_lift;rewrite <-hproj_hcconf0;eapply hcsteps_proj;exact Et. }
 assert(Hsucc:forall a c,hcovers n ls rs a c ->
  match hng_succs tm k n ls rs a with
  |Some xs=>match step tm c with
   |Some c'=>exists a',In a' xs /\ hcovers n ls rs a' c'|None=>False end
  |None=>True end).
 {intros;apply hng_succs_sound;assumption. }
 assert(Hinv:forall N,exists cc a,csteps tm N cc0=Some cc /\ In a Sl /\ hcovers n ls rs a(lift cc)).
 {intro N;eapply closure_invariant_c;[exact hctx_enc_inj|exact Hsucc|exact Hclosed|exact Hin|exact Hcov]. }
 assert(Hnh:NonHalt tm).
 {intros j Hj;destruct(le_lt_dec t j).
  - destruct(Hinv(j-t))as(cc&a&EN&_).
    replace j with(t+(j-t))in Hj by lia;rewrite stepn_add,Eprefix in Hj.
    rewrite(csteps_lift tm(j-t)cc0 cc EN)in Hj;discriminate.
  - destruct(stepn_prefix tm j t InitES(lift cc0)ltac:(lia)Eprefix)as(c&E&_);congruence. }
 assert(HAr:forall N,exists j,N<=j /\ VisitsAt tm StA j).
 {intro N;destruct(Hinv N)as(cc&aN&EN&_).
  destruct(gm_preserve_steps tm k n ls rs Sl(ms_mark mask)Hn Hz Hclosed Hedges
    N cc0 cc a0 Hin Hcov Hi EN)as(a&Ha&Hca&Hia).
  set(weight:=mp_weights w1 w2 w3).
  assert(Hw:weight S0=0)by reflexivity.
  set(padded:=mp_pad(S(mp_weight weight cc))cc).
  assert(Hcp:hcovers n ls rs a(lift padded)).
  {unfold padded;rewrite mp_pad_lift;exact Hca. }
  assert(Hip:gm_inv(ms_mark mask)padded)by(apply gm_pad_inv;exact Hia).
  assert(Hcapacity:mp_capacity weight padded)by(apply mp_padded_capacity;exact Hw).
  destruct(gm_reaches_A tm k n ls rs Sl(ms_mark mask)Hn Hz Hclosed Hedges
    weight Hw Hr padded a Ha Hcp Hip Hcapacity)as(j&cc'&Ej&Hstate).
  exists(t+N+j);split;[lia|];exists(lift cc');split;[|exact Hstate].
  rewrite !stepn_add,Eprefix.
  rewrite(csteps_lift tm N cc0 cc EN).
  pose proof(csteps_lift tm j padded cc' Ej)as Htail.
  unfold padded in Htail;rewrite mp_pad_lift in Htail;exact Htail. }
 pose proof(orc_goal_recurs tm StB Hnh HB)as HBr.
 split;[exact Hnh|].
 intros state s[_ Hquiet];destruct state.
 - destruct(HAr(S s))as(j&Hj&Hv);exfalso;apply(Hquiet j);[lia|exact Hv].
 - destruct(HBr(S s))as(j&Hj&Hv);exfalso;apply(Hquiet j);[lia|exact Hv].
Qed.
Print Assumptions gm_check_sound.
