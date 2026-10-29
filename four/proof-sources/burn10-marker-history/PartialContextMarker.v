(** Partial-table contextual markers. Closure proves reachable nonhalting;
    the capacity checker supplies B transitions, and conditional one-state
    reachability proves B recurrence without defining unreachable A cells. *)
From Coq Require Import List Arith Lia Bool Wf_nat NArith.
From BBB24 Require Import Statement Spec CTape PosEnc Closure HistCensus HistRankSearch
 OneStateReach OneStateConditional MarkerState MarkerPotential TotalCompletion.
From BBB24.Checkers Require Import NGram NGramHist.
From BBB24Burn4EntryMarker Require Import EntryMarker.
From BBB24Burn9ContextMarker Require Import ContextMarker.
Import ListNotations.

Lemma pm_B_defined : forall tm weight h,
 mp_rank_check tm weight=true -> exists tr,tm StB h=Some tr.
Proof.
 intros tm weight h H;unfold mp_rank_check in H;apply andb_true_iff in H as[_ H].
 apply forallb_forall with(x:=h)in H;[|apply ore_symbols_complete].
 unfold mp_cell in H;destruct(tm StB h)as[tr|]eqn:E;[eauto|discriminate].
Qed.

Section Graph.
Variables (tm:TM)(k n:nat)(ls rs:hgset)(Sl:list hcconf)(mark:Sym->bool).
Hypothesis Hn:1<=n.
Hypothesis Hz:mark S0=false.
Hypothesis Hclosed:closed_b hcconf hctx_enc(hng_succs tm k n ls rs)Sl=true.
Hypothesis Hedges:cm_edges tm k n ls rs mark Sl=true.
Lemma pm_reaches_A : forall weight,
 weight S0=0 -> mp_rank_check tm weight=true ->
 forall cc a,In a Sl -> hcovers n ls rs a(lift cc) -> em_inv mark cc ->
 mp_capacity weight cc -> ore_reaches tm StA cc.
Proof.
 intros weight Hzero Hr.
 apply(well_founded_induction_type(well_founded_ltof cconf(mp_measure weight))
  (fun cc=>forall a,In a Sl -> hcovers n ls rs a(lift cc) -> em_inv mark cc ->
   mp_capacity weight cc -> ore_reaches tm StA cc)).
 intros[q[[l h]r]]IH a Hin Hcov Hi Hcap;destruct q.
 - exists 0,(StA,(l,h,r));split;reflexivity.
 - destruct(pm_B_defined tm weight h Hr)as(tr&Et).
   assert(E:cstep tm(StB,(l,h,r))=Some(t_next tr,ctape_move(t_dir tr)(t_write tr)(l,h,r))).
   {cbn[cstep];rewrite Et;reflexivity. }
   destruct(t_next tr)eqn:En.
   + eapply ore_reaches_step;[exact E|];exists 0;eexists;split;reflexivity.
   + destruct(cm_preserve_step tm k n ls rs Sl mark Hn Hz Hclosed Hedges _ _ _ Hin Hcov Hi E)as(a'&Hin'&Hcov'&Hi').
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

Definition pm_check tm mask w1 w2 w3 k n t fuel rounds :=
 let mark:=ms_mark mask in let weight:=mp_weights w1 w2 w3 in
 negb(mark S0) && (mp_rank_check tm weight &&
 (ore_auto_goal(orc_fill_goal tm StB)StB && ((1<=?n) &&
 match hcsteps tm k t hcconf0 with
 |None=>false
 |Some cc=>let '(_, (l,_,r)):=cc in
  let a0:=hng_start n cc in
  let '(ls,rs):=hn_grow tm k n a0 fuel rounds(hseed_side n l)(hseed_side n r)in
  let Sl:=hn_explore tm k n ls rs fuel [] PositiveSet.empty[a0]in
  cm_initial mark(hproj cc) && (hseed_ok n ls rs cc &&
  (closed_b hcconf hctx_enc(hng_succs tm k n ls rs)Sl &&
  (mem hcconf hctx_enc a0 Sl && cm_edges tm k n ls rs mark Sl)))
 end))).

Theorem pm_check_sound : forall tm mask w1 w2 w3 k n t fuel rounds,
 pm_check tm mask w1 w2 w3 k n t fuel rounds=true -> NonHalt tm /\ QHBound 0 tm.
Proof.
 intros tm mask w1 w2 w3 k n t fuel rounds H;unfold pm_check in H;cbv zeta in H.
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
 apply cm_initial_sound in Hi.
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
  destruct(cm_preserve_steps tm k n ls rs Sl(ms_mark mask)Hn Hz Hclosed Hedges
    N cc0 cc a0 Hin Hcov Hi EN)as(a&Ha&Hca&Hia).
  set(weight:=mp_weights w1 w2 w3).
  assert(Hw:weight S0=0)by reflexivity.
  set(padded:=mp_pad(S(mp_weight weight cc))cc).
  assert(Hcp:hcovers n ls rs a(lift padded)).
  {unfold padded;rewrite mp_pad_lift;exact Hca. }
  assert(Hip:em_inv(ms_mark mask)padded)by(apply em_pad_inv;exact Hia).
  assert(Hcapacity:mp_capacity weight padded)by(apply mp_padded_capacity;exact Hw).
  destruct(pm_reaches_A tm k n ls rs Sl(ms_mark mask)Hn Hz Hclosed Hedges
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
Print Assumptions pm_check_sound.
