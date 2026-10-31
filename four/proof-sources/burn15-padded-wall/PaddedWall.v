(** A single untouched blank supplies a left boundary for each B-only tail.
    The right boundary is protected by an actual historical-cell marker. *)
From Coq Require Import List Arith Lia Bool Wf_nat NArith.
From BBB24 Require Import Statement Spec CTape PosEnc Closure HistCensus HistRankSearch
 OneStateReach OneStateConditional MarkerState MarkerPotential.
From BBB24.Checkers Require Import NGram NGramHist.
From BBB24Burn12HistoryMarker Require Import HistoryMarker.
Import ListNotations.

Definition pw_guard(mask:N)(s:Sym) := N.testbit mask
 (match s with S0=>0|S1=>1|S2=>2|S3=>3 end)%N.
Definition pw_rank(r0 r1 r2 r3:nat)(s:Sym) :=
 match s with S0=>r0|S1=>r1|S2=>r2|S3=>r3 end.
Definition pw_cell tm(rank:Sym->nat)h := match tm StB h with
 |None=>false|Some tr=>st_eqb(t_next tr)StA ||
 match t_dir tr with DL=>true|DR=>rank(t_write tr)<?rank h end end.
Definition pw_rank_check tm rank :=
 forallb(fun h=>rank h<=?4)ore_symbols && forallb(pw_cell tm rank)ore_symbols.
Definition pw_guard_check tm guard := guard S0 &&
 forallb(fun h=>negb(guard h) || match tm StB h with
 |None=>false|Some tr=>st_eqb(t_next tr)StA ||
 match t_dir tr with DL=>false|DR=>guard(t_write tr)end end)ore_symbols.
Fixpoint pw_boundary(l:list hsym)(h:hsym) := match l with
 |[]=>h|b::rest=>pw_boundary rest b end.
Definition pw_wall guard(cc:hcconf) :=
 let '(_, (l,h,_)):=cc in guard(hbit(pw_boundary l h))=true.

Lemma pw_B_defined : forall tm rank h,
 pw_rank_check tm rank=true -> exists tr,tm StB h=Some tr.
Proof.
 intros tm rank h H;unfold pw_rank_check in H;apply andb_prop in H as[_ H].
 apply forallb_forall with(x:=h)in H;[|apply ore_symbols_complete].
 unfold pw_cell in H;destruct(tm StB h)as[tr|]eqn:E;[eauto|discriminate].
Qed.
Lemma pw_rank_bound : forall tm rank h,
 pw_rank_check tm rank=true -> rank h<=4.
Proof.
 intros tm rank h H;apply andb_prop in H as[H _].
 apply forallb_forall with(x:=h)in H;[apply Nat.leb_le;exact H|apply ore_symbols_complete].
Qed.
Lemma pw_right_delta : forall tm rank h tr,
 pw_rank_check tm rank=true -> tm StB h=Some tr -> t_next tr=StB ->
 t_dir tr=DR -> rank(t_write tr)<rank h.
Proof.
 intros tm rank h tr H Et En Ed;apply andb_prop in H as[_ H].
 apply forallb_forall with(x:=h)in H;[|apply ore_symbols_complete].
 unfold pw_cell in H;rewrite Et,En,Ed in H;apply Nat.ltb_lt;exact H.
Qed.
Lemma pw_guard_zero : forall tm guard,pw_guard_check tm guard=true -> guard S0=true.
Proof. intros tm guard H;apply andb_prop in H;tauto. Qed.
Lemma pw_guard_step : forall tm guard h tr,
 pw_guard_check tm guard=true -> tm StB h=Some tr -> t_next tr=StB ->
 guard h=true -> t_dir tr=DR /\ guard(t_write tr)=true.
Proof.
 intros tm guard h tr H Et En Hh;apply andb_prop in H as[_ H].
 apply forallb_forall with(x:=h)in H;[|apply ore_symbols_complete].
 rewrite Hh,Et,En in H;destruct(t_dir tr)eqn:Ed;[discriminate|];split;auto.
Qed.
Lemma pw_boundary_pad : forall l h,pw_boundary(l++[hblank])h=hblank.
Proof. induction l;intro h;cbn[pw_boundary app];[reflexivity|apply IHl]. Qed.
Lemma pw_pad_wall : forall tm guard cc,
 pw_guard_check tm guard=true -> pw_wall guard(hm_pad 1 cc).
Proof.
 intros tm guard[q[[l h]r]]H;unfold hm_pad,pw_wall;cbn[repeat].
 rewrite pw_boundary_pad;apply(pw_guard_zero tm guard H).
Qed.
Lemma pw_wall_step : forall tm guard l h r tr k,
 pw_guard_check tm guard=true -> tm StB(hbit h)=Some tr -> t_next tr=StB ->
 pw_wall guard(StB,(l,h,r)) ->
 pw_wall guard(StB,hctape_move(t_dir tr)
  (t_write tr,firstn k((StB,hbit h)::snd h))(l,h,r)).
Proof.
 intros tm guard l h r tr k Hg Et En Hwall.
 destruct(t_dir tr)eqn:Ed;destruct l as[|b l];
  cbn[hctape_move hchd hctl pw_wall pw_boundary]in *;try exact Hwall.
 - destruct(pw_guard_step tm guard(hbit h)tr Hg Et En Hwall)as[Hd _];congruence.
 - exact(proj2(pw_guard_step tm guard(hbit h)tr Hg Et En Hwall)).
Qed.

Section Graph.
Variables (tm:TM)(k n:nat)(ls rs:hgset)(Sl:list hcconf)(mark:hsym->bool).
Hypothesis Hn:1<=n.
Hypothesis Hz:mark hblank=false.
Hypothesis Hclosed:closed_b hcconf hctx_enc(hng_succs tm k n ls rs)Sl=true.
Hypothesis Hedges:hm_edges tm k n ls rs mark Sl=true.

Lemma pw_reaches_A : forall rank guard,
 pw_rank_check tm rank=true -> pw_guard_check tm guard=true ->
 forall cc a,In a Sl -> hng_covers n ls rs a cc -> hm_inv mark cc ->
 pw_wall guard cc -> ore_reaches tm StA(hproj cc).
Proof.
 intros rank guard Hr Hg.
 apply(well_founded_induction_type(well_founded_ltof hcconf(fun cc=>ore_measure rank(hproj cc)))
  (fun cc=>forall a,In a Sl -> hng_covers n ls rs a cc -> hm_inv mark cc ->
   pw_wall guard cc -> ore_reaches tm StA(hproj cc))).
 intros[q[[l h]r]]IH a Hin Hcov Hi Hwall;destruct q.
 - exists 0,(hproj(StA,(l,h,r)));split;reflexivity.
 - destruct(pw_B_defined tm rank(hbit h)Hr)as(tr&Et).
   set(w:=(t_write tr,firstn k((StB,hbit h)::snd h)):hsym).
   assert(E:hcstep tm k(StB,(l,h,r))=Some(t_next tr,hctape_move(t_dir tr)w(l,h,r))).
   {cbn[hcstep];rewrite Et;reflexivity. }
   pose proof(hcstep_proj_some tm k _ _ E)as Ep.
   destruct(t_next tr)eqn:En.
   + eapply ore_reaches_step;[exact Ep|];exists 0;eexists;split;
     [reflexivity|rewrite hproj_state;reflexivity].
   + destruct(hm_preserve_step tm k n ls rs Sl mark Hn Hz Hclosed Hedges
       _ _ _ Hin Hcov Hi E)as(a'&Hin'&Hcov'&Hi').
     pose proof(pw_wall_step tm guard l h r tr k Hg Et En Hwall)as Hwall'.
     destruct(t_dir tr)eqn:Ed;cbn[hctape_move]in E,Ep,Hcov',Hi',Hwall'.
     * destruct l as[|b l];cbn[hchd hctl]in E,Ep,Hcov',Hi',Hwall'.
       -- change(guard(hbit h)=true)in Hwall.
          destruct(pw_guard_step tm guard(hbit h)tr Hg Et En Hwall)as[Hd _];congruence.
       -- eapply ore_reaches_step;[exact Ep|];eapply IH with(a:=a');try assumption.
          ++ unfold ltof;cbn[hproj hproj_side hbit w].
             apply ore_left_drop;eapply pw_rank_bound;exact Hr.
     * destruct r as[|b r];cbn[hchd hctl]in E,Ep,Hcov',Hi',Hwall'.
       -- change(hm_has mark[hblank])in Hi'.
          pose proof(hm_has_single mark hblank Hi');congruence.
       -- eapply ore_reaches_step;[exact Ep|];eapply IH with(a:=a');try assumption.
          ++ unfold ltof;cbn[hproj hproj_side hbit w].
             apply ore_right_drop;eapply pw_right_delta;eauto.
Qed.
End Graph.

Definition pw_check tm mask guardmask r0 r1 r2 r3 k n t fuel rounds :=
 let mark:=hm_mark mask in let rank:=pw_rank r0 r1 r2 r3 in let guard:=pw_guard guardmask in
 negb(mark hblank) && (pw_rank_check tm rank && (pw_guard_check tm guard &&
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
 end)))).

Theorem pw_check_sound : forall tm mask guardmask r0 r1 r2 r3 k n t fuel rounds,
 pw_check tm mask guardmask r0 r1 r2 r3 k n t fuel rounds=true -> NonHalt tm /\ QHBound 0 tm.
Proof.
 intros tm mask guardmask r0 r1 r2 r3 k n t fuel rounds H;unfold pw_check in H;cbv zeta in H.
 repeat rewrite andb_true_iff in H;destruct H as[Hz[Hr[Hg[HB[Hn H]]]]].
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
  set(rank:=pw_rank r0 r1 r2 r3);set(guard:=pw_guard guardmask).
  set(padded:=hm_pad 1 cc).
  assert(Hcp:hng_covers n ls rs a padded)by(apply hm_pad_covers;exact Hca).
  assert(Hip:hm_inv(hm_mark mask)padded)by(apply hm_pad_inv;exact Hia).
  assert(Hwall:pw_wall guard padded)by(eapply pw_pad_wall;exact Hg).
  destruct(pw_reaches_A tm k n ls rs Sl(hm_mark mask)Hn Hz Hclosed Hedges
    rank guard Hr Hg padded a Ha Hcp Hip Hwall)as(j&cc'&Ej&Hstate).
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
Print Assumptions pw_check_sound.
