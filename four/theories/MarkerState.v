(** Checked state recurrence from a rightmost-marker invariant.
    This checker proves STATE bound0 only. It accepts total tables and uses
    either a right sweep or a symbol-rank decrease for B-only episodes.
    A-only episodes use the independent OneStateReach checker. *)
From Coq Require Import List Arith Lia Bool Wf_nat NArith.
From BBB24 Require Import Statement Spec CTape Census TotalCompletion
 OneStateReach StatePipeline StateOnlyCloseout RightMarkerState.
Import ListNotations.

Definition ms_mark (mask:N)(h:Sym) := N.testbit mask
 (match h with S0=>0 |S1=>1 |S2=>2 |S3=>3 end)%N.
Definition ms_keeps (mark:Sym->bool)(tr:Trans) := match t_dir tr with
 |DL=>mark(t_write tr) |DR=>st_eqb(t_next tr)StA end.
Definition ms_cell (tm:TM)(mark:Sym->bool)(q:St)(h:Sym) := match tm q h with
 |None=>false
 |Some tr=>
 (if (st_eqb q StA && sym_eqb h S0)||mark h then ms_keeps mark tr else true) &&
 (if st_eqb q StB && mark h then st_eqb(t_next tr)StA else true)
 end.
Definition ms_preserve (tm:TM)(mark:Sym->bool) :=
 forallb(fun q=>forallb(ms_cell tm mark q)ore_symbols)all_St.
Definition ms_blank (tm:TM) := match tm StB S0 with
 |None=>false |Some tr=>st_eqb(t_next tr)StB && match t_dir tr with DL=>false|DR=>true end end.
Definition ms_exit (tm:TM)(h:Sym) := match tm StB h with
 |None=>false |Some tr=>st_eqb(t_next tr)StA end.
Definition ms_right_cell (tm:TM)(h:Sym) := match tm StB h with
 |None=>false |Some tr=>st_eqb(t_next tr)StA || match t_dir tr with DL=>false|DR=>true end end.
Definition ms_right_check (tm:TM) := forallb(ms_right_cell tm)ore_symbols.
Definition ms_rank_cell (tm:TM)(rank:Sym->nat)(h:Sym) := match tm StB h with
 |None=>false |Some tr=>st_eqb(t_next tr)StA ||
 match t_dir tr with DL=>ms_exit tm(t_write tr) |DR=>rank(t_write tr)<?rank h end end.
Definition ms_rank_check (tm:TM)(rank:Sym->nat) :=
 forallb(fun h=>rank h<=?4)ore_symbols && forallb(ms_rank_cell tm rank)ore_symbols.
Definition ms_check (tm:TM)(mask:N) :=
 let mark:=ms_mark mask in
 negb(mark S0) && (ms_preserve tm mark && (ms_blank tm &&
 ((ms_right_check tm || ms_rank_check tm(ore_rank_walk tm StA 4)) && ore_auto_goal tm StB))).

Lemma ms_checked_cell : forall tm mark q h,
 ms_preserve tm mark=true -> exists tr,tm q h=Some tr /\
 (((q=StA /\ h=S0) \/ mark h=true) ->
   match t_dir tr with DL=>mark(t_write tr)=true |DR=>t_next tr=StA end) /\
 (q=StB -> mark h=true -> t_next tr=StA).
Proof.
 intros tm mark q h H. unfold ms_preserve in H.
 apply forallb_forall with(x:=q)in H;[|apply all_St_complete].
 apply forallb_forall with(x:=h)in H;[|apply ore_symbols_complete].
 unfold ms_cell in H. destruct(tm q h)as[tr|]eqn:Et;[|discriminate].
 apply andb_prop in H as[Hp He]. exists tr;split;[reflexivity|];split.
 - intros Hguard. assert(G:((st_eqb q StA && sym_eqb h S0)||mark h)=true).
   {apply orb_true_iff. destruct Hguard as[[-> ->]|Hm];[left;reflexivity|right;exact Hm]. }
   rewrite G in Hp. unfold ms_keeps in Hp. destruct(t_dir tr);[exact Hp|].
   apply st_eqb_spec;exact Hp.
 - intros -> Hm. change ((if mark h then st_eqb(t_next tr)StA else true)=true) in He.
   rewrite Hm in He. apply st_eqb_spec;exact He.
Qed.
Lemma ms_preserve_total : forall tm mark,ms_preserve tm mark=true -> Total tm.
Proof. intros tm mark H q h;destruct(ms_checked_cell tm mark q h H)as(tr&Et&_);eauto. Qed.

Inductive ms_marker (mark:Sym->bool) : list Sym -> Prop :=
 | ms_at : forall h r,mark h=true -> mr_zeros r -> ms_marker mark(h::r)
 | ms_skip : forall h r,ms_marker mark r -> ms_marker mark(h::r).
Definition ms_inv mark(cc:cconf) := let '(q,(l,h,r)):=cc in
 ms_marker mark(h::r) \/ (q=StA /\ mr_zeros(h::r)).
Lemma ms_right_marker : forall mark r,ms_marker mark r -> ms_marker mark(chd r::ctl r).
Proof. intros mark[|h r]H;[inversion H|exact H]. Qed.
Lemma ms_single : forall mark h,ms_marker mark[h] -> mark h=true.
Proof. intros mark h H;inversion H;subst;[assumption|match goal with H:ms_marker _ []|-_=>inversion H end]. Qed.
Lemma ms_inv_step : forall tm mark cc cc',
 ms_preserve tm mark=true -> ms_inv mark cc -> cstep tm cc=Some cc' -> ms_inv mark cc'.
Proof.
 intros tm mark[q[[l h]r]]cc' Hp Hinv E.
 destruct(ms_checked_cell tm mark q h Hp)as(tr&Et&Hkeep&Hexit).
 cbn[cstep]in E;rewrite Et in E;injection E as <-.
 unfold ms_inv in *. cbn[fst snd]in *.
 destruct Hinv as[Hmarker|[Hq Hz]].
 - inversion Hmarker as[hh rr Hmarked Hz|hh rr Htail];subst.
   + specialize(Hkeep(or_intror Hmarked)). destruct(t_dir tr)eqn:Ed;cbn[ctape_move].
     * left;apply ms_skip;apply ms_at;assumption.
     * right;split;[exact Hkeep|apply mr_right_zeros;exact Hz].
   + destruct(t_dir tr);cbn[ctape_move];left.
     * apply ms_skip;apply ms_skip;exact Htail.
     * apply ms_right_marker;exact Htail.
 - subst q. apply mr_zero_cons in Hz as[-> Hz].
   specialize(Hkeep(or_introl(conj eq_refl eq_refl))).
   destruct(t_dir tr);cbn[ctape_move].
   + left;apply ms_skip;apply ms_at;assumption.
   + right;split;[exact Hkeep|apply mr_right_zeros;exact Hz].
Qed.
Lemma ms_inv_steps : forall tm mark n cc cc',
 ms_preserve tm mark=true -> ms_inv mark cc -> csteps tm n cc=Some cc' -> ms_inv mark cc'.
Proof.
 intros tm mark n;induction n;intros cc cc' Hp Hi E;cbn[csteps]in E.
 - inversion E;subst;exact Hi.
 - destruct(cstep tm cc)as[cm|]eqn:Es;[|discriminate].
   eapply IHn;[exact Hp|eapply ms_inv_step;eauto|exact E].
Qed.
Lemma ms_inv_initial : forall mark,ms_inv mark c0.
Proof. intros;right;split;[reflexivity|repeat constructor]. Qed.
Lemma ms_inv_B : forall mark l h r,ms_inv mark(StB,(l,h,r))->ms_marker mark(h::r).
Proof. intros mark l h r[H|[H _]];[exact H|discriminate]. Qed.

Lemma ms_checked_right : forall tm h tr,
 ms_right_check tm=true -> tm StB h=Some tr -> t_next tr=StB -> t_dir tr=DR.
Proof.
 intros tm h tr H Et En. unfold ms_right_check in H.
 apply forallb_forall with(x:=h)in H;[|apply ore_symbols_complete].
 unfold ms_right_cell in H;rewrite Et,En in H.
 destruct(t_dir tr);[discriminate|reflexivity].
Qed.
Definition ms_right_length(cc:cconf) := let '(_,(_,_,r)):=cc in length r.
Lemma ms_right_reaches : forall tm mark,
 ms_preserve tm mark=true -> ms_right_check tm=true ->
 forall cc,ms_inv mark cc -> ore_reaches tm StA cc.
Proof.
 intros tm mark Hp Hr.
 apply(well_founded_induction_type(well_founded_ltof cconf ms_right_length)
  (fun cc=>ms_inv mark cc -> ore_reaches tm StA cc)).
 intros[q[[l h]r]]IH Hi. destruct q.
 - exists 0,(StA,(l,h,r));split;reflexivity.
 - destruct(ms_checked_cell tm mark StB h Hp)as(tr&Et&Hkeep&Hexit).
   assert(Hstep:cstep tm(StB,(l,h,r))=Some(t_next tr,ctape_move(t_dir tr)(t_write tr)(l,h,r))).
   {cbn[cstep];rewrite Et;reflexivity. }
   destruct(t_next tr)eqn:En.
   + eapply ore_reaches_step;[exact Hstep|]. exists 0;eexists;split;reflexivity.
   + assert(Ed:t_dir tr=DR)by(eapply ms_checked_right;eauto).
     rewrite Ed in Hstep. cbn[ctape_move]in Hstep.
     destruct r as[|b r].
     * pose proof(ms_single mark h(ms_inv_B mark l h [] Hi))as Hm.
       specialize(Hexit eq_refl Hm);congruence.
     * eapply ore_reaches_step;[exact Hstep|]. apply IH.
       -- unfold ltof,ms_right_length;cbn;lia.
       -- eapply ms_inv_step;eauto.
Qed.

Lemma ms_checked_blank : forall tm,ms_blank tm=true ->
 exists tr,tm StB S0=Some tr /\ t_next tr=StB /\ t_dir tr=DR.
Proof.
 intros tm H;unfold ms_blank in H. destruct(tm StB S0)as[tr|]eqn:E;[|discriminate].
 apply andb_prop in H as[Hq Hd]. apply st_eqb_spec in Hq.
 destruct(t_dir tr)eqn:Ed;[discriminate|]. exists tr;auto.
Qed.
Lemma ms_exit_reaches : forall tm l h r,
 ms_exit tm h=true -> ore_reaches tm StA(StB,(l,h,r)).
Proof.
 intros tm l h r H;unfold ms_exit in H.
 destruct(tm StB h)as[tr|]eqn:Et;[|discriminate]. apply st_eqb_spec in H.
 exists 1,(t_next tr,ctape_move(t_dir tr)(t_write tr)(l,h,r));split;[|exact H].
 rewrite csteps_1;cbn[cstep];rewrite Et;reflexivity.
Qed.
Lemma ms_blank_return : forall tm l h r,
 ms_blank tm=true -> ms_exit tm h=true -> ore_reaches tm StA(StB,(l,S0,h::r)).
Proof.
 intros tm l h r Hb He. destruct(ms_checked_blank tm Hb)as(tr&Et&En&Ed).
 eapply ore_reaches_step.
 - cbn[cstep];rewrite Et,En,Ed;reflexivity.
 - apply ms_exit_reaches;exact He.
Qed.
Lemma ms_checked_rank_bound : forall tm rank h,
 ms_rank_check tm rank=true -> rank h<=4.
Proof.
 intros tm rank h H;apply andb_prop in H as[H _].
 apply forallb_forall with(x:=h)in H;[apply Nat.leb_le;exact H|apply ore_symbols_complete].
Qed.
Lemma ms_checked_rank_cell : forall tm rank h tr,
 ms_rank_check tm rank=true -> tm StB h=Some tr -> t_next tr=StB ->
 match t_dir tr with DL=>ms_exit tm(t_write tr)=true |DR=>rank(t_write tr)<rank h end.
Proof.
 intros tm rank h tr H Et En;apply andb_prop in H as[_ H].
 apply forallb_forall with(x:=h)in H;[|apply ore_symbols_complete].
 unfold ms_rank_cell in H;rewrite Et,En in H.
 destruct(t_dir tr);[exact H|apply Nat.ltb_lt;exact H].
Qed.
Lemma ms_rank_reaches : forall tm mark rank,
 ms_preserve tm mark=true -> ms_blank tm=true -> ms_rank_check tm rank=true ->
 forall cc,ms_inv mark cc -> ore_reaches tm StA cc.
Proof.
 intros tm mark rank Hp Hb Hr.
 apply(well_founded_induction_type(well_founded_ltof cconf(ore_measure rank))
  (fun cc=>ms_inv mark cc -> ore_reaches tm StA cc)).
 intros[q[[l h]r]]IH Hi. destruct q.
 - exists 0,(StA,(l,h,r));split;reflexivity.
 - destruct(ms_checked_cell tm mark StB h Hp)as(tr&Et&Hkeep&Hexit).
   assert(Hstep:cstep tm(StB,(l,h,r))=Some(t_next tr,ctape_move(t_dir tr)(t_write tr)(l,h,r))).
   {cbn[cstep];rewrite Et;reflexivity. }
   destruct(t_next tr)eqn:En.
   + eapply ore_reaches_step;[exact Hstep|]. exists 0;eexists;split;reflexivity.
   + pose proof(ms_checked_rank_cell tm rank h tr Hr Et En)as Hrank.
     destruct(t_dir tr)eqn:Ed;cbn[ctape_move]in Hstep.
     * destruct l as[|a l];cbn[chd ctl]in Hstep.
       -- eapply ore_reaches_step;[exact Hstep|]. apply ms_blank_return;assumption.
       -- eapply ore_reaches_step;[exact Hstep|]. apply IH.
          ++ unfold ltof. apply ore_left_drop. eapply ms_checked_rank_bound;exact Hr.
          ++ eapply ms_inv_step;eauto.
     * destruct r as[|b r];cbn[chd ctl]in Hstep.
       -- pose proof(ms_single mark h(ms_inv_B mark l h [] Hi))as Hm.
          specialize(Hexit eq_refl Hm);congruence.
       -- eapply ore_reaches_step;[exact Hstep|]. apply IH.
          ++ unfold ltof. apply ore_right_drop;exact Hrank.
          ++ eapply ms_inv_step;eauto.
Qed.

Theorem ms_check_sound : forall tm mask,
 ms_check tm mask=true -> NonHalt tm /\ QHBound 0 tm.
Proof.
 intros tm mask H;unfold ms_check in H;cbv zeta in H.
 repeat rewrite andb_true_iff in H. destruct H as[Hzero[Hp[Hb[Hmode Hother]]]].
 assert(Htotal:Total tm)by(eapply ms_preserve_total;exact Hp).
 assert(Hreach:forall cc,ms_inv(ms_mark mask)cc -> ore_reaches tm StA cc).
 {apply orb_true_iff in Hmode as[Hr|Hr].
  - eapply ms_right_reaches;eauto.
  - eapply ms_rank_reaches;eauto. }
 assert(Hrecur:forall goal N,exists n,N<=n /\ VisitsAt tm goal n).
 {intros goal N;destruct goal.
  - destruct(ore_total_csteps tm Htotal N c0)as(cc&Eprefix).
    assert(Hi:ms_inv(ms_mark mask)cc)by(eapply ms_inv_steps;[exact Hp|apply ms_inv_initial|exact Eprefix]).
    destruct(Hreach cc Hi)as(k&cc'&Etail&Hstate).
    exists(N+k);split;[lia|]. exists(lift cc');split;[|exact Hstate].
    rewrite <-lift_c0. apply csteps_lift. rewrite csteps_add,Eprefix;exact Etail.
  - apply(ore_reaches_recurs tm StB Htotal). apply ore_auto_goal_sound;exact Hother. }
 split;[apply ore_total_nonhalt;exact Htotal|].
 intros q s [_ Hquiet]. destruct(Hrecur q(S s))as(n&Hn&Hv).
 exfalso;apply(Hquiet n);[lia|exact Hv].
Qed.
Definition ms_batch_check(rows:list(N*N)) :=
 forallb(fun '(packed,mask)=>ms_check(stp_machine packed)mask)rows.
Definition ms_board(rows:list(N*N)) := map(fun row=>stp_machine(fst row))rows.
Theorem ms_batch_state_sound : forall rows,
 ms_batch_check rows=true -> StateBoardSound 0(ms_board rows).
Proof.
 intros rows H family Hin tm Hle. apply in_map_iff in Hin as([packed mask]&<-&Hin).
 apply forallb_forall with(x:=(packed,mask))in H;[|exact Hin].
 destruct(ms_check_sound _ _ H)as[Hnh Hb]. eapply state_bound_extend;eauto.
Qed.
Theorem ms_batch_nonhalt : forall rows,
 ms_batch_check rows=true -> forall family,In family(ms_board rows)->NonHalt family.
Proof.
 intros rows H family Hin. apply in_map_iff in Hin as([packed mask]&<-&Hin).
 apply forallb_forall with(x:=(packed,mask))in H;[|exact Hin].
 exact(proj1(ms_check_sound _ _ H)).
Qed.
Print Assumptions ms_check_sound.
