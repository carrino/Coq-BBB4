(** State recurrence between independently preserved left and right markers.
    A checked two-step boot establishes the left wall; both walls then prevent
    avoiding episodes from enlarging the finite tape used by the rank measure. *)
From Coq Require Import List Arith Lia Bool Wf_nat NArith.
From BBB24 Require Import Statement Spec CTape Census TotalCompletion
 OneStateReach StatePipeline StateOnlyCloseout MarkerState.
Import ListNotations.

Definition mw_has mark(l:list Sym) := exists h,In h l /\ mark h=true.
Definition mw_left mark(cc:cconf) := let '(q,(l,h,r)):=cc in
 mw_has mark l \/ (q=StB /\ mark h=true).
Definition mw_leftb mark(cc:cconf) := let '(q,(l,h,r)):=cc in
 existsb mark l || (st_eqb q StB && mark h).
Definition mw_cell tm mark q h := match tm q h with
 |None=>false |Some tr=>
 (match t_dir tr with DL=>st_eqb(t_next tr)StB |DR=>true end) &&
 (if st_eqb q StB && mark h then
   match t_dir tr with DL=>false |DR=>mark(t_write tr) end else true)
 end.
Definition mw_preserve tm mark := forallb(fun q=>forallb(mw_cell tm mark q)ore_symbols)all_St.
Definition mw_rank_cell tm rank h := match tm StB h with
 |None=>false |Some tr=>st_eqb(t_next tr)StA ||
   match t_dir tr with DL=>true |DR=>rank(t_write tr)<?rank h end end.
Definition mw_rank_check tm rank := forallb(fun h=>rank h<=?4)ore_symbols &&
 forallb(mw_rank_cell tm rank)ore_symbols.
Definition mw_boot tm mark := match csteps tm 2 c0 with
 |None=>false |Some cc=>mw_leftb mark cc end.
Definition mw_check tm mask := let mark:=ms_mark mask in
 negb(mark S0) && (ms_preserve tm mark && (mw_preserve tm mark &&
 (mw_boot tm mark && (mw_rank_check tm(ore_rank_walk tm StA 4) && ore_auto_goal tm StB)))).

Lemma mw_leftb_sound : forall mark cc,mw_leftb mark cc=true -> mw_left mark cc.
Proof.
 intros mark[q[[l h]r]]H;unfold mw_leftb in H;unfold mw_left.
 apply orb_true_iff in H as[H|H].
 - left;apply existsb_exists in H;exact H.
 - right;apply andb_prop in H as[Hq Hh];apply st_eqb_spec in Hq;auto.
Qed.
Lemma mw_checked_cell : forall tm mark q h tr,
 mw_preserve tm mark=true -> tm q h=Some tr ->
 (t_dir tr=DL -> t_next tr=StB) /\
 (q=StB -> mark h=true -> t_dir tr=DR /\ mark(t_write tr)=true).
Proof.
 intros tm mark q h tr H Et. unfold mw_preserve in H.
 apply forallb_forall with(x:=q)in H;[|apply all_St_complete].
 apply forallb_forall with(x:=h)in H;[|apply ore_symbols_complete].
 unfold mw_cell in H;rewrite Et in H;apply andb_prop in H as[Hd Hm];split.
 - intro Ed;rewrite Ed in Hd;apply st_eqb_spec;exact Hd.
 - intros -> Hmark. change((if mark h then
    match t_dir tr with DL=>false|DR=>mark(t_write tr)end else true)=true)in Hm.
   rewrite Hmark in Hm. destruct(t_dir tr);[discriminate|auto].
Qed.
Lemma mw_left_step : forall tm mark cc cc',
 ms_preserve tm mark=true -> mw_preserve tm mark=true ->
 mw_left mark cc -> cstep tm cc=Some cc' -> mw_left mark cc'.
Proof.
 intros tm mark[q[[l h]r]]cc' Hp Hw Hi Es.
 destruct(ms_checked_cell tm mark q h Hp)as(tr&Et&_).
 pose proof(mw_checked_cell tm mark q h tr Hw Et)as[Hleft Hmarked].
 cbn[cstep]in Es;rewrite Et in Es;injection Es as <-.
 unfold mw_left in *. destruct Hi as[(x&Hin&Hx)|[-> Hh]].
 - destruct(t_dir tr)eqn:Ed;cbn[ctape_move].
   + destruct l as[|a l];[contradiction|]. cbn[chd ctl].
     destruct Hin as[<-|Hin].
     * right;split;[apply Hleft;reflexivity|exact Hx].
     * left;exists x;auto.
   + left;exists x;split;[right;exact Hin|exact Hx].
 - destruct(Hmarked eq_refl Hh)as[Ed Hwrite];rewrite Ed;cbn[ctape_move].
   left;exists(t_write tr);split;[left;reflexivity|exact Hwrite].
Qed.
Lemma mw_left_steps : forall tm mark n cc cc',
 ms_preserve tm mark=true -> mw_preserve tm mark=true ->
 mw_left mark cc -> csteps tm n cc=Some cc' -> mw_left mark cc'.
Proof.
 intros tm mark n;induction n;intros cc cc' Hp Hw Hi E;cbn[csteps]in E.
 - inversion E;subst;exact Hi.
 - destruct(cstep tm cc)as[cm|]eqn:Es;[|discriminate].
   eapply IHn;[exact Hp|exact Hw|eapply mw_left_step;eauto|exact E].
Qed.
Lemma mw_rank_bound : forall tm rank h,mw_rank_check tm rank=true -> rank h<=4.
Proof.
 intros tm rank h H;apply andb_prop in H as[H _].
 apply forallb_forall with(x:=h)in H;[apply Nat.leb_le;exact H|apply ore_symbols_complete].
Qed.
Lemma mw_rank_drop : forall tm rank h tr,
 mw_rank_check tm rank=true -> tm StB h=Some tr -> t_next tr=StB ->
 t_dir tr=DR -> rank(t_write tr)<rank h.
Proof.
 intros tm rank h tr H Et En Ed;apply andb_prop in H as[_ H].
 apply forallb_forall with(x:=h)in H;[|apply ore_symbols_complete].
 unfold mw_rank_cell in H;rewrite Et,En,Ed in H;apply Nat.ltb_lt;exact H.
Qed.
Lemma mw_reaches_A : forall tm mark rank,
 ms_preserve tm mark=true -> mw_preserve tm mark=true -> mw_rank_check tm rank=true ->
 forall cc,ms_inv mark cc -> mw_left mark cc -> ore_reaches tm StA cc.
Proof.
 intros tm mark rank Hp Hw Hr.
 apply(well_founded_induction_type(well_founded_ltof cconf(ore_measure rank))
   (fun cc=>ms_inv mark cc -> mw_left mark cc -> ore_reaches tm StA cc)).
 intros[q[[l h]r]]IH Hi Hl;destruct q.
 - exists 0,(StA,(l,h,r));split;reflexivity.
 - destruct(ms_checked_cell tm mark StB h Hp)as(tr&Et&Hkeep&Hexit).
   assert(Hstep:cstep tm(StB,(l,h,r))=Some(t_next tr,ctape_move(t_dir tr)(t_write tr)(l,h,r)))
    by(cbn[cstep];rewrite Et;reflexivity).
   destruct(t_next tr)eqn:En.
   + eapply ore_reaches_step;[exact Hstep|]. exists 0;eexists;split;reflexivity.
   + destruct(t_dir tr)eqn:Ed;cbn[ctape_move]in Hstep.
     * destruct l as[|a l];cbn[chd ctl]in Hstep.
       -- destruct Hl as[(x&Hin&_)|[_ Hm]];[contradiction|].
          specialize(Hexit eq_refl Hm);congruence.
       -- eapply ore_reaches_step;[exact Hstep|]. apply IH.
          ++ unfold ltof;apply ore_left_drop;eapply mw_rank_bound;exact Hr.
          ++ eapply ms_inv_step;eauto.
          ++ eapply mw_left_step;eauto.
     * destruct r as[|b r];cbn[chd ctl]in Hstep.
       -- pose proof(ms_single mark h(ms_inv_B mark l h [] Hi))as Hm.
          specialize(Hexit eq_refl Hm);congruence.
       -- eapply ore_reaches_step;[exact Hstep|]. apply IH.
          ++ unfold ltof;apply ore_right_drop;eapply mw_rank_drop;eauto.
          ++ eapply ms_inv_step;eauto.
          ++ eapply mw_left_step;eauto.
Qed.
Theorem mw_check_sound : forall tm mask,
 mw_check tm mask=true -> NonHalt tm /\ QHBound 0 tm.
Proof.
 intros tm mask H;unfold mw_check in H;cbv zeta in H.
 repeat rewrite andb_true_iff in H. destruct H as[Hzero[Hp[Hw[Hboot[Hr Hother]]]]].
 assert(Htotal:Total tm)by(eapply ms_preserve_total;exact Hp).
 unfold mw_boot in Hboot. destruct(csteps tm 2 c0)as[boot|]eqn:Eboot;[|discriminate].
 apply mw_leftb_sound in Hboot.
 assert(Hrecur:forall goal N,exists n,N<=n /\ VisitsAt tm goal n).
 {intros goal N;destruct goal.
  - destruct(ore_total_csteps tm Htotal N boot)as(cc&Etail).
    assert(Eprefix:csteps tm(2+N)c0=Some cc)by(rewrite csteps_add,Eboot;exact Etail).
    assert(Hi:ms_inv(ms_mark mask)cc)by(eapply ms_inv_steps;[exact Hp|apply ms_inv_initial|exact Eprefix]).
    assert(Hl:mw_left(ms_mark mask)cc)by(eapply mw_left_steps;eauto).
    destruct(mw_reaches_A tm(ms_mark mask)_ Hp Hw Hr cc Hi Hl)as(k&cc'&Eend&Hstate).
    exists(2+N+k);split;[lia|]. exists(lift cc');split;[|exact Hstate].
    rewrite <-lift_c0. apply csteps_lift. rewrite csteps_add,Eprefix;exact Eend.
  - apply(ore_reaches_recurs tm StB Htotal). apply ore_auto_goal_sound;exact Hother. }
 split;[apply ore_total_nonhalt;exact Htotal|].
 intros q s [_ Hquiet]. destruct(Hrecur q(S s))as(n&Hn&Hv).
 exfalso;apply(Hquiet n);[lia|exact Hv].
Qed.
Definition mw_batch_check(rows:list(N*N)) :=
 forallb(fun '(packed,mask)=>mw_check(stp_machine packed)mask)rows.
Definition mw_board(rows:list(N*N)) := map(fun row=>stp_machine(fst row))rows.
Theorem mw_batch_state_sound : forall rows,
 mw_batch_check rows=true -> StateBoardSound 0(mw_board rows).
Proof.
 intros rows H family Hin tm Hle. apply in_map_iff in Hin as([packed mask]&<-&Hin).
 apply forallb_forall with(x:=(packed,mask))in H;[|exact Hin].
 destruct(mw_check_sound _ _ H)as[Hnh Hb]. eapply state_bound_extend;eauto.
Qed.
Theorem mw_batch_nonhalt : forall rows,
 mw_batch_check rows=true -> forall family,In family(mw_board rows)->NonHalt family.
Proof.
 intros rows H family Hin. apply in_map_iff in Hin as([packed mask]&<-&Hin).
 apply forallb_forall with(x:=(packed,mask))in H;[|exact Hin].
 exact(proj1(mw_check_sound _ _ H)).
Qed.
Print Assumptions mw_check_sound.
