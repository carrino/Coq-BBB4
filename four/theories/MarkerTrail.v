(** A checked rightmost-marker recurrence criterion with an exit-symbol trail.
    Every B-self right step leaves an immediate return-to-A symbol behind it.
    Left steps are unrestricted. The conclusion is state bound zero only. *)
From Coq Require Import List Arith Lia Bool NArith.
From BBB24 Require Import Statement Spec CTape Census TotalCompletion
 OneStateReach StatePipeline StateOnlyCloseout MarkerState.
Import ListNotations.

Definition mt_cell (tm:TM)(h:Sym) := match tm StB h with
 |None=>false
 |Some tr=>st_eqb(t_next tr)StA ||
   match t_dir tr with DL=>true |DR=>ms_exit tm(t_write tr) end
 end.
Definition mt_trail (tm:TM) := forallb(mt_cell tm)ore_symbols.
Definition mt_check (tm:TM)(mask:N) :=
 let mark:=ms_mark mask in
 negb(mark S0) && (ms_preserve tm mark &&
 (ms_blank tm && (mt_trail tm && ore_auto_goal tm StB))).

Lemma mt_checked_cell : forall tm h tr,
 mt_trail tm=true -> tm StB h=Some tr -> t_next tr=StB ->
 t_dir tr=DR -> ms_exit tm(t_write tr)=true.
Proof.
 intros tm h tr H Et En Ed. unfold mt_trail in H.
 apply forallb_forall with(x:=h)in H;[|apply ore_symbols_complete].
 unfold mt_cell in H;rewrite Et,En,Ed in H;exact H.
Qed.

(** Once an exit is immediately to the left, every rightward continuation
    writes a fresh exit. A reversal therefore exits B in one further step. *)
Lemma mt_trail_reaches : forall tm mark,
 ms_preserve tm mark=true -> mt_trail tm=true ->
 forall r l h x,ms_exit tm x=true ->
 ms_inv mark(StB,(x::l,h,r)) -> ore_reaches tm StA(StB,(x::l,h,r)).
Proof.
 intros tm mark Hp Htrail r;induction r as[|b r IH];intros l h x Hx Hi;
 destruct(ms_checked_cell tm mark StB h Hp)as(tr&Et&Hkeep&Hexit);
 match type of Hi with ms_inv _ (StB,(?ls,?head,?rs)) =>
 assert(Hstep:cstep tm(StB,(ls,head,rs))=
   Some(t_next tr,ctape_move(t_dir tr)(t_write tr)(ls,head,rs)))
   by(cbn[cstep];rewrite Et;reflexivity) end.
 - destruct(t_next tr)eqn:En.
   + eapply ore_reaches_step;[exact Hstep|]. exists 0;eexists;split;reflexivity.
   + destruct(t_dir tr)eqn:Ed;cbn[ctape_move chd ctl]in Hstep.
     * eapply ore_reaches_step;[exact Hstep|]. apply ms_exit_reaches;exact Hx.
     * pose proof(ms_single mark h(ms_inv_B mark(x::l)h[] Hi))as Hm.
       specialize(Hexit eq_refl Hm);congruence.
 - destruct(t_next tr)eqn:En.
   + eapply ore_reaches_step;[exact Hstep|]. exists 0;eexists;split;reflexivity.
   + destruct(t_dir tr)eqn:Ed;cbn[ctape_move chd ctl]in Hstep.
     * eapply ore_reaches_step;[exact Hstep|]. apply ms_exit_reaches;exact Hx.
     * eapply ore_reaches_step;[exact Hstep|]. apply IH.
       -- eapply mt_checked_cell;eauto.
       -- eapply ms_inv_step;eauto.
Qed.

(** Before a trail exists, leftward motion shortens the finite left tape.
    At its boundary the checked B0 right step starts a trail. *)
Lemma mt_reaches_A : forall tm mark,
 ms_preserve tm mark=true -> ms_blank tm=true -> mt_trail tm=true ->
 forall cc,ms_inv mark cc -> ore_reaches tm StA cc.
Proof.
 intros tm mark Hp Hb Htrail[q[[l h]r]]Hi. destruct q.
 - exists 0,(StA,(l,h,r));split;reflexivity.
 - revert h r Hi. induction l as[|a l IH];intros h r Hi;
   destruct(ms_checked_cell tm mark StB h Hp)as(tr&Et&Hkeep&Hexit);
   match type of Hi with ms_inv _ (StB,(?ls,?head,?rs)) =>
   assert(Hstep:cstep tm(StB,(ls,head,rs))=
     Some(t_next tr,ctape_move(t_dir tr)(t_write tr)(ls,head,rs)))
     by(cbn[cstep];rewrite Et;reflexivity) end.
   + destruct(t_next tr)eqn:En.
     * eapply ore_reaches_step;[exact Hstep|]. exists 0;eexists;split;reflexivity.
     * destruct(t_dir tr)eqn:Ed;cbn[ctape_move chd ctl]in Hstep.
       -- destruct(ms_checked_blank tm Hb)as(z&Ez&Enz&Edz).
          assert(Hblank:cstep tm(StB,([],S0,t_write tr::r))=
           Some(StB,([t_write z],t_write tr,r))).
          {cbn[cstep];rewrite Ez,Enz,Edz;reflexivity. }
          eapply ore_reaches_step;[exact Hstep|].
          eapply ore_reaches_step;[exact Hblank|].
          eapply mt_trail_reaches;[exact Hp|exact Htrail| |].
          ++ eapply mt_checked_cell;eauto.
          ++ eapply ms_inv_step;[exact Hp| |exact Hblank]. eapply ms_inv_step;eauto.
       -- eapply ore_reaches_step;[exact Hstep|].
          eapply mt_trail_reaches;[exact Hp|exact Htrail| |].
          ++ eapply mt_checked_cell;eauto.
          ++ eapply ms_inv_step;eauto.
   + destruct(t_next tr)eqn:En.
     * eapply ore_reaches_step;[exact Hstep|]. exists 0;eexists;split;reflexivity.
     * destruct(t_dir tr)eqn:Ed;cbn[ctape_move chd ctl]in Hstep.
       -- eapply ore_reaches_step;[exact Hstep|]. apply IH. eapply ms_inv_step;eauto.
       -- eapply ore_reaches_step;[exact Hstep|].
          eapply mt_trail_reaches;[exact Hp|exact Htrail| |].
          ++ eapply mt_checked_cell;eauto.
          ++ eapply ms_inv_step;eauto.
Qed.

Theorem mt_check_sound : forall tm mask,
 mt_check tm mask=true -> NonHalt tm /\ QHBound 0 tm.
Proof.
 intros tm mask H;unfold mt_check in H;cbv zeta in H.
 repeat rewrite andb_true_iff in H. destruct H as[Hzero[Hp[Hb[Htrail Hother]]]].
 assert(Htotal:Total tm)by(eapply ms_preserve_total;exact Hp).
 assert(Hreach:forall cc,ms_inv(ms_mark mask)cc -> ore_reaches tm StA cc)
  by(eapply mt_reaches_A;eauto).
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
Definition mt_batch_check(rows:list(N*N)) :=
 forallb(fun '(packed,mask)=>mt_check(stp_machine packed)mask)rows.
Definition mt_board(rows:list(N*N)) := map(fun row=>stp_machine(fst row))rows.
Theorem mt_batch_state_sound : forall rows,
 mt_batch_check rows=true -> StateBoardSound 0(mt_board rows).
Proof.
 intros rows H family Hin tm Hle. apply in_map_iff in Hin as([packed mask]&<-&Hin).
 apply forallb_forall with(x:=(packed,mask))in H;[|exact Hin].
 destruct(mt_check_sound _ _ H)as[Hnh Hb]. eapply state_bound_extend;eauto.
Qed.
Theorem mt_batch_nonhalt : forall rows,
 mt_batch_check rows=true -> forall family,In family(mt_board rows)->NonHalt family.
Proof.
 intros rows H family Hin. apply in_map_iff in Hin as([packed mask]&<-&Hin).
 apply forallb_forall with(x:=(packed,mask))in H;[|exact Hin].
 exact(proj1(mt_check_sound _ _ H)).
Qed.
Print Assumptions mt_check_sound.
