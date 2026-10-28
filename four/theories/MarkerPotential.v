(** Weighted-capacity extension of the state-only marker checker.

    Blank padding on the left preserves the denoted infinite tape. Reserve
    more left cells than the total symbol weight. A B-self right step adds
    at most one unit of weight; a left step removes at least one. The margin
    therefore stays positive, excluding a left-boundary escape. The marker
    excludes a right-boundary escape. On this fixed finite window the mirrored
    OneStateReach measure decreases, so B must reach A. *)
From Coq Require Import List Arith Lia Bool Wf_nat NArith.
From BBB24 Require Import Statement Spec CTape Census TotalCompletion OneStateReach
 StatePipeline StateOnlyCloseout MarkerState.
Import ListNotations.

Definition mp_weights (w1 w2 w3:nat)(h:Sym) := match h with
 |S0=>0 |S1=>w1 |S2=>w2 |S3=>w3 end.
Definition mp_cell (tm:TM)(weight:Sym->nat)(h:Sym) := match tm StB h with
 |None=>false |Some tr=>st_eqb(t_next tr)StA ||
 match t_dir tr with
 |DL=>S(weight(t_write tr))<=?weight h
 |DR=>weight(t_write tr)<=?S(weight h)
 end end.
Definition mp_rank_check tm weight :=
 forallb(fun h=>weight h<=?4)ore_symbols && forallb(mp_cell tm weight)ore_symbols.
Definition mp_check tm mask w1 w2 w3 :=
 let mark:=ms_mark mask in let weight:=mp_weights w1 w2 w3 in
 negb(mark S0) && (ms_preserve tm mark && (ms_blank tm &&
 (mp_rank_check tm weight && ore_auto_goal tm StB))).
Fixpoint mp_sum (weight:Sym->nat)(cells:list Sym) := match cells with
 |[]=>0 |h::r=>weight h+mp_sum weight r end.
Definition mp_weight weight(cc:cconf) := let '(_, (l,h,r)):=cc in
 mp_sum weight l+weight h+mp_sum weight r.
Definition mp_left_length(cc:cconf) := let '(_,(l,_,_)):=cc in length l.
Definition mp_capacity weight cc := mp_weight weight cc<mp_left_length cc.
Definition mp_measure weight cc := ore_measure weight(ore_mirror_cc cc).

Lemma mp_checked_bound : forall tm weight h,
 mp_rank_check tm weight=true -> weight h<=4.
Proof.
 intros tm weight h H;apply andb_prop in H as[H _].
 apply forallb_forall with(x:=h)in H;[apply Nat.leb_le;exact H|apply ore_symbols_complete].
Qed.
Lemma mp_checked_delta : forall tm weight h tr,
 mp_rank_check tm weight=true -> tm StB h=Some tr -> t_next tr=StB ->
 match t_dir tr with DL=>S(weight(t_write tr))<=weight h
 |DR=>weight(t_write tr)<=S(weight h) end.
Proof.
 intros tm weight h tr H Et En;apply andb_prop in H as[_ H].
 apply forallb_forall with(x:=h)in H;[|apply ore_symbols_complete].
 unfold mp_cell in H;rewrite Et,En in H.
 destruct(t_dir tr);apply Nat.leb_le;exact H.
Qed.
Lemma mp_weight_move : forall weight q q' l h r d w,
 weight S0=0 ->
 mp_weight weight(q',ctape_move d w(l,h,r))+weight h=
 mp_weight weight(q,(l,h,r))+weight w.
Proof.
 intros weight q q' l h r d w Hz.
 destruct d;[destruct l|destruct r];
 cbn[ctape_move mp_weight mp_sum chd ctl];rewrite ?Hz;lia.
Qed.
Lemma mp_capacity_move : forall weight q q' l h r d w,
 weight S0=0 -> mp_capacity weight(q,(l,h,r)) ->
 (match d with DL=>S(weight w)<=weight h |DR=>weight w<=S(weight h) end) ->
 mp_capacity weight(q',ctape_move d w(l,h,r)).
Proof.
 intros weight q q' l h r d w Hz Hcap Hd.
 pose proof(mp_weight_move weight q q' l h r d w Hz)as Hw.
 unfold mp_capacity in *.
 destruct d.
 - destruct l as[|a l];cbn[mp_left_length ctape_move chd ctl length]in *;lia.
 - cbn[mp_left_length ctape_move length]in *;lia.
Qed.
Lemma mp_reaches_A : forall tm mark weight,
 weight S0=0 -> ms_preserve tm mark=true -> mp_rank_check tm weight=true ->
 forall cc,ms_inv mark cc -> mp_capacity weight cc -> ore_reaches tm StA cc.
Proof.
 intros tm mark weight Hz Hp Hr.
 apply(well_founded_induction_type(well_founded_ltof cconf(mp_measure weight))
  (fun cc=>ms_inv mark cc -> mp_capacity weight cc -> ore_reaches tm StA cc)).
 intros[q[[l h]r]]IH Hi Hcap;destruct q.
 - exists 0,(StA,(l,h,r));split;reflexivity.
 - destruct(ms_checked_cell tm mark StB h Hp)as(tr&Et&Hkeep&Hexit).
   assert(Hstep:cstep tm(StB,(l,h,r))=Some(t_next tr,ctape_move(t_dir tr)(t_write tr)(l,h,r))).
   {cbn[cstep];rewrite Et;reflexivity. }
   destruct(t_next tr)eqn:En.
   + eapply ore_reaches_step;[exact Hstep|]. exists 0;eexists;split;reflexivity.
   + pose proof(mp_checked_delta tm weight h tr Hr Et En)as Hd.
     pose proof(mp_capacity_move weight StB StB l h r(t_dir tr)(t_write tr)Hz Hcap Hd)as Hcap'.
     destruct(t_dir tr)eqn:Ed;cbn[ctape_move]in Hstep,Hcap'.
     * destruct l as[|a l];cbn[chd ctl]in Hstep,Hcap'.
       -- unfold mp_capacity,mp_left_length in Hcap;cbn in Hcap;lia.
       -- eapply ore_reaches_step;[exact Hstep|]. apply IH.
          ++ unfold ltof,mp_measure,ore_mirror_cc.
             apply ore_right_drop;lia.
          ++ eapply ms_inv_step;eauto.
          ++ exact Hcap'.
     * destruct r as[|b r];cbn[chd ctl]in Hstep,Hcap'.
       -- pose proof(ms_single mark h(ms_inv_B mark l h [] Hi))as Hm.
          specialize(Hexit eq_refl Hm);congruence.
       -- eapply ore_reaches_step;[exact Hstep|]. apply IH.
          ++ unfold ltof,mp_measure,ore_mirror_cc.
             apply ore_left_drop. eapply mp_checked_bound;exact Hr.
          ++ eapply ms_inv_step;eauto.
          ++ exact Hcap'.
Qed.

Definition mp_pad n(cc:cconf) := let '(q,(l,h,r)):=cc in
 (q,(l++repeat S0 n,h,r)).
Lemma mp_padding_eqb : forall l n,lpad_eqb(l++repeat S0 n)l=true.
Proof.
 induction l as[|h l IH];intro n.
 - induction n;cbn[lpad_eqb repeat app];auto.
 - cbn[lpad_eqb app]. assert(Hh:sym_eqb h h=true)by(apply sym_eqb_spec;reflexivity).
   rewrite Hh,IH;reflexivity.
Qed.
Lemma mp_pad_lift : forall n cc,lift(mp_pad n cc)=lift cc.
Proof.
 intros n[q[[l h]r]]. unfold mp_pad, lift, lift_tape;cbn[fst snd].
 rewrite(lpad_eqb_lift _ _ (mp_padding_eqb l n));reflexivity.
Qed.
Lemma mp_pad_inv : forall mark n cc,ms_inv mark cc -> ms_inv mark(mp_pad n cc).
Proof. intros mark n[q[[l h]r]]H;exact H. Qed.
Lemma mp_sum_app : forall weight l r,mp_sum weight(l++r)=mp_sum weight l+mp_sum weight r.
Proof. intros weight l;induction l;intro r;cbn[mp_sum app];[reflexivity|rewrite IHl;lia]. Qed.
Lemma mp_sum_zeros : forall weight n,weight S0=0 -> mp_sum weight(repeat S0 n)=0.
Proof. intros weight n;induction n;intro H;cbn[mp_sum repeat];[reflexivity|rewrite H,IHn;auto]. Qed.
Lemma mp_padded_capacity : forall weight cc,
 weight S0=0 -> mp_capacity weight(mp_pad(S(mp_weight weight cc))cc).
Proof.
 intros weight[q[[l h]r]]Hz.
 unfold mp_capacity,mp_left_length;cbn[mp_pad mp_weight].
 rewrite mp_sum_app,mp_sum_zeros by exact Hz.
 rewrite app_length,repeat_length;cbn;lia.
Qed.

Theorem mp_check_sound : forall tm mask w1 w2 w3,
 mp_check tm mask w1 w2 w3=true -> NonHalt tm /\ QHBound 0 tm.
Proof.
 intros tm mask w1 w2 w3 H;unfold mp_check in H;cbv zeta in H.
 repeat rewrite andb_true_iff in H. destruct H as[Hmark[Hp[Hb[Hr Hother]]]].
 assert(Htotal:Total tm)by(eapply ms_preserve_total;exact Hp).
 set(weight:=mp_weights w1 w2 w3).
 assert(Hz:weight S0=0)by reflexivity.
 assert(Hrecur:forall goal N,exists n,N<=n /\ VisitsAt tm goal n).
 {intros goal N;destruct goal.
  - destruct(ore_total_csteps tm Htotal N c0)as(cc&Eprefix).
    assert(Hi:ms_inv(ms_mark mask)cc)by(eapply ms_inv_steps;[exact Hp|apply ms_inv_initial|exact Eprefix]).
    set(padded:=mp_pad(S(mp_weight weight cc))cc).
    assert(Hpi:ms_inv(ms_mark mask)padded)by(apply mp_pad_inv;exact Hi).
    assert(Hpc:mp_capacity weight padded)by(apply mp_padded_capacity;exact Hz).
    destruct(mp_reaches_A tm(ms_mark mask)weight Hz Hp Hr padded Hpi Hpc)as(k&cc'&Etail&Hstate).
    exists(N+k);split;[lia|]. exists(lift cc');split;[|exact Hstate].
    rewrite stepn_add.
    pose proof(csteps_lift tm N c0 cc Eprefix)as Hprefix.
    rewrite lift_c0 in Hprefix;rewrite Hprefix.
    pose proof(csteps_lift tm k padded cc' Etail)as Htail.
    unfold padded in Htail;rewrite mp_pad_lift in Htail;exact Htail.
  - apply(ore_reaches_recurs tm StB Htotal). apply ore_auto_goal_sound;exact Hother. }
 split;[apply ore_total_nonhalt;exact Htotal|].
 intros q s [_ Hquiet]. destruct(Hrecur q(S s))as(n&Hn&Hv).
 exfalso;apply(Hquiet n);[lia|exact Hv].
Qed.
Record MPRow := mkMPRow {
 mp_code : N; mp_mask : N; mp_w1 : N; mp_w2 : N; mp_w3 : N
}.
Definition mp_row_check row := mp_check(stp_machine(mp_code row))(mp_mask row)
 (N.to_nat(mp_w1 row))(N.to_nat(mp_w2 row))(N.to_nat(mp_w3 row)).
Definition mp_batch_check rows := forallb mp_row_check rows.
Definition mp_board rows := map(fun row=>stp_machine(mp_code row))rows.
Theorem mp_batch_state_sound : forall rows,
 mp_batch_check rows=true -> StateBoardSound 0(mp_board rows).
Proof.
 intros rows H family Hin tm Hle. apply in_map_iff in Hin as(row&<-&Hin).
 apply forallb_forall with(x:=row)in H;[|exact Hin].
 destruct(mp_check_sound _ _ _ _ _ H)as[Hnh Hb]. eapply state_bound_extend;eauto.
Qed.
Theorem mp_batch_nonhalt : forall rows,
 mp_batch_check rows=true -> forall family,In family(mp_board rows)->NonHalt family.
Proof.
 intros rows H family Hin. apply in_map_iff in Hin as(row&<-&Hin).
 apply forallb_forall with(x:=row)in H;[|exact Hin].
 exact(proj1(mp_check_sound _ _ _ _ _ H)).
Qed.
Print Assumptions mp_check_sound.
