(** A marker may turn left while remaining in B. Preservation and capacity
    suffice: a marked right move must exit to A, whereas a left move strictly
    decreases the padded finite-tape potential. This proves STATE bounds only. *)
From Coq Require Import List Arith Lia Bool Wf_nat NArith.
From BBB24 Require Import Statement Spec CTape Census TotalCompletion
  OneStateReach StatePipeline StateOnlyCloseout RightMarkerState MarkerState MarkerPotential.
Import ListNotations.

Definition rmp_cell (tm:TM)(mark:Sym->bool)(q:St)(h:Sym) :=
 match tm q h with
 |None=>false
 |Some tr=>if (st_eqb q StA && sym_eqb h S0)||mark h
           then ms_keeps mark tr else true
 end.
Definition rmp_preserve (tm:TM)(mark:Sym->bool) :=
 forallb(fun q=>forallb(rmp_cell tm mark q)ore_symbols)all_St.
Definition rmp_check (tm:TM)(mask:N)(w1 w2 w3:nat) :=
 let mark:=ms_mark mask in let weight:=mp_weights w1 w2 w3 in
 negb(mark S0) && (rmp_preserve tm mark && (ms_blank tm &&
 (mp_rank_check tm weight && ore_auto_goal tm StB))).

Lemma rmp_preserve_weaker : forall tm mark,
 ms_preserve tm mark=true -> rmp_preserve tm mark=true.
Proof.
 intros tm mark H. unfold ms_preserve in H. unfold rmp_preserve.
 apply forallb_forall;intros q Hq.
 apply forallb_forall with(x:=q)in H;[|exact Hq].
 apply forallb_forall;intros h Hh.
 apply forallb_forall with(x:=h)in H;[|exact Hh].
 unfold ms_cell in H. unfold rmp_cell.
 destruct(tm q h);[apply andb_true_iff in H;exact(proj1 H)|discriminate].
Qed.
Lemma rmp_check_extends_mp : forall tm mask w1 w2 w3,
 mp_check tm mask w1 w2 w3=true -> rmp_check tm mask w1 w2 w3=true.
Proof.
 intros tm mask w1 w2 w3 H. unfold mp_check in H;unfold rmp_check.
 cbv zeta in *. repeat rewrite andb_true_iff in *.
 destruct H as[Hz[Hp[Hb[Hr Ho]]]].
 repeat split;try assumption. apply rmp_preserve_weaker;exact Hp.
Qed.

Lemma rmp_checked_cell : forall tm mark q h,
 rmp_preserve tm mark=true -> exists tr,tm q h=Some tr /\
 (((q=StA /\ h=S0) \/ mark h=true) ->
  match t_dir tr with DL=>mark(t_write tr)=true |DR=>t_next tr=StA end).
Proof.
 intros tm mark q h H. unfold rmp_preserve in H.
 apply forallb_forall with(x:=q)in H;[|apply all_St_complete].
 apply forallb_forall with(x:=h)in H;[|apply ore_symbols_complete].
 unfold rmp_cell in H. destruct(tm q h)as[tr|]eqn:Et;[|discriminate].
 exists tr;split;[reflexivity|].
 intros Hguard. assert(G:((st_eqb q StA && sym_eqb h S0)||mark h)=true).
 {apply orb_true_iff. destruct Hguard as[[-> ->]|Hm];[left;reflexivity|right;exact Hm]. }
 rewrite G in H. unfold ms_keeps in H. destruct(t_dir tr);[exact H|].
 apply st_eqb_spec;exact H.
Qed.
Lemma rmp_preserve_total : forall tm mark,
 rmp_preserve tm mark=true -> Total tm.
Proof. intros tm mark H q h;destruct(rmp_checked_cell tm mark q h H)as(tr&Et&_);eauto. Qed.
Lemma rmp_inv_step : forall tm mark cc cc',
 rmp_preserve tm mark=true -> ms_inv mark cc -> cstep tm cc=Some cc' -> ms_inv mark cc'.
Proof.
 intros tm mark[q[[l h]r]]cc' Hp Hinv E.
 destruct(rmp_checked_cell tm mark q h Hp)as(tr&Et&Hkeep).
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
Lemma rmp_inv_steps : forall tm mark n cc cc',
 rmp_preserve tm mark=true -> ms_inv mark cc -> csteps tm n cc=Some cc' -> ms_inv mark cc'.
Proof.
 intros tm mark n;induction n;intros cc cc' Hp Hi E;cbn[csteps]in E.
 - inversion E;subst;exact Hi.
 - destruct(cstep tm cc)as[cm|]eqn:Es;[|discriminate].
   eapply IHn;[exact Hp|eapply rmp_inv_step;eauto|exact E].
Qed.

Lemma rmp_reaches_A : forall tm mark weight,
 weight S0=0 -> rmp_preserve tm mark=true -> mp_rank_check tm weight=true ->
 forall cc,ms_inv mark cc -> mp_capacity weight cc -> ore_reaches tm StA cc.
Proof.
 intros tm mark weight Hz Hp Hr.
 apply(well_founded_induction_type(well_founded_ltof cconf(mp_measure weight))
  (fun cc=>ms_inv mark cc -> mp_capacity weight cc -> ore_reaches tm StA cc)).
 intros[q[[l h]r]]IH Hi Hcap;destruct q.
 - exists 0,(StA,(l,h,r));split;reflexivity.
 - destruct(rmp_checked_cell tm mark StB h Hp)as(tr&Et&Hkeep).
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
          ++ unfold ltof,mp_measure,ore_mirror_cc. apply ore_right_drop;lia.
          ++ eapply rmp_inv_step;eauto.
          ++ exact Hcap'.
     * destruct r as[|b r];cbn[chd ctl]in Hstep,Hcap'.
       -- pose proof(ms_single mark h(ms_inv_B mark l h [] Hi))as Hm.
          specialize(Hkeep(or_intror Hm));congruence.
       -- eapply ore_reaches_step;[exact Hstep|]. apply IH.
          ++ unfold ltof,mp_measure,ore_mirror_cc.
             apply ore_left_drop. eapply mp_checked_bound;exact Hr.
          ++ eapply rmp_inv_step;eauto.
          ++ exact Hcap'.
Qed.

Theorem rmp_check_sound : forall tm mask w1 w2 w3,
 rmp_check tm mask w1 w2 w3=true -> NonHalt tm /\ QHBound 0 tm.
Proof.
 intros tm mask w1 w2 w3 H;unfold rmp_check in H;cbv zeta in H.
 repeat rewrite andb_true_iff in H. destruct H as[Hmark[Hp[Hb[Hr Hother]]]].
 assert(Htotal:Total tm)by(eapply rmp_preserve_total;exact Hp).
 set(weight:=mp_weights w1 w2 w3).
 assert(Hz:weight S0=0)by reflexivity.
 assert(Hrecur:forall goal N,exists n,N<=n /\ VisitsAt tm goal n).
 {intros goal N;destruct goal.
  - destruct(ore_total_csteps tm Htotal N c0)as(cc&Eprefix).
    assert(Hi:ms_inv(ms_mark mask)cc)by(eapply rmp_inv_steps;[exact Hp|apply ms_inv_initial|exact Eprefix]).
    set(padded:=mp_pad(S(mp_weight weight cc))cc).
    assert(Hpi:ms_inv(ms_mark mask)padded)by(apply mp_pad_inv;exact Hi).
    assert(Hpc:mp_capacity weight padded)by(apply mp_padded_capacity;exact Hz).
    destruct(rmp_reaches_A tm(ms_mark mask)weight Hz Hp Hr padded Hpi Hpc)as(k&cc'&Etail&Hstate).
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
Print Assumptions rmp_check_sound.
