(** An existential marker is required only during B episodes. Every A-to-B
    entry creates one by moving left and writing a marker. B-to-B steps
    preserve its existence on the head/right suffix. A-only steps are free.
    Padded capacity and the existing mirrored potential force return to A. *)
From Coq Require Import List Arith Lia Bool Wf_nat NArith.
From BBB24 Require Import Statement Spec CTape Census TotalCompletion
  OneStateReach StatePipeline StateOnlyCloseout MarkerState MarkerPotential.
Import ListNotations.

Definition em_has (mark:Sym->bool)(cells:list Sym) :=
 exists h,In h cells /\ mark h=true.
Definition em_inv (mark:Sym->bool)(cc:cconf) :=
 let '(q,(l,h,r)):=cc in match q with StA=>True |StB=>em_has mark(h::r) end.
Definition em_cell (tm:TM)(mark:Sym->bool)(q:St)(h:Sym) :=
 match tm q h with
 |None=>false
 |Some tr=>match t_next tr with
   |StA=>true
   |StB=>if st_eqb q StA || mark h then
      match t_dir tr with DL=>mark(t_write tr) |DR=>false end else true
   end
 end.
Definition em_preserve (tm:TM)(mark:Sym->bool) :=
 forallb(fun q=>forallb(em_cell tm mark q)ore_symbols)all_St.
Definition em_check (tm:TM)(mask:N)(w1 w2 w3:nat) :=
 let mark:=ms_mark mask in let weight:=mp_weights w1 w2 w3 in
 negb(mark S0) && (em_preserve tm mark &&
 (mp_rank_check tm weight && ore_auto_goal tm StB)).

Lemma em_checked_cell : forall tm mark q h,
 em_preserve tm mark=true -> exists tr,tm q h=Some tr /\
 (t_next tr=StB -> q=StA \/ mark h=true ->
  t_dir tr=DL /\ mark(t_write tr)=true).
Proof.
 intros tm mark q h H. unfold em_preserve in H.
 apply forallb_forall with(x:=q)in H;[|apply all_St_complete].
 apply forallb_forall with(x:=h)in H;[|apply ore_symbols_complete].
 unfold em_cell in H. destruct(tm q h)as[tr|]eqn:Et;[|discriminate].
 exists tr;split;[reflexivity|]. intros En Hg. rewrite En in H.
 assert(G:(st_eqb q StA || mark h)=true).
 {apply orb_true_iff. destruct Hg as[->|Hm];[left;reflexivity|right;exact Hm]. }
 rewrite G in H. destruct(t_dir tr)eqn:Ed;[split;[reflexivity|exact H]|discriminate].
Qed.
Lemma em_preserve_total : forall tm mark,
 em_preserve tm mark=true -> Total tm.
Proof. intros tm mark H q h;destruct(em_checked_cell tm mark q h H)as(tr&Et&_);eauto. Qed.
Lemma em_has_head : forall mark h r,mark h=true -> em_has mark(h::r).
Proof. intros mark h r H;exists h;split;[left;reflexivity|exact H]. Qed.
Lemma em_has_split : forall mark h r,
 em_has mark(h::r) -> mark h=true \/ em_has mark r.
Proof.
 intros mark h r(x&[Hx|Hin]&Hm).
 - subst x;left;exact Hm.
 - right;exists x;auto.
Qed.
Lemma em_has_right : forall mark r,
 em_has mark r -> em_has mark(chd r::ctl r).
Proof. intros mark[|h r]H;[destruct H as(x&H&_);contradiction|exact H]. Qed.
Lemma em_has_left : forall mark l w r,
 em_has mark r -> em_has mark(chd l::w::r).
Proof. intros mark l w r(x&Hin&Hm);exists x;split;[right;right;exact Hin|exact Hm]. Qed.
Lemma em_has_single : forall mark h,em_has mark[h] -> mark h=true.
Proof. intros mark h H;apply em_has_split in H as[H|(x&H&_)];[exact H|contradiction]. Qed.

Lemma em_inv_step : forall tm mark cc cc',
 em_preserve tm mark=true -> em_inv mark cc -> cstep tm cc=Some cc' -> em_inv mark cc'.
Proof.
 intros tm mark[q[[l h]r]]cc' Hp Hi E.
 destruct(em_checked_cell tm mark q h Hp)as(tr&Et&Hkeep).
 cbn[cstep]in E;rewrite Et in E;injection E as <-.
 destruct(t_next tr)eqn:En.
 - destruct(t_dir tr);exact I.
 - destruct q.
   + destruct(Hkeep eq_refl(or_introl eq_refl))as[Ed Hm]. rewrite Ed.
     unfold em_inv;cbn[ctape_move]. exists(t_write tr);split;[right;left;reflexivity|exact Hm].
   + change(em_has mark(h::r))in Hi. apply em_has_split in Hi as[Hm|Htail].
     * destruct(Hkeep eq_refl(or_intror Hm))as[Ed Hw]. rewrite Ed.
       unfold em_inv;cbn[ctape_move]. exists(t_write tr);split;[right;left;reflexivity|exact Hw].
     * destruct(t_dir tr);unfold em_inv;cbn[ctape_move].
       -- apply em_has_left;exact Htail.
       -- apply em_has_right;exact Htail.
Qed.
Lemma em_inv_initial : forall mark,em_inv mark c0.
Proof. intros;exact I. Qed.
Lemma em_inv_steps : forall tm mark n cc cc',
 em_preserve tm mark=true -> em_inv mark cc -> csteps tm n cc=Some cc' -> em_inv mark cc'.
Proof.
 intros tm mark n;induction n;intros cc cc' Hp Hi E;cbn[csteps]in E.
 - inversion E;subst;exact Hi.
 - destruct(cstep tm cc)as[cm|]eqn:Es;[|discriminate].
   eapply IHn;[exact Hp|eapply em_inv_step;eauto|exact E].
Qed.
Lemma em_pad_inv : forall mark n cc,em_inv mark cc -> em_inv mark(mp_pad n cc).
Proof. intros mark n[q[[l h]r]]H;exact H. Qed.

Lemma em_reaches_A : forall tm mark weight,
 weight S0=0 -> em_preserve tm mark=true -> mp_rank_check tm weight=true ->
 forall cc,em_inv mark cc -> mp_capacity weight cc -> ore_reaches tm StA cc.
Proof.
 intros tm mark weight Hz Hp Hr.
 apply(well_founded_induction_type(well_founded_ltof cconf(mp_measure weight))
  (fun cc=>em_inv mark cc -> mp_capacity weight cc -> ore_reaches tm StA cc)).
 intros[q[[l h]r]]IH Hi Hcap;destruct q.
 - exists 0,(StA,(l,h,r));split;reflexivity.
 - destruct(em_checked_cell tm mark StB h Hp)as(tr&Et&Hkeep).
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
          ++ eapply em_inv_step;eauto.
          ++ exact Hcap'.
     * destruct r as[|b r];cbn[chd ctl]in Hstep,Hcap'.
       -- pose proof(em_has_single mark h Hi)as Hm.
          destruct(Hkeep eq_refl(or_intror Hm))as[Hbad _];congruence.
       -- eapply ore_reaches_step;[exact Hstep|]. apply IH.
          ++ unfold ltof,mp_measure,ore_mirror_cc.
             apply ore_left_drop. eapply mp_checked_bound;exact Hr.
          ++ eapply em_inv_step;eauto.
          ++ exact Hcap'.
Qed.
Theorem em_check_sound : forall tm mask w1 w2 w3,
 em_check tm mask w1 w2 w3=true -> NonHalt tm /\ QHBound 0 tm.
Proof.
 intros tm mask w1 w2 w3 H;unfold em_check in H;cbv zeta in H.
 repeat rewrite andb_true_iff in H. destruct H as[Hmark[Hp[Hr Hother]]].
 assert(Htotal:Total tm)by(eapply em_preserve_total;exact Hp).
 set(weight:=mp_weights w1 w2 w3).
 assert(Hz:weight S0=0)by reflexivity.
 assert(Hrecur:forall goal N,exists n,N<=n /\ VisitsAt tm goal n).
 {intros goal N;destruct goal.
  - destruct(ore_total_csteps tm Htotal N c0)as(cc&Eprefix).
    assert(Hi:em_inv(ms_mark mask)cc)by(eapply em_inv_steps;[exact Hp|apply em_inv_initial|exact Eprefix]).
    set(padded:=mp_pad(S(mp_weight weight cc))cc).
    assert(Hpi:em_inv(ms_mark mask)padded)by(apply em_pad_inv;exact Hi).
    assert(Hpc:mp_capacity weight padded)by(apply mp_padded_capacity;exact Hz).
    destruct(em_reaches_A tm(ms_mark mask)weight Hz Hp Hr padded Hpi Hpc)as(k&cc'&Etail&Hstate).
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
Print Assumptions em_check_sound.
