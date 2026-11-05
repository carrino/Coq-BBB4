From Coq Require Import List Arith Lia Bool.
From SmallBB Require Import Statement CTape Bounds.
From SmallBB.Checkers Require Import Cycle.
From BBBWait Require Import Spec.
Import ListNotations.

Definition state_closed tm p := forallb (fun h=>match tm p h with
 |None=>true|Some tr=>st_eqb(t_next tr)p end) [S0;S1;S2].
Lemma closed_next : forall tm p, state_closed tm p=true -> forall h tr,
 tm p h=Some tr -> t_next tr=p.
Proof.
 intros tm p H h tr E;unfold state_closed in H;apply forallb_forall with(x:=h)in H.
 - rewrite E in H;now apply st_eqb_spec in H.
 - destruct h;cbn;auto.
Qed.
Lemma closed_run : forall tm p, state_closed tm p=true -> forall n c d,
 fst c=p -> csteps tm n c=Some d -> fst d=p.
Proof.
 intros tm p H n;induction n;intros [q[[l h]r]] d Hq E;cbn in Hq;subst q.
 - injection E as <-;reflexivity.
 - cbn[csteps cstep]in E;destruct(tm p h)as[tr|]eqn:Et;[|discriminate].
   eapply IHn in E;[exact E|cbn;exact(closed_next tm p H h tr Et)].
Qed.
Lemma blank_drift_right : forall tm p w,tm p S0=Some(mkTrans w DR p)->
 forall n l r,all_blank r=true->exists l' r',
 csteps tm n(p,(l,S0,r))=Some(p,(l',S0,r')).
Proof.
 intros tm p w H n;induction n;intros l r Hr.
 - exists l,r;reflexivity.
 - destruct r as[|h r].
   + cbn[csteps cstep ctape_move chd ctl];rewrite H;cbn;apply IHn;reflexivity.
   + cbn[all_blank]in Hr;apply andb_prop in Hr as[Hh Hr];apply sym_eqb_spec in Hh;subst h.
     cbn[csteps cstep ctape_move chd ctl];rewrite H;cbn;apply IHn;exact Hr.
Qed.
Lemma blank_drift_left : forall tm p w,tm p S0=Some(mkTrans w DL p)->
 forall n l r,all_blank l=true->exists l' r',
 csteps tm n(p,(l,S0,r))=Some(p,(l',S0,r')).
Proof.
 intros tm p w H n;induction n;intros l r Hl.
 - exists l,r;reflexivity.
 - destruct l as[|h l].
   + cbn[csteps cstep ctape_move chd ctl];rewrite H;cbn;apply IHn;reflexivity.
   + cbn[all_blank]in Hl;apply andb_prop in Hl as[Hh Hl];apply sym_eqb_spec in Hh;subst h.
     cbn[csteps cstep ctape_move chd ctl];rewrite H;cbn;apply IHn;exact Hl.
Qed.
Definition drift_check tm c := let '(p,(l,h,r)):=c in
 sym_eqb h S0 && match tm p S0 with
 |None=>true|Some tr=>st_eqb(t_next tr)p &&
   match t_dir tr with DL=>all_blank l|DR=>all_blank r end end.
Lemma drift_sound : forall tm c,drift_check tm c=true->forall n d,
 csteps tm n c=Some d->fst d=fst c.
Proof.
 intros tm[p[[l h]r]]H n d E;unfold drift_check in H.
 apply andb_prop in H as[Hh H];apply sym_eqb_spec in Hh;subst h.
 destruct(tm p S0)as[[w dr q]|]eqn:Et.
 - apply andb_prop in H as[Hq Hblank];apply st_eqb_spec in Hq;cbn in Hq;subst q.
   destruct dr.
   + destruct(blank_drift_left tm p w Et n l r Hblank)as(l'&r'&Er);rewrite Er in E;injection E as <-;reflexivity.
   + destruct(blank_drift_right tm p w Et n l r Hblank)as(l'&r'&Er);rewrite Er in E;injection E as <-;reflexivity.
 - destruct n;[injection E as <-;reflexivity|];cbn[csteps cstep]in E;rewrite Et in E;discriminate.
Qed.
(** A target with no incoming transition cannot be reached from another
    state. This also handles inactive states of smaller machines. *)
Definition no_entry tm q := forallb (fun p => forallb (fun h =>
  match tm p h with None => true | Some tr => negb (st_eqb (t_next tr) q) end)
  [S0; S1; S2]) all_St.
Lemma no_entry_next : forall tm q, no_entry tm q = true -> forall p h tr,
  tm p h = Some tr -> t_next tr <> q.
Proof.
  intros tm q H p h tr E.
  unfold no_entry in H.
  apply forallb_forall with (x := p) in H; [|apply all_St_complete].
  apply forallb_forall with (x := h) in H; [|destruct h; cbn; auto].
  rewrite E in H. intro Eq; rewrite Eq in H; destruct q; discriminate.
Qed.
Lemma no_entry_run : forall tm q, no_entry tm q = true -> forall n c d,
  fst c <> q -> csteps tm n c = Some d -> fst d <> q.
Proof.
  intros tm q H n; induction n; intros [p [[l h] r]] d Hneq E.
  - injection E as <-; exact Hneq.
  - cbn [csteps cstep] in E.
    destruct (tm p h) as [tr|] eqn:Et; [|discriminate].
    eapply IHn in E; [exact E|].
    cbn; eapply no_entry_next; eauto.
Qed.
Definition trap_check tm q c := negb (st_eqb (fst c) q) &&
  (no_entry tm q || state_closed tm (fst c) || drift_check tm c).
Lemma trap_sound : forall tm q c, trap_check tm q c = true -> forall n d,
  csteps tm n c = Some d -> fst d <> q.
Proof.
  intros tm q c H n d E.
  unfold trap_check in H; apply andb_prop in H as [Hneq H].
  assert (Hne : fst c <> q).
  { intro Eq; rewrite Eq in Hneq; destruct q; discriminate. }
  apply orb_prop in H as [H|H].
  - apply orb_prop in H as [H|H].
    + eapply no_entry_run; eauto.
    + rewrite (closed_run tm (fst c) H n c d eq_refl E); exact Hne.
  - rewrite (drift_sound tm c H n d E); exact Hne.
Qed.
Definition window_check tm B w q := match csteps tm B c0 with
 |None=>true|Some c=>cvisits tm c(S w)q ||
   match csteps tm w c with None=>true|Some d=>trap_check tm q d end end.
Lemma window_sound : forall tm B w q,window_check tm B w q=true->
 FutureBeep tm q B->BeepWindow tm q B w.
Proof.
 intros tm B w q H(t&Ht&Hv);destruct(visits_computable tm t q Hv)as(ct&Et&Hq).
 destruct(csteps_prefix tm B t c0 ct Ht Et)as(cb&Eb&Ebt).
 unfold window_check in H;rewrite Eb in H;apply orb_prop in H as[Hwin|Htail].
 - destruct(cvisits_sound tm(S w)cb q Hwin)as(i&ci&Hi&Ei&Hqi).
   exists(B+i);repeat split;try lia;exists(lift ci);split;[|exact Hqi].
   rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,Eb;exact Ei.
 - destruct(le_lt_dec t(B+w))as[Hle|Hlt].
   + exists t;auto.
   + destruct(csteps_prefix tm w(t-B)cb ct ltac:(lia)Ebt)as(d&Ed&Edt).
     rewrite Ed in Htail;exfalso;exact(trap_sound tm q d Htail(t-B-w)ct Edt Hq).
Qed.
Definition machine_check tm B w := forallb(window_check tm B w)all_St.
Lemma machine_sound : forall tm B w,machine_check tm B w=true->
 forall q,FutureBeep tm q B->BeepWindow tm q B w.
Proof.
 intros tm B w H q;apply window_sound;unfold machine_check in H.
 apply forallb_forall with(x:=q)in H;[exact H|apply all_St_complete].
Qed.
