(** Cheap, sound permanent-silence checks for instruction targets. *)
From Coq Require Import List Arith Lia Bool.
From SmallBB Require Import Statement StatementTr CTape ClosureTr Bounds.
From BBBWait Require Import SpecTr Checker.
Import ListNotations.

Lemma cfires_sound : forall tm len c tg,
 cfires tm c len tg=true -> exists i ci,
 i<len /\ csteps tm i c=Some ci /\ cinstr ci=tg.
Proof.
 intros tm len;induction len;intros c tg H;[discriminate|].
 cbn[cfires]in H;destruct(instr_eqb(cinstr c)tg)eqn:Ht.
 - exists 0,c;repeat split;try lia;now apply instr_eqb_spec in Ht.
 - destruct(cstep tm c)as[d|]eqn:E;[|discriminate].
   destruct(IHlen d tg H)as(i&ci&Hi&Ei&Hqi).
   exists(S i),ci;repeat split;try lia;try assumption;cbn[csteps];rewrite E;exact Ei.
Qed.
Lemma drift_instr_sound : forall tm c,drift_check tm c=true->forall n d,
 csteps tm n c=Some d->cinstr d=cinstr c.
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
Definition symbol_free a (l:list Sym) := forallb(fun h=>negb(sym_eqb h a))l.
Definition tape_free a (ct:ctape) := let '(l,h,r):=ct in
 symbol_free a l && negb(sym_eqb h a) && symbol_free a r.
Definition no_write tm a := forallb(fun p=>forallb(fun h=>match tm p h with
 None=>true|Some tr=>negb(sym_eqb(t_write tr)a)end)[S0;S1;S2])all_St.
Lemma no_write_next : forall tm a,no_write tm a=true->forall p h tr,
 tm p h=Some tr->negb(sym_eqb(t_write tr)a)=true.
Proof.
 intros tm a H p h tr E;unfold no_write in H.
 apply forallb_forall with(x:=p)in H;[|apply all_St_complete].
 apply forallb_forall with(x:=h)in H;[now rewrite E in H|destruct h;cbn;auto].
Qed.
Lemma symbol_free_tl : forall a l,symbol_free a l=true->symbol_free a(ctl l)=true.
Proof. intros a[|h l]H;[reflexivity|];unfold symbol_free in *;cbn in H;apply andb_prop in H;tauto. Qed.
Lemma symbol_free_hd : forall a l,negb(sym_eqb S0 a)=true->symbol_free a l=true->
 negb(sym_eqb(chd l)a)=true.
Proof. intros a[|h l]H0 H;[exact H0|];unfold symbol_free in H;cbn in H;apply andb_prop in H;tauto. Qed.
Lemma tape_free_move : forall a d w ct,negb(sym_eqb S0 a)=true->
 negb(sym_eqb w a)=true->tape_free a ct=true->tape_free a(ctape_move d w ct)=true.
Proof.
 intros a d w[[l h]r]H0 Hw H;unfold tape_free in H;apply andb_prop in H as[H Hright];apply andb_prop in H as[Hleft Hhead].
 destruct d;cbn[ctape_move tape_free].
 - apply andb_true_intro;split;[apply andb_true_intro;split|].
   + now apply symbol_free_tl.
   + now apply symbol_free_hd.
   + change(negb(sym_eqb w a)&&symbol_free a r=true);rewrite Hw,Hright;reflexivity.
 - apply andb_true_intro;split;[apply andb_true_intro;split|].
   + change(negb(sym_eqb w a)&&symbol_free a l=true);rewrite Hw,Hleft;reflexivity.
   + now apply symbol_free_hd.
   + now apply symbol_free_tl.
Qed.
Lemma symbol_free_run : forall tm a,no_write tm a=true->negb(sym_eqb S0 a)=true->
 forall n c d,tape_free a(snd c)=true->csteps tm n c=Some d->tape_free a(snd d)=true.
Proof.
 intros tm a Hwrite H0 n;induction n;intros[p[[l h]r]]d Hfree E.
 - injection E as <-;exact Hfree.
 - cbn[csteps cstep]in E;destruct(tm p h)as[tr|]eqn:Et;[|discriminate].
   eapply IHn in E;[exact E|];change(tape_free a(ctape_move(t_dir tr)(t_write tr)(l,h,r))=true);apply tape_free_move;[exact H0|eapply no_write_next;eauto|exact Hfree].
Qed.
Definition symbol_trap tm a(c:cconf) := negb(sym_eqb S0 a) && no_write tm a && tape_free a(snd c).
Lemma symbol_trap_sound : forall tm a c,symbol_trap tm a c=true->forall n d,
 csteps tm n c=Some d->snd(cinstr d)<>a.
Proof.
 intros tm a c H n[p[[l h]r]]E;unfold symbol_trap in H.
 apply andb_prop in H as[H Hfree];apply andb_prop in H as[H0 Hwrite].
 pose proof(symbol_free_run tm a Hwrite H0 n c(p,(l,h,r))Hfree E)as Hd.
 unfold tape_free in Hd;cbn in Hd;apply andb_prop in Hd as[Hd _];apply andb_prop in Hd as[_ Hd].
 cbn;intro Eq;subst h;destruct a;discriminate.
Qed.
Definition trap_tr_check tm tg c :=
 if trap_check tm(fst tg)c then true else
 if negb(instr_eqb(cinstr c)tg) && drift_check tm c then true else
 symbol_trap tm(snd tg)c.
Lemma trap_tr_sound : forall tm tg c,trap_tr_check tm tg c=true->forall n d,
 csteps tm n c=Some d->cinstr d<>tg.
Proof.
 intros tm tg c H n d E;unfold trap_tr_check in H.
 destruct(trap_check tm(fst tg)c)eqn:Hstate.
 - pose proof(trap_sound tm(fst tg)c Hstate n d E)as Hneq.
   intro Eq;apply Hneq;change(fst(cinstr d)=fst tg);now rewrite Eq.
 - destruct(negb(instr_eqb(cinstr c)tg)&&drift_check tm c)eqn:Hd.
   + apply andb_prop in Hd as[Hneq Hd];rewrite(drift_instr_sound tm c Hd n d E).
     intro Eq;rewrite Eq in Hneq;assert(instr_eqb tg tg=true)by(now apply instr_eqb_spec);rewrite H0 in Hneq;discriminate.
   + pose proof(symbol_trap_sound tm(snd tg)c H n d E)as Hneq.
     intro Eq;apply Hneq;now rewrite Eq.
Qed.
Definition window_tr_check tm B w tg := match csteps tm B c0 with
 |None=>true|Some c=>if cfires tm c(S w)tg then true else
   match csteps tm w c with None=>true|Some d=>trap_tr_check tm tg d end end.
Lemma window_tr_sound : forall tm B w tg,window_tr_check tm B w tg=true->
 FutureBeepTr tm tg B->BeepWindowTr tm tg B w.
Proof.
 intros tm B w tg H(t&Ht&Hv);destruct(fires_computable tm t tg Hv)as(ct&Et&Hq).
 destruct(csteps_prefix tm B t c0 ct Ht Et)as(cb&Eb&Ebt).
 unfold window_tr_check in H;rewrite Eb in H;destruct(cfires tm cb(S w)tg)eqn:Hwin.
 - destruct(cfires_sound tm(S w)cb tg Hwin)as(i&ci&Hi&Ei&Hqi).
   exists(B+i);repeat split;try lia;exists(lift ci);split;[|rewrite cinstr_lift;exact Hqi].
   rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,Eb;exact Ei.
 - destruct(le_lt_dec t(B+w))as[Hle|Hlt].
   + exists t;auto.
   + destruct(csteps_prefix tm w(t-B)cb ct ltac:(lia)Ebt)as(d&Ed&Edt).
     rewrite Ed in H;exfalso;exact(trap_tr_sound tm tg d H(t-B-w)ct Edt Hq).
Qed.
Definition machine_tr_check tm B w := forallb(window_tr_check tm B w)all_Instr.
Lemma machine_tr_sound : forall tm B w,machine_tr_check tm B w=true->
 forall tg,FutureBeepTr tm tg B->BeepWindowTr tm tg B w.
Proof.
 intros tm B w H tg;apply window_tr_sound;unfold machine_tr_check in H.
 apply forallb_forall with(x:=tg)in H;[exact H|apply all_Instr_complete].
Qed.
