(** Reuse the paired-digit invariant and seven recurrence theorems after a
    concrete entry, allowing dormant cells beyond its permanent left marker. *)
From Coq Require Import Arith Lia List NArith.
From BBB24 Require Import Statement StatementTr CTape Bounds Shadow.
From BBB24Burn3Tail Require Import TailInvariant SevenTargets Closeout.
Import ListNotations.
Definition tp_pad L(c:cconf):cconf:=let '(q,(l,h,r)):=c in(q,(l++L,h,r)).
Definition tp_agrees(tm:TM):Prop:=forall q h,(q,h)<>(StB,S1)->tm q h=ti_tm q h.
Lemma tp_left_nonempty:forall n,ti_left n<>[].
Proof. intros n H;unfold ti_left in H;apply app_eq_nil in H;destruct H;discriminate. Qed.
Lemma tp_pad_nonempty:forall L q l h r,l<>[]->
 cstep ti_tm(tp_pad L(q,(l,h,r)))=option_map(tp_pad L)(cstep ti_tm(q,(l,h,r))).
Proof. intros L q[|x l]h r H;[contradiction|];destruct q,h;reflexivity. Qed.
Lemma tp_pad_step:forall L c,ti_inv c->
 cstep ti_tm(tp_pad L c)=option_map(tp_pad L)(cstep ti_tm c).
Proof.
 intros L c H;destruct H.
 - reflexivity.
 - apply tp_pad_nonempty;apply tp_left_nonempty.
 - apply tp_pad_nonempty;apply tp_left_nonempty.
 - apply tp_pad_nonempty;apply tp_left_nonempty.
 - apply tp_pad_nonempty;discriminate.
 - apply tp_pad_nonempty;apply tp_left_nonempty.
 - apply tp_pad_nonempty;apply tp_left_nonempty.
Qed.
Lemma tp_step_agrees:forall tm L c,tp_agrees tm->ti_inv c->
 cstep tm(tp_pad L c)=cstep ti_tm(tp_pad L c).
Proof.
 intros tm L[q[[l h]r]]Hag Hinv;unfold tp_pad,cstep.
 rewrite Hag;[reflexivity|exact(ti_inv_excludes_B1 _ Hinv)].
Qed.
Lemma tp_transfer:forall tm,tp_agrees tm->forall n L c d,
 ti_inv c->csteps ti_tm n c=Some d->csteps tm n(tp_pad L c)=Some(tp_pad L d).
Proof.
 intros tm Hag n;induction n;intros L c d Hinv E;cbn[csteps]in *.
 - injection E as <-;reflexivity.
 - rewrite(tp_step_agrees tm L c Hag Hinv),(tp_pad_step L c Hinv).
   destruct(cstep ti_tm c)as[e|]eqn:HE;[|discriminate].
   apply IHn;[eapply ti_inv_step;eauto|exact E].
Qed.
Definition tp_state(b:bool)q:=if b then swap_state q else q.
Definition tp_instr b(tg:Instr):Instr:=(tp_state b(fst tg),snd tg).
Definition tp_config b(c:ExecState):ExecState:=(tp_state b(fst c),snd c).
Definition tp_cconf b(c:cconf):cconf:=(tp_state b(fst c),snd c).
Definition tp_tm(b:bool)(tm:TM):TM:=if b then swap_tm tm else tm.
Lemma tp_state_involutive:forall b q,tp_state b(tp_state b q)=q.
Proof. intros[] [];reflexivity. Qed.
Lemma tp_instr_involutive:forall b tg,tp_instr b(tp_instr b tg)=tg.
Proof. intros[][[] h];reflexivity. Qed.
Lemma tp_config_instr:forall b c,instr_of(tp_config b c)=tp_instr b(instr_of c).
Proof. reflexivity. Qed.
Lemma tp_pad_instr:forall L c,instr_of(lift(tp_pad L c))=instr_of(lift c).
Proof. intros L[q[[l h]r]];reflexivity. Qed.
Lemma tp_stepn:forall b tm k c,
 stepn tm k(tp_config b c)=option_map(tp_config b)(stepn(tp_tm b tm)k c).
Proof.
 intros[]tm k[q tp];[apply swap_stepn|].
 unfold tp_tm,tp_config,tp_state;cbn[fst snd].
 destruct(stepn tm k(q,tp))as[[q' tp']|];reflexivity.
Qed.
Definition tp_entry_check tm entry b L c:=match csteps tm entry c0 with
 |Some d=>ceqb d(tp_cconf b(tp_pad L c))|None=>false end.
Lemma tp_entry_sound:forall tm entry b L c,tp_entry_check tm entry b L c=true->
 stepn tm entry InitES=Some(tp_config b(lift(tp_pad L c))).
Proof.
 intros tm entry b L c H;unfold tp_entry_check in H.
 destruct(csteps tm entry c0)as[d|]eqn:E;[|discriminate].
 apply ceqb_lift in H;rewrite<-lift_c0,(csteps_lift _ _ _ _ E),H.
 destruct c as[q[[l h]r]];reflexivity.
Qed.
Lemma tp_anchor_inv:forall anchor c,10<=anchor->csteps ti_tm anchor c0=Some c->ti_inv c.
Proof.
 intros anchor c Hle Hrun.
 replace anchor with(10+(anchor-10))in Hrun by lia.
 rewrite csteps_add,ti_prefix in Hrun.
 eapply(ti_inv_steps(anchor-10)(StB,(ti_left 2,S0,[]))c);[|exact Hrun].
 change(ti_inv(StB,(ti_left(2*1),S0,[])));constructor.
Qed.
Section Entry.
Variable tm:TM.
Variable b:bool.
Variable L:list Sym.
Variable source:cconf.
Variables entry anchor:nat.
Hypothesis agrees:tp_agrees(tp_tm b tm).
Hypothesis source_entry:csteps ti_tm anchor c0=Some source.
Hypothesis source_inv:ti_inv source.
Hypothesis entered:tp_entry_check tm entry b L source=true.
Lemma tp_tail:forall k d,csteps ti_tm k source=Some d->
 stepn tm(entry+k)InitES=Some(tp_config b(lift(tp_pad L d))).
Proof.
 intros k d Hd;rewrite stepn_add,(tp_entry_sound _ _ _ _ _ entered),tp_stepn.
 rewrite(csteps_lift _ _ _ _ (tp_transfer(tp_tm b tm)agrees k L source d source_inv Hd));reflexivity.
Qed.
Lemma tp_recurrent:forall tg,tg<>(StB,S1)->forall N,
 exists k,N<=k /\ FiresAt tm(tp_instr b tg)k.
Proof.
 intros tg Htg N.
 destruct(recurrent_except_B1 tg Htg(anchor+N))as(k&Hk&e&He&Hfire).
 destruct(ti_total(k-anchor)source)as(d&Hd).
 replace k with(anchor+(k-anchor))in He by lia.
 change(stepn ti_tm(anchor+(k-anchor))InitES=Some e)in He.
 rewrite stepn_add,<-lift_c0,(csteps_lift _ _ _ _ source_entry),(csteps_lift _ _ _ _ Hd)in He.
 injection He as <-.
 exists(entry+(k-anchor));split;[lia|].
 exists(tp_config b(lift(tp_pad L d)));split;[apply tp_tail;exact Hd|].
 now rewrite tp_config_instr,tp_pad_instr,Hfire.
Qed.
Lemma tp_nonhalt:NonHalt tm.
Proof.
 intros n Hnone;destruct(tp_recurrent(StA,S0)ltac:(discriminate)n)as(k&Hk&d&Hd&_).
 replace k with(n+(k-n))in Hd by lia;rewrite stepn_add,Hnone in Hd;discriminate.
Qed.
Lemma tp_bad_quiet:QuietFromTr tm(tp_instr b(StB,S1))entry.
Proof.
 intros n Hn(e&He&Hfire);destruct(ti_total(n-entry)source)as(d&Hd).
 replace n with(entry+(n-entry))in He by lia.
 rewrite(tp_tail _ _ Hd)in He;injection He as <-.
 rewrite tp_config_instr,tp_pad_instr in Hfire.
 apply(f_equal(tp_instr b))in Hfire;rewrite !tp_instr_involutive in Hfire.
 apply(ti_inv_excludes_B1 d(ti_inv_steps _ _ _ source_inv Hd)).
 destruct d as[q[[l h]r]];exact Hfire.
Qed.
Theorem tp_bounds:Bounds 0%N(N.of_nat entry)tm.
Proof.
 unfold Bounds;rewrite Nat2N.id;cbn;split.
 - intros q s[Hv Hquiet].
   destruct(tp_recurrent(tp_state b q,S0)ltac:(discriminate)(S s))as(k&Hk&Hfire).
   unfold tp_instr in Hfire;cbn[fst snd]in Hfire;rewrite tp_state_involutive in Hfire.
   exfalso;apply(Hquiet k);[lia|eapply fires_visits;exact Hfire].
 - intros tg s[Hfire Hquiet].
   destruct(instr_eqb tg(tp_instr b(StB,S1)))eqn:Etg.
   + apply instr_eqb_spec in Etg;subst tg.
     destruct(lt_dec s entry);[lia|].
     exfalso;apply(tp_bad_quiet s);[lia|exact Hfire].
   + assert(Hneq:tp_instr b tg<>(StB,S1)).
     {intro E;apply(f_equal(tp_instr b))in E;rewrite tp_instr_involutive in E.
      subst tg;assert(instr_eqb(tp_instr b(StB,S1))(tp_instr b(StB,S1))=true)by(apply instr_eqb_spec;reflexivity);congruence. }
     destruct(tp_recurrent(tp_instr b tg)Hneq(S s))as(k&Hk&Hfire').
     rewrite tp_instr_involutive in Hfire';exfalso;apply(Hquiet k);[lia|exact Hfire'].
Qed.
End Entry.
Print Assumptions tp_bounds.
