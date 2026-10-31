(** Reuse the proved ternary macro under six fixed transitions.  The sentinel
    isolates an arbitrary dormant suffix, including a suffix containing 3. *)
From Coq Require Import Arith Lia List NArith.
From BBB24 Require Import Statement StatementTr CTape Bounds.
From BBB24Burn4Ternary Require Import Counter Tail.
Import ListNotations.
Definition tt_agrees (tm:TM):Prop := forall q h,
 (q=StA \/ h=S1 \/ h=S2) -> tm q h=tc_tm q h.
Inductive tt_mark (L:list Sym):list Sym->Prop :=
 | tt_last:tt_mark L (S1::L)
 | tt_one:forall l,tt_mark L l->tt_mark L(S1::l)
 | tt_two:forall l,tt_mark L l->tt_mark L(S2::l).
Definition tt_inv L(c:cconf):Prop:=let '(q,(l,h,r)):=c in
 match q with StA=>tt_mark L l|StB=>tt_mark L(h::l)end.
Lemma tt_focus:forall L l,tt_mark L l->tt_mark L(chd l::ctl l).
Proof. intros L[|h l]H;[inversion H|exact H]. Qed.
Lemma tt_step:forall L c d,tt_inv L c->cstep tc_tm c=Some d->tt_inv L d.
Proof.
 intros L[q[[l h]r]]d H E;unfold tt_inv in H.
 destruct q,h;cbn[cstep tc_tm ctape_move]in E;injection E as <-;cbn[tt_inv].
 - apply tt_focus;exact H.
 - apply tt_focus;exact H.
 - apply tt_focus;exact H.
 - apply tt_two;exact H.
 - inversion H.
 - exact H.
 - inversion H;subst;apply tt_focus;assumption.
 - inversion H.
Qed.
Lemma tt_safe:forall L q l h r,tt_inv L(q,(l,h,r))->q=StA \/ h=S1 \/ h=S2.
Proof. intros L q l h r H;destruct q,h;cbn[tt_inv]in H;auto;inversion H. Qed.
Lemma tt_transfer:forall tm,tt_agrees tm->forall n L c d,
 tt_inv L c->csteps tc_tm n c=Some d->csteps tm n c=Some d /\ tt_inv L d.
Proof.
 intros tm Hag n;induction n;intros L c d H E;cbn[csteps]in *.
 - injection E as <-;auto.
 - assert(Hstep:cstep tm c=cstep tc_tm c).
   {destruct c as[q[[l h]r]];unfold cstep;rewrite Hag;[reflexivity|eapply tt_safe;exact H]. }
   rewrite Hstep. destruct(cstep tc_tm c)as[e|]eqn:HE;[|discriminate].
   apply(IHn L e d);[eapply tt_step;eauto|exact E].
Qed.
Lemma tt_after_inv:forall n L r,tt_inv L(tc_after n L r).
Proof. intros n L r;unfold tc_after,tc_front;cbn[tt_inv];induction n;cbn;constructor;auto. Qed.
Lemma tt_next:forall n L,
 csteps tc_tm(tc_gap n)(tc_after n L[])=Some(tc_after(S n)L[]).
Proof.
 intros n L;unfold tc_gap.
 change(csteps tc_tm(n+2+tc_work(S n))(tc_after n L[S0])=Some(tc_after(S n)L[])).
 rewrite csteps_add,(tc_bump n L[]S0 S1 eq_refl).
 replace(tc_first n L[S1])with(tc_first(S n)L[]).
 - apply tc_block.
 - unfold tc_first;rewrite tc_repeat;reflexivity.
Qed.
(** Each positive block visits all six active instructions. *)
Lemma tt_B1:forall n L r,
 csteps tc_tm n(tc_back StB(repeat S2 n++S1::L)r)=Some(StB,(L,S1,repeat S1 n++r)).
Proof.
 induction n;intros L r;[reflexivity|].
 cbn[repeat app tc_back csteps cstep tc_tm ctape_move chd ctl].
 change(csteps tc_tm n(tc_back StB(repeat S2 n++S1::L)(S1::r))=
 Some(StB,(L,S1,S1::(repeat S1 n++r)))).
 rewrite IHn,tc_repeat;reflexivity.
Qed.
Lemma tt_targets:forall n L tg,tg<>(StB,S0)->tg<>(StB,S3)->
 exists t d,csteps tc_tm t(tc_after(S n)L[])=Some d /\
 (fst d,let '(_,h,_) :=snd d in h)=tg.
Proof.
 intros n L[q h]H0 H3;change(tc_after(S n)L[])with(tc_after(S n)L[S0]);destruct q,h;
 try(exfalso;apply H0;reflexivity);try(exfalso;apply H3;reflexivity).
 - exists 0,(tc_after(S n)L[]);split;reflexivity.
 - exists(S n+2+tc_work n),(tc_after n L[S1;S1]);split;[|reflexivity].
   rewrite csteps_add,(tc_bump(S n)L[]S0 S1 eq_refl).
   replace(tc_first(S n)L[S1])with(tc_first n L[S1;S1]).
   + apply tc_block.
   + unfold tc_first;rewrite tc_repeat;reflexivity.
 - exists(S n+2+tc_work n+(n+2+tc_work n)),(tc_after n L[S2;S1]);split;[|reflexivity].
   rewrite csteps_add,csteps_add,(tc_bump(S n)L[]S0 S1 eq_refl).
   replace(tc_first(S n)L[S1])with(tc_first n L[S1;S1])by(unfold tc_first;rewrite tc_repeat;reflexivity).
   rewrite tc_block,csteps_add,(tc_bump n L[S1]S1 S2 eq_refl);apply tc_block.
 - exists(S n+2+tc_work n+(n+2+tc_work n)+(n+2+tc_work n)),(tc_after n L[S3;S1]);split;[|reflexivity].
   rewrite csteps_add,csteps_add,csteps_add,(tc_bump(S n)L[]S0 S1 eq_refl).
   replace(tc_first(S n)L[S1])with(tc_first n L[S1;S1])by(unfold tc_first;rewrite tc_repeat;reflexivity).
   rewrite tc_block,csteps_add,(tc_bump n L[S1]S1 S2 eq_refl),tc_block.
   rewrite csteps_add,(tc_bump n L[S1]S2 S3 eq_refl);apply tc_block.
 - exists(S(S n)),(StB,(L,S1,repeat S1(S n)++[S1]));split;[|reflexivity].
   change(csteps tc_tm(S n)(tc_back StB(repeat S2(S n)++S1::L)[S1])=Some(StB,(L,S1,repeat S1(S n)++[S1]))).
   apply tt_B1.
 - exists 1,(StB,(repeat S2 n++S1::L,S2,[S1]));split;reflexivity.
Qed.
Fixpoint tt_time entry start n:=match n with
 |0=>entry|S k=>tt_time entry start k+tc_gap(start+k)end.
Lemma tt_time_grows:forall n entry start,n<=tt_time entry start n.
Proof. induction n;intros;cbn[tt_time];[lia|pose proof(IHn entry start);pose proof(tc_gap_positive(start+n));lia]. Qed.
Section Entry.
Variable tm:TM.
Variable L:list Sym.
Variables entry start:nat.
Hypothesis agrees:tt_agrees tm.
Hypothesis entered:csteps tm entry c0=Some(tc_after start L[]).
Lemma tt_returns:forall n,csteps tm(tt_time entry start n)c0=Some(tc_after(start+n)L[]).
Proof.
 induction n;[now rewrite Nat.add_0_r|].
 cbn[tt_time];rewrite csteps_add,IHn.
 replace(start+S n)with(S(start+n))by lia.
 eapply(proj1(tt_transfer tm agrees _ L _ _ (tt_after_inv _ _ _) (tt_next _ _))).
Qed.
Lemma tt_recurrent:forall tg,tg<>(StB,S0)->tg<>(StB,S3)->
 forall N,exists k,N<=k /\ FiresAt tm tg k.
Proof.
 intros tg H0 H3 N.
 replace(start+S N)with(S(start+N))in * by lia.
 destruct(tt_targets(start+N)L tg H0 H3)as(t&d&Hrun&Htg).
 exists(tt_time entry start(S N)+t);split.
 - pose proof(tt_time_grows(S N)entry start);lia.
 - exists(lift d);split;[|destruct d as[q[[l h]r]];exact Htg].
   rewrite<-lift_c0;apply csteps_lift.
   rewrite csteps_add,tt_returns.
   replace(start+S N)with(S(start+N))by lia.
   exact(proj1(tt_transfer tm agrees _ L _ _ (tt_after_inv _ _ _) Hrun)).
Qed.
Lemma tt_nonhalt:NonHalt tm.
Proof.
 intros n Hnone.
 destruct(tt_recurrent(StA,S0)ltac:(discriminate)ltac:(discriminate)n)as(k&Hk&d&Hrun&_).
 replace k with(n+(k-n))in Hrun by lia;rewrite stepn_add,Hnone in Hrun;discriminate.
Qed.
Lemma tt_bad_quiet:forall h,h=S0 \/ h=S3->QuietFromTr tm(StB,h)entry.
Proof.
 intros h Hh n Hn(e&He&Hfire).
 destruct(tc_total(n-entry)(tc_after start L[]))as(d&Hd).
 destruct(tt_transfer tm agrees _ L _ _ (tt_after_inv _ _ _) Hd)as[Hrun Hinv].
 replace n with(entry+(n-entry))in He by lia.
 rewrite stepn_add,<-lift_c0,(csteps_lift _ _ _ _ entered),(csteps_lift _ _ _ _ Hrun)in He.
 injection He as <-.
 destruct d as[q[[l x]r]];destruct Hh as[->| ->];destruct q;cbn in Hfire;try discriminate;
 injection Hfire as ->;inversion Hinv.
Qed.
Theorem tt_bounds:Bounds 0%N (N.of_nat entry) tm.
Proof.
 unfold Bounds;rewrite Nat2N.id;cbn;split.
 - intros q s[Hv Hquiet].
   destruct(tt_recurrent(q,S1)ltac:(discriminate)ltac:(discriminate)(S s))as(k&Hk&Hfire).
   exfalso;apply(Hquiet k);[lia|eapply fires_visits;exact Hfire].
 - intros tg s[Hfire Hquiet].
   destruct(lt_dec s entry);[lia|].
   assert(Hcases:tg=(StB,S0) \/ tg=(StB,S3) \/ (tg<>(StB,S0) /\ tg<>(StB,S3))).
   {destruct tg as[q h];destruct q,h;intuition congruence. }
   destruct Hcases as[->|[->|[H0 H3]]].
   + exfalso;apply(tt_bad_quiet S0 ltac:(auto)s);[lia|exact Hfire].
   + exfalso;apply(tt_bad_quiet S3 ltac:(auto)s);[lia|exact Hfire].
   + destruct(tt_recurrent tg H0 H3(S s))as(k&Hk&Hfire').
     exfalso;apply(Hquiet k);[lia|exact Hfire'].
Qed.
End Entry.
Print Assumptions tt_bounds.
