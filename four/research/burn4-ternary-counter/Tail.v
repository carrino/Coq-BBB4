(** A permanent sentinel 1 keeps B from reading blank or 3 after step 4. *)
From Coq Require Import Arith Lia List.
From BBB24 Require Import Statement StatementTr CTape.
From BBB24Burn4Ternary Require Import Counter.
Import ListNotations.
Inductive tc_mark:list Sym->Prop:=
 |tc_mark_last:tc_mark[S1]
 |tc_mark_one:forall l,tc_mark l->tc_mark(S1::l)
 |tc_mark_two:forall l,tc_mark l->tc_mark(S2::l).
Definition tc_inv(c:cconf):Prop:=let '(q,(l,h,r)):=c in
 match q with StA=>tc_mark l|StB=>tc_mark(h::l)end.
Lemma tc_mark_focus:forall l,tc_mark l->tc_mark(chd l::ctl l).
Proof. intros[|h l]H;[inversion H|exact H]. Qed.
Lemma tc_inv_step:forall c d,tc_inv c->cstep tc_tm c=Some d->tc_inv d.
Proof.
 intros[q[[l h]r]]d H E;unfold tc_inv in H.
 destruct q,h;cbn[cstep tc_tm ctape_move]in E;injection E as <-;cbn[tc_inv].
 - apply tc_mark_focus;exact H.
 - apply tc_mark_focus;exact H.
 - apply tc_mark_focus;exact H.
 - apply tc_mark_two;exact H.
 - inversion H.
 - exact H.
 - inversion H;subst;apply tc_mark_focus;assumption.
 - inversion H.
Qed.
Lemma tc_inv_steps:forall n c d,tc_inv c->csteps tc_tm n c=Some d->tc_inv d.
Proof.
 induction n;intros c d H E;cbn[csteps]in E.
 - injection E as <-;exact H.
 - destruct(cstep tc_tm c)as[e|]eqn:HE;[|discriminate].
   eapply IHn;[eapply tc_inv_step;eauto|exact E].
Qed.
Lemma tc_inv_excludes:forall c h,tc_inv c->h=S0 \/ h=S3->
 (fst c,let '(_,x,_) := snd c in x)<>(StB,h).
Proof.
 intros[q[[l x]r]]h H[-> | ->];destruct q;cbn in *;intro E;try discriminate;
 injection E as ->;inversion H.
Qed.
Example tc_tail_entry:csteps tc_tm 4 c0=Some(StB,([S1],S2,[])).
Proof. reflexivity. Qed.
Lemma tc_total:forall n c,exists d,csteps tc_tm n c=Some d.
Proof.
 induction n;intro c;[eexists;reflexivity|].
 destruct c as[q[[l h]r]];destruct q,h;cbn[csteps cstep tc_tm];apply IHn.
Qed.
Theorem tc_bad_quiet:forall h,h=S0 \/ h=S3->QuietFromTr tc_tm(StB,h)4.
Proof.
 intros h Hh n Hn(e&He&Hfire).
 destruct(tc_total(n-4)(StB,([S1],S2,[])))as(d&Hd).
 assert(Hinv:tc_inv d).
 {eapply(tc_inv_steps(n-4)(StB,([S1],S2,[]))d);[unfold tc_inv;repeat constructor|exact Hd]. }
 replace n with(4+(n-4))in He by lia.
 rewrite stepn_add,<-lift_c0,(csteps_lift _ _ _ _ tc_tail_entry),(csteps_lift _ _ _ _ Hd)in He.
 injection He as <-;apply(tc_inv_excludes d h Hinv Hh).
 destruct d as[q[[l x]r]];exact Hfire.
Qed.
Theorem tc_B3_exact_last:QuietAfterTr tc_tm(StB,S3)3.
Proof.
 split.
 - eexists;split;[rewrite<-lift_c0;apply csteps_lift;reflexivity|reflexivity].
 - intros n Hn;apply(tc_bad_quiet S3 ltac:(auto));lia.
Qed.
Theorem tc_B0_prefix:FiresAt tc_tm(StB,S0)1.
Proof. eexists;split;[rewrite<-lift_c0;apply csteps_lift;reflexivity|reflexivity]. Qed.
Print Assumptions tc_bad_quiet.
