(** State exchange is used only after a checked concrete entry, never as a
    symmetry of the blank A-start run. *)
From Coq Require Import Arith Lia List NArith.
From BBB24 Require Import Statement StatementTr CTape Bounds Shadow ReadySwap.
From BBB24Burn4Ternary Require Import Counter Tail.
From BBB24Burn4TernaryTemplate Require Import Template.
Import ListNotations.
Lemma ts_returns:forall n start L,
 csteps tc_tm(tt_time 0 start n)(tc_after start L[])=Some(tc_after(start+n)L[]).
Proof.
 induction n;intros start L;[rewrite Nat.add_0_r;reflexivity|].
 cbn[tt_time];rewrite csteps_add,IHn.
 replace(start+S n)with(S(start+n))by lia;apply tt_next.
Qed.
Section Entry.
Variable tm:TM.
Variable L:list Sym.
Variables entry start:nat.
Hypothesis agrees:tt_agrees(swap_tm tm).
Hypothesis entered:csteps tm entry c0=Some(ready_swap_cconf(tc_after start L[])).
Lemma ts_tail:forall k,
 stepn tm(entry+k)InitES=option_map swap_config(stepn tc_tm k(lift(tc_after start L[]))).
Proof.
 intro k;rewrite stepn_add,<-lift_c0,(csteps_lift _ _ _ _ entered).
 change(stepn tm k(swap_config(lift(tc_after start L[])))=option_map swap_config(stepn tc_tm k(lift(tc_after start L[])))).
 rewrite swap_stepn.
 destruct(tc_total k(tc_after start L[]))as(d&HD).
 rewrite(csteps_lift _ _ _ _ HD).
 rewrite(csteps_lift _ _ _ _ (proj1(tt_transfer(swap_tm tm)agrees _ L _ _ (tt_after_inv _ _ _) HD))).
 reflexivity.
Qed.
Lemma ts_recurrent:forall tg,tg<>(StB,S0)->tg<>(StB,S3)->
 forall N,exists k,N<=k /\ FiresAt tm(swap_instr tg)k.
Proof.
 intros tg H0 H3 N.
 destruct(tt_targets(start+N)L tg H0 H3)as(t&d&Hrun&Htg).
 exists(entry+(tt_time 0 start(S N)+t));split.
 - pose proof(tt_time_grows(S N)0 start);lia.
 - exists(swap_config(lift d));split.
   + rewrite ts_tail,stepn_add,(csteps_lift _ _ _ _ (ts_returns(S N)start L)).
     replace(start+S N)with(S(start+N))by lia.
     rewrite(csteps_lift _ _ _ _ Hrun);reflexivity.
   + rewrite swap_config_instr;f_equal;destruct d as[q[[l h]r]];exact Htg.
Qed.
Lemma ts_nonhalt:NonHalt tm.
Proof.
 intros n Hnone.
 destruct(ts_recurrent(StA,S0)ltac:(discriminate)ltac:(discriminate)n)as(k&Hk&d&Hrun&_).
 replace k with(n+(k-n))in Hrun by lia;rewrite stepn_add,Hnone in Hrun;discriminate.
Qed.
Lemma ts_bad_quiet:forall h,h=S0 \/ h=S3->QuietFromTr tm(StA,h)entry.
Proof.
 intros h Hh n Hn(e&He&Hfire).
 destruct(tc_total(n-entry)(tc_after start L[]))as(d&HD).
 pose proof(proj2(tt_transfer(swap_tm tm)agrees _ L _ _ (tt_after_inv _ _ _) HD))as Hinv.
 replace n with(entry+(n-entry))in He by lia.
 rewrite ts_tail,(csteps_lift _ _ _ _ HD)in He;injection He as <-.
 destruct d as[q[[l x]r]];destruct Hh as[->| ->];destruct q;cbn in Hfire;try discriminate;
 injection Hfire as ->;inversion Hinv.
Qed.
Theorem ts_bounds:Bounds 0%N(N.of_nat entry)tm.
Proof.
 unfold Bounds;rewrite Nat2N.id;cbn;split.
 - intros q s[Hv Hquiet].
   destruct(ts_recurrent(swap_state q,S1)ltac:(discriminate)ltac:(discriminate)(S s))as(k&Hk&Hfire).
   unfold swap_instr in Hfire;cbn in Hfire;rewrite swap_state_involutive in Hfire.
   exfalso;apply(Hquiet k);[lia|eapply fires_visits;exact Hfire].
 - intros tg s[Hfire Hquiet].
   destruct(lt_dec s entry);[lia|].
   assert(Hcases:tg=(StA,S0) \/ tg=(StA,S3) \/ (tg<>(StA,S0) /\ tg<>(StA,S3))).
   {destruct tg as[q h];destruct q,h;intuition congruence. }
   destruct Hcases as[->|[->|[H0 H3]]].
   + exfalso;apply(ts_bad_quiet S0 ltac:(auto)s);[lia|exact Hfire].
   + exfalso;apply(ts_bad_quiet S3 ltac:(auto)s);[lia|exact Hfire].
   + assert(H0':swap_instr tg<>(StB,S0)).
     {intro E;apply(f_equal swap_instr)in E;rewrite swap_instr_involutive in E;exact(H0 E). }
     assert(H3':swap_instr tg<>(StB,S3)).
     {intro E;apply(f_equal swap_instr)in E;rewrite swap_instr_involutive in E;exact(H3 E). }
     destruct(ts_recurrent(swap_instr tg)H0' H3'(S s))as(k&Hk&Hfire').
     rewrite swap_instr_involutive in Hfire'.
     exfalso;apply(Hquiet k);[lia|exact Hfire'].
Qed.
End Entry.
Print Assumptions ts_bounds.
