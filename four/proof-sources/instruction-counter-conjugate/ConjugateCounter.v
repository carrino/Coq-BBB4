(** Transport the erased-B0 counter suffix through state/symbol/mirror changes.
    The source run starts at a proved nonblank boundary, never at source blank. *)
From Coq Require Import List Arith Lia NArith FunctionalExtensionality.
From BBB24 Require Import Statement StatementTr Spec CTape Instructions Bounds Census
 Mirror Symmetry Shadow.
From BBB24SparseTwos Require Import TwosCounter.
Import ListNotations.

Lemma swap_forward_step:forall tm c,
 step(swap_tm tm)(swap_config c)=option_map swap_config(step tm c).
Proof.
 intros tm[q tp];unfold step,swap_tm,swap_config;cbn.
 rewrite swap_state_involutive.
 destruct(tm q(t_head tp))as[[w dr q']|];reflexivity.
Qed.
Lemma swap_forward_steps:forall tm n c,
 stepn(swap_tm tm)n(swap_config c)=option_map swap_config(stepn tm n c).
Proof.
 intros tm n;induction n;intro c;cbn[stepn];[reflexivity|].
 rewrite swap_forward_step;destruct(step tm c);cbn;[apply IHn|reflexivity].
Qed.
Definition phi(c:ExecState):ExecState:=mirror_es(perm_config P231(swap_config c)).
Definition phi_instr(tg:Instr):Instr:=perm_instr P231(swap_instr tg).
Definition unphi_instr(tg:Instr):Instr:=swap_instr(perm_instr P312 tg).
Definition transformed b0:=mirror_tm(perm_tm P231(swap_tm(tc_tm b0))).
Lemma transformed_run:forall b0 n c,
 stepn(transformed b0)n(phi c)=option_map phi(stepn(tc_tm b0)n c).
Proof.
 intros b0 n c;unfold transformed,phi.
 rewrite mirror_stepn,perm_stepn,swap_forward_steps.
 destruct(stepn(tc_tm b0)n c);reflexivity.
Qed.
Lemma phi_target:forall c,instr_of(phi c)=phi_instr(instr_of c).
Proof. intros[q tp];reflexivity. Qed.
Lemma phi_target_inverse:forall tg,phi_instr(unphi_instr tg)=tg.
Proof. intros[q h];destruct q,h;reflexivity. Qed.
Lemma phi_not_zero:forall tg,tg<>(StA,S0)->unphi_instr tg<>(StB,S0).
Proof. intros tg H E;apply H;apply(f_equal phi_instr)in E;rewrite phi_target_inverse in E;exact E. Qed.

Definition cb0:option Trans:=Some(mkTrans S3 DR StA).
Definition actual:=transformed cb0.
Lemma entry_three:stepn actual 3 InitES=Some(phi(lift(main 0 S1))).
Proof.
 rewrite <-lift_c0.
 replace(phi(lift(main 0 S1)))with(lift(StB,([],S2,[S2]))).
 - apply csteps_lift;reflexivity.
 - unfold phi,mirror_es,perm_config,swap_config,mirror_tape,perm_tape,
     lift,main,lift_tape,twos;cbn.
   f_equal;f_equal;apply functional_extensionality;intro n;unfold lift_side,nthb;destruct n;cbn;try reflexivity;destruct n;reflexivity.
Qed.

Lemma suffix_run:forall n,
 stepn actual(3+n)InitES=option_map phi(stepn(tc_tm cb0)n(lift(main 0 S1))).
Proof. intro n;rewrite stepn_add,entry_three;apply transformed_run. Qed.

Theorem seven_recurrent:forall tg,tg<>(StA,S0)->forall N,
 exists k,N<=k/\FiresAt actual tg k.
Proof.
 intros tg Hnot N.
 destruct(returns_from cb0 N)as(k&n&Hn&Hk&Ek).
 destruct(prefix_hits cb0 n Hn(unphi_instr tg)(phi_not_zero tg Hnot))as(j&d&Ej&Htarget).
 exists(3+(k+j));split;[lia|].
 exists(phi(lift d));split.
 - rewrite suffix_run.
   pose proof(csteps_lift(tc_tm cb0)(k+j)(main 0 S1)d)as E.
   rewrite csteps_add,Ek in E;specialize(E Ej);rewrite E;reflexivity.
 - rewrite phi_target,cinstr_lift,Htarget;apply phi_target_inverse.
Qed.

Lemma actual_nonhalt:NonHalt actual.
Proof.
 intros n Hnone.
 destruct(returns_from cb0 n)as(k&j&Hj&Hk&Ek).
 assert(E:stepn actual(3+k)InitES=Some(phi(lift(main j S1)))).
 { rewrite suffix_run,(csteps_lift(tc_tm cb0)k(main 0 S1)(main j S1)Ek);reflexivity. }
 destruct(stepn_prefix actual n(3+k)InitES(phi(lift(main j S1)))ltac:(lia)E)as(c&Ec&_);congruence.
Qed.

Lemma A0_quiet:forall n,3<=n->~FiresAt actual(StA,S0)n.
Proof.
 intros n Hn(c&Ec&Htarget);set(k:=n-3).
 destruct(every_from None k)as(d&Ed).
 assert(Hle:TM_le(tc_tm None)(tc_tm cb0)).
 { intros q h;destruct q,h;try(right;reflexivity);left;reflexivity. }
 pose proof(extend_steps(tc_tm None)(tc_tm cb0)k(lift(main 0 S1))(lift d)Hle
  (csteps_lift(tc_tm None)k(main 0 S1)d Ed))as Ea.
 replace n with(3+k)in Ec by(unfold k;lia).
 rewrite suffix_run,Ea in Ec;injection Ec as <-.
 rewrite phi_target,cinstr_lift in Htarget.
 assert(Hbad:cinstr d=(StB,S0)).
 {destruct d as[q[[l h]r]];destruct q,h;cbv in Htarget;cbv;congruence. }
 destruct(every_from None(S k))as(e&Ee).
 replace(S k)with(k+1)in Ee by lia;rewrite csteps_add,Ed in Ee.
 destruct d as[q[[l h]r]];destruct q,h;try discriminate Hbad.
 cbn[csteps cstep tc_tm]in Ee;discriminate.
Qed.

Theorem state_zero:QHBound 0 actual.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(seven_recurrent(StA,S2)ltac:(discriminate)(S s))as(k&Hk&Hfire).
   exfalso;apply(Hquiet k);[lia|eapply fires_visits;exact Hfire].
 - destruct(seven_recurrent(StB,S2)ltac:(discriminate)(S s))as(k&Hk&Hfire).
   exfalso;apply(Hquiet k);[lia|eapply fires_visits;exact Hfire].
Qed.
Lemma A0_quiet_one:forall n,1<=n->~FiresAt actual(StA,S0)n.
Proof.
 intros n Hn;destruct n as[|[|[|n]]];try lia.
 - intros(c&Ec&Htarget);vm_compute in Ec;injection Ec as <-;discriminate Htarget.
 - intros(c&Ec&Htarget);vm_compute in Ec;injection Ec as <-;discriminate Htarget.
 - apply A0_quiet;lia.
Qed.
Theorem instruction_bound:QHBoundTr 1 actual.
Proof.
 intros tg s[Hfire Hquiet];destruct(instr_eqb tg(StA,S0))eqn:Et.
 - apply instr_eqb_spec in Et;subst tg.
   destruct(lt_dec s 1);[lia|exfalso;exact(A0_quiet_one s ltac:(lia)Hfire)].
 - assert(Hnot:tg<>(StA,S0)).
   {intro E;subst tg;discriminate Et. }
   destruct(seven_recurrent tg Hnot(S s))as(k&Hk&Hf).
   exfalso;exact(Hquiet k ltac:(lia)Hf).
Qed.
Theorem instruction_attains:AttainsTr actual 1.
Proof.
 exists(StA,S0),0;split;[split|reflexivity].
 - eexists;split;reflexivity.
 - intros n Hn;apply A0_quiet_one;lia.
Qed.
Theorem family_run:NonHalt actual/\Bounds 0%N 1%N actual.
Proof. split;[exact actual_nonhalt|split;[exact state_zero|exact instruction_bound]]. Qed.
Print Assumptions family_run.
