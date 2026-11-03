(** Any finite entry into the symbolic counter inherits its seven recurrent
    instructions; only the parameterized B0 instruction can be transient. *)
From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement StatementTr Spec CTape Instructions Bounds Census.
From BBB24SparseTwos Require Import TwosCounter.
From BBB24ThreeCounter Require Import ThreeCounter.
Import ListNotations.

Section EntryTransport.
Variable b0:option Trans.
Variable context:list Sym.
Variable p:nat.
Hypothesis Hentry:stepn(tc_tm b0)p InitES=Some(lift(main3 context 0 S1)).

Lemma counter_returns:forall N,exists k n,1<=n/\N<=k/\
 stepn(tc_tm b0)k InitES=Some(lift(main3 context n S1)).
Proof.
 intro N;destruct(returns_from3 b0 context N)as(k&n&Hn&Hk&E).
 exists(p+k),n;repeat split;try lia.
 rewrite stepn_add,Hentry;apply csteps_lift;exact E.
Qed.

Theorem entry_seven_recurrent:forall tg,tg<>(StB,S0)->forall N,
 exists k,N<=k/\FiresAt(tc_tm b0)tg k.
Proof.
 intros tg Hnot N;destruct(counter_returns N)as(k&n&Hn&Hk&E).
 destruct(prefix_hits3 b0 context n Hn tg Hnot)as(j&d&Ehit&Htarget).
 exists(k+j);split;[lia|];exists(lift d);split.
 - rewrite stepn_add,E;apply csteps_lift;exact Ehit.
 - rewrite cinstr_lift;exact Htarget.
Qed.

Theorem entry_nonhalt:NonHalt(tc_tm b0).
Proof.
 intros n Hnone;destruct(counter_returns n)as(k&j&Hj&Hk&E).
 destruct(stepn_prefix(tc_tm b0)n k InitES(lift(main3 context j S1))Hk E)as(c&Ec&_).
 congruence.
Qed.

Theorem entry_state_zero:QHBound 0(tc_tm b0).
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(entry_seven_recurrent(StA,S1)ltac:(discriminate)(S s))as(k&Hk&Hfire).
   exfalso;apply(Hquiet k);[lia|eapply fires_visits;exact Hfire].
 - destruct(entry_seven_recurrent(StB,S1)ltac:(discriminate)(S s))as(k&Hk&Hfire).
   exfalso;apply(Hquiet k);[lia|eapply fires_visits;exact Hfire].
Qed.

Lemma erased_extends_parameter:TM_le erased(tc_tm b0).
Proof. intros q h;destruct q,h;try(right;reflexivity);left;reflexivity. Qed.

Theorem entry_B0_quiet:forall n,p<=n->~FiresAt(tc_tm b0)(StB,S0)n.
Proof.
 intros n Hn(c&Eroot&Htarget);set(k:=n-p).
 destruct(every_from3 None context k)as(d&Ed).
 pose proof(extend_steps erased(tc_tm b0)k(lift(main3 context 0 S1))(lift d)
   erased_extends_parameter(csteps_lift erased k(main3 context 0 S1)d Ed))as Ea.
 replace n with(p+k)in Eroot by(unfold k;lia).
 rewrite stepn_add,Hentry,Ea in Eroot;injection Eroot as <-.
 rewrite cinstr_lift in Htarget.
 destruct(every_from3 None context(S k))as(e&Ee).
 replace(S k)with(k+1)in Ee by lia;rewrite csteps_add,Ed in Ee.
 destruct d as[q[[l h]r]];destruct q,h;try discriminate Htarget.
 cbn[csteps cstep erased tc_tm]in Ee;discriminate.
Qed.

Theorem entry_instruction_bound:forall B,
 (forall s,s<p->FiresAt(tc_tm b0)(StB,S0)s->S s<=B)->QHBoundTr B(tc_tm b0).
Proof.
 intros B Hprefix tg s[Hfire Hquiet];destruct(instr_eqb tg(StB,S0))eqn:Et.
 - apply instr_eqb_spec in Et;subst tg.
   destruct(lt_dec s p);[apply Hprefix;assumption|].
   exfalso;exact(entry_B0_quiet s ltac:(lia)Hfire).
 - assert(Hnot:tg<>(StB,S0)).
   { intro E;subst tg;discriminate Et. }
   destruct(entry_seven_recurrent tg Hnot(S s))as(k&Hk&Hf).
   exfalso;exact(Hquiet k ltac:(lia)Hf).
Qed.
End EntryTransport.

Definition three_b0:=Some(mkTrans S3 DR StA).
Definition three_tm:=tc_tm three_b0.
Example three_entry_checked:csteps three_tm 2 c0=Some(main3[]0 S1).
Proof. reflexivity. Qed.
Lemma three_enters:stepn three_tm 2 InitES=Some(lift(main3[]0 S1)).
Proof. rewrite <-lift_c0;apply csteps_lift;exact three_entry_checked. Qed.
Theorem three_nonhalt:NonHalt three_tm.
Proof. exact(entry_nonhalt three_b0[]2 three_enters). Qed.
Theorem three_state_bound:QHBound 0 three_tm.
Proof. exact(entry_state_zero three_b0[]2 three_enters). Qed.
Theorem three_instruction_bound:QHBoundTr 2 three_tm.
Proof.
 apply(entry_instruction_bound three_b0[]2 three_enters 2).
 intros s Hs _;lia.
Qed.
Theorem three_instruction_attains:AttainsTr three_tm 2.
Proof.
 exists(StB,S0),1;split;[split|reflexivity].
 - eexists;split;reflexivity.
 - intros n Hn;exact(entry_B0_quiet three_b0[]2 three_enters n ltac:(lia)).
Qed.
Theorem three_family_run:NonHalt three_tm/\Bounds 0%N 2%N three_tm.
Proof. split;[exact three_nonhalt|split;[exact three_state_bound|exact three_instruction_bound]]. Qed.
Print Assumptions three_family_run.
Print Assumptions three_instruction_attains.
