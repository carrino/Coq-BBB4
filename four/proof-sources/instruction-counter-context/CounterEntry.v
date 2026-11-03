(** Any finite entry into the symbolic counter inherits its seven recurrent
    instructions; only the parameterized B0 instruction can be transient. *)
From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement StatementTr Spec CTape Instructions Bounds Census.
From BBB24SparseTwos Require Import TwosCounter.
From BBB24CounterEntry Require Import ContextCounter.
Import ListNotations.

Section EntryTransport.
Variable b0:option Trans.
Variable context:list Sym.
Variable p:nat.
Hypothesis Hentry:stepn(tc_tm b0)p InitES=Some(lift(ctx_main context 0 S1)).

Lemma counter_returns:forall N,exists k n,1<=n/\N<=k/\
 stepn(tc_tm b0)k InitES=Some(lift(ctx_main context n S1)).
Proof.
 intro N;destruct(ctx_returns_from b0 context N)as(k&n&Hn&Hk&E).
 exists(p+k),n;repeat split;try lia.
 rewrite stepn_add,Hentry;apply csteps_lift;exact E.
Qed.

Theorem entry_seven_recurrent:forall tg,tg<>(StB,S0)->forall N,
 exists k,N<=k/\FiresAt(tc_tm b0)tg k.
Proof.
 intros tg Hnot N;destruct(counter_returns N)as(k&n&Hn&Hk&E).
 destruct(ctx_prefix_hits b0 context n Hn tg Hnot)as(j&d&Ehit&Htarget).
 exists(k+j);split;[lia|];exists(lift d);split.
 - rewrite stepn_add,E;apply csteps_lift;exact Ehit.
 - rewrite cinstr_lift;exact Htarget.
Qed.

Theorem entry_nonhalt:NonHalt(tc_tm b0).
Proof.
 intros n Hnone;destruct(counter_returns n)as(k&j&Hj&Hk&E).
 destruct(stepn_prefix(tc_tm b0)n k InitES(lift(ctx_main context j S1))Hk E)as(c&Ec&_).
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
 destruct(ctx_every_from None context k)as(d&Ed).
 pose proof(extend_steps erased(tc_tm b0)k(lift(ctx_main context 0 S1))(lift d)
   erased_extends_parameter(csteps_lift erased k(ctx_main context 0 S1)d Ed))as Ea.
 replace n with(p+k)in Eroot by(unfold k;lia).
 rewrite stepn_add,Hentry,Ea in Eroot;injection Eroot as <-.
 rewrite cinstr_lift in Htarget.
 destruct(ctx_every_from None context(S k))as(e&Ee).
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

(** All four right-moving B-state entries leave their write symbol behind
    the permanent sentinel. The symbolic counter never reads that context. *)
Definition rb_b0(w:Sym):=Some(mkTrans w DR StB).
Definition rb_tm(w:Sym):=tc_tm(rb_b0 w).
Example rb_entry_checked:forall w,
 csteps(rb_tm w)5 c0=Some(ctx_main[w]0 S1).
Proof. intro w;reflexivity. Qed.
Lemma rb_enters:forall w,stepn(rb_tm w)5 InitES=Some(lift(ctx_main[w]0 S1)).
Proof. intro w;rewrite <-lift_c0;apply csteps_lift;apply rb_entry_checked. Qed.
Lemma rb_B0_quiet:forall w n,2<=n->~FiresAt(rb_tm w)(StB,S0)n.
Proof.
 intros w n Hn;destruct(lt_dec n 5).
 - assert(n=2\/n=3\/n=4)by lia;destruct H as[E|[E|E]];subst n;
     intros(c&Ec&Et);cbn[rb_tm rb_b0 tc_tm stepn step InitES tape_move push_side tail_side]in Ec;
     injection Ec as <-;discriminate Et.
 - exact(entry_B0_quiet(rb_b0 w)[w]5(rb_enters w)n ltac:(lia)).
Qed.
Theorem rb_nonhalt:forall w,NonHalt(rb_tm w).
Proof. intro w;exact(entry_nonhalt(rb_b0 w)[w]5(rb_enters w)). Qed.
Theorem rb_state_bound:forall w,QHBound 0(rb_tm w).
Proof. intro w;exact(entry_state_zero(rb_b0 w)[w]5(rb_enters w)). Qed.
Theorem rb_instruction_bound:forall w,QHBoundTr 2(rb_tm w).
Proof.
 intro w;apply(entry_instruction_bound(rb_b0 w)[w]5(rb_enters w)2).
 intros s Hs Hfire;destruct(lt_dec s 2);[lia|].
 exfalso;exact(rb_B0_quiet w s ltac:(lia)Hfire).
Qed.
Theorem rb_instruction_attains:forall w,AttainsTr(rb_tm w)2.
Proof.
 intro w;exists(StB,S0),1;split;[split|reflexivity].
 - eexists;split;reflexivity.
 - intros n Hn;apply rb_B0_quiet;lia.
Qed.
Theorem rb_family_run:forall w,NonHalt(rb_tm w)/\Bounds 0%N 2%N(rb_tm w).
Proof. intro w;split;[exact(rb_nonhalt w)|split;[exact(rb_state_bound w)|exact(rb_instruction_bound w)]]. Qed.
Print Assumptions entry_instruction_bound.
Print Assumptions rb_family_run.
Print Assumptions rb_instruction_attains.
