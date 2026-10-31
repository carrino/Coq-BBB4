(** S071: excluding reachable literal B0/rightnil excludes every B-only
    right spinout, even when the physical CTape contains trailing blanks.
    This file does not establish its no-spinout premise. *)
From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn43S071FAR Require Import Programs Progress.
Import ListNotations.
Definition c49_no_spinout_from (entry:cconf) := forall n l,
 csteps s71_tm n entry<>Some(StB,(l,S0,[])).
Definition c49_no_spinout := c49_no_spinout_from c0.
Theorem c49_B0_drain : forall r,all_blank r=true->forall l,
 csteps s71_tm(length r)(StB,(l,S0,r))=
 Some(StB,(repeat S0(length r)++l,S0,[])).
Proof.
 induction r as[|h r IH];intros H l;[reflexivity|].
 destruct h;cbn[all_blank sym_eqb]in H;try discriminate.
 change(csteps s71_tm(length r)(StB,(S0::l,S0,r))=
 Some(StB,(S0::(repeat S0(length r)++l),S0,[]))).
 rewrite(IH H),s71_shift;reflexivity.
Qed.
Theorem c49_no_spinout_guard : forall entry,
 c49_no_spinout_from entry->s71_guard_from entry.
Proof.
 intros entry H n l r Ec;destruct(all_blank r)eqn:E;[|reflexivity].
 exfalso;apply(H(n+length r)(repeat S0(length r)++l)).
 rewrite csteps_add,Ec;now apply c49_B0_drain.
Qed.
Theorem c49_A_recurrent_from_no_spinout : c49_no_spinout->
 forall N,exists n,N<=n/\VisitsAt s71_tm StA n.
Proof.
 intro H;apply(s71_A_recurrent_from_guard c0 0 eq_refl).
 now apply c49_no_spinout_guard.
Qed.
Theorem c49_A_recurrent_after_no_spinout_entry : forall entry d,
 csteps s71_tm d c0=Some entry->c49_no_spinout_from entry->
 forall N,exists n,N<=n/\VisitsAt s71_tm StA n.
Proof.
 intros entry d Ed H;apply(s71_A_recurrent_from_guard entry d Ed).
 now apply c49_no_spinout_guard.
Qed.
Theorem c49_zero_from_A_recurrent :
 (forall N,exists n,N<=n/\VisitsAt s71_tm StA n)->QHBound 0 s71_tm.
Proof.
 intros HA q s[Hv Hquiet];exfalso;destruct q.
 - destruct(HA(S s))as(k&Hk&Hv');apply(Hquiet k);[lia|exact Hv'].
 - destruct(s71_B_recurrent(S s))as(k&Hk&Hv');apply(Hquiet k);[lia|exact Hv'].
Qed.
Theorem c49_zero_from_no_spinout : c49_no_spinout->QHBound 0 s71_tm.
Proof.
 intro H;apply c49_zero_from_A_recurrent.
 now apply c49_A_recurrent_from_no_spinout.
Qed.
Theorem c49_zero_after_no_spinout_entry : forall entry d,
 csteps s71_tm d c0=Some entry->c49_no_spinout_from entry->QHBound 0 s71_tm.
Proof.
 intros entry d Ed H;apply c49_zero_from_A_recurrent.
 now apply(c49_A_recurrent_after_no_spinout_entry entry d Ed).
Qed.
Print Assumptions c49_B0_drain.
Print Assumptions c49_no_spinout_guard.
Print Assumptions c49_A_recurrent_from_no_spinout.
Print Assumptions c49_zero_from_A_recurrent.
Print Assumptions c49_zero_from_no_spinout.
