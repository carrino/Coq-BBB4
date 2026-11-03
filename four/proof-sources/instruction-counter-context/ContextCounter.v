(** The counter leaves an arbitrary tape context behind its left sentinel.
This extends the earlier empty-context macro without changing its source. *)
From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement StatementTr Spec CTape Instructions Bounds Census.
From BBB24SparseTwos Require Import TwosCounter.
Import ListNotations.
Section ContextCounter.
Variable b0:option Trans.
Variable context:list Sym.
Definition ctx_main n h:cconf:=(StA,(twos n++S1::context,h,[])).
Lemma start_one:forall n,
 csteps(tc_tm b0)(n+2)(ctx_main n S1)=Some(front(S3::context)(twos n++[S2])).
Proof.
 intro n;replace(n+2)with(1+(n+1))by lia;rewrite csteps_add.
 change(csteps(tc_tm b0)(n+1)(back(twos n++S1::context)[S2])=Some(front(S3::context)(twos n++[S2]))).
 rewrite csteps_add,(left_twos b0);reflexivity.
Qed.
Lemma start_zero:forall n,
 csteps(tc_tm b0)(n+2)(ctx_main n S0)=Some(front(S3::context)(twos n++[S1])).
Proof.
 intro n;replace(n+2)with(1+(n+1))by lia;rewrite csteps_add.
 change(csteps(tc_tm b0)(n+1)(back(twos n++S1::context)[S1])=Some(front(S3::context)(twos n++[S1]))).
 rewrite csteps_add,(left_twos b0);reflexivity.
Qed.
Definition phase_one n:=n+2+walk(S n)0.
Definition phase_zero n:=n+2+walk n 0.
Theorem one_phase:forall n,
 csteps(tc_tm b0)(phase_one n)(ctx_main n S1)=Some(ctx_main(S n)S0).
Proof.
 intro n;unfold phase_one;rewrite csteps_add,start_one,two_shift.
 change(csteps(tc_tm b0)(walk(S n)0)(front(S3::context)(twos(S n)++[]))=Some(ctx_main(S n)S0)).
 rewrite (scan_twos b0) by lia;reflexivity.
Qed.
Theorem zero_phase:forall n,
 csteps(tc_tm b0)(phase_zero(S n))(ctx_main(S n)S0)=Some(ctx_main(S n)S1).
Proof.
 intro n;unfold phase_zero;rewrite csteps_add,start_zero.
 rewrite (scan_twos b0) by lia;reflexivity.
Qed.
Definition gap n:=phase_one n+phase_zero(S n).
Lemma gap_formula:forall n,gap n+5=16*2^n.
Proof.
 intro n;pose proof(work_walk n);pose proof(work_walk(S n));pose proof(work_formula n).
 unfold gap,phase_one,phase_zero;rewrite walk_snoc;cbn[work Nat.add]in *;lia.
Qed.
Theorem main_next:forall n,
 csteps(tc_tm b0)(gap n)(ctx_main n S1)=Some(ctx_main(S n)S1).
Proof. intro n;unfold gap;rewrite csteps_add,one_phase;apply zero_phase. Qed.

Lemma ctx_returns_from:forall N,exists k n,1<=n/\N<=k/\
 csteps(tc_tm b0)k(ctx_main 0 S1)=Some(ctx_main n S1).
Proof.
 intro N;induction N as[|N IH].
 - exists(gap 0),1;repeat split;try lia;apply main_next.
 - destruct IH as(k&n&Hn&Hk&E);exists(k+gap n),(S n);repeat split;try lia.
   + unfold gap,phase_one,phase_zero;lia.
   + rewrite csteps_add,E;apply main_next.
Qed.
Lemma ctx_every_from:forall n,exists d,csteps(tc_tm b0)n(ctx_main 0 S1)=Some d.
Proof.
 intro n;destruct(ctx_returns_from n)as(k&j&Hj&Hk&E).
 destruct(csteps_prefix(tc_tm b0)n k(ctx_main 0 S1)(ctx_main j S1)Hk E)as(d&Ed&_).
 exists d;exact Ed.
Qed.
Lemma ctx_prefix_hits:forall n,1<=n->forall tg,tg<>(StB,S0)->exists j d,
 csteps(tc_tm b0)j(ctx_main n S1)=Some d/\cinstr d=tg.
Proof.
 intros n Hn[q h]Hnot;destruct q,h.
 - exists(phase_one n),(ctx_main(S n)S0);split;[apply one_phase|reflexivity].
 - exists 0;eexists;split;reflexivity.
 - exists(n+2);rewrite start_one;destruct n;[lia|];eexists;split;reflexivity.
 - exists(n+2+2);rewrite csteps_add,start_one;destruct n;[lia|];eexists;split;reflexivity.
 - contradiction.
 - exists(1+n);rewrite csteps_add.
   change(exists d,csteps(tc_tm b0)n(back(twos n++S1::context)[S2])=Some d/\cinstr d=(StB,S1)).
   rewrite (left_twos b0);eexists;split;reflexivity.
 - exists 1;destruct n;[lia|];eexists;split;reflexivity.
 - exists(n+2+1);rewrite csteps_add,start_one;destruct n;[lia|];eexists;split;reflexivity.
Qed.

End ContextCounter.
