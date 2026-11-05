(** The shared four-phase counter visits every instruction in each nonempty
    block.  The B2 write parameter is preserved throughout the proof. *)
From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement StatementTr Spec CTape Bounds Instructions.
From BBB24Burn23S004S005Unary Require Import UnaryPhases.
Import ListNotations.

Lemma pu_instruction_prefix : forall bit n tg, exists j d,
 csteps(pu_tm bit)j(pu_main(S n)[])=Some d /\ cinstr d=tg.
Proof.
 intros bit n[q h];destruct bit;destruct q,h;
 first [exists 2; eexists;split;reflexivity |
        exists 11; eexists;split;reflexivity |
        exists 7; eexists;split;reflexivity |
        exists 4; eexists;split;reflexivity |
        exists 0; eexists;split;reflexivity |
        exists 1; eexists;split;reflexivity |
        exists 5; eexists;split;reflexivity |
        exists 3; eexists;split;reflexivity].
Qed.

Lemma pu_positive_returns : forall bit N,exists k n,N<=k /\
 csteps(pu_tm bit)k c0=Some(pu_main(S n)[]).
Proof.
 intros bit N;destruct(pu_returns bit N)as(t&n&Ht&E).
 exists(t+(232*n+228)),(S n);split;[lia|].
 rewrite csteps_add,E,pu_cycle.
 replace(n+2)with(S(S n))by lia;reflexivity.
Qed.

Theorem pu_instructions_recurrent : forall bit tg N,exists k,
 N<=k /\ FiresAt(pu_tm bit)tg k.
Proof.
 intros bit tg N;destruct(pu_positive_returns bit N)as(t&n&Ht&E).
 destruct(pu_instruction_prefix bit n tg)as(j&d&Ed&Hd).
 exists(t+j);split;[lia|];exists(lift d);split.
 - rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;exact Ed.
 - rewrite cinstr_lift;exact Hd.
Qed.

Theorem pu_instruction_zero : forall bit,QHBoundTr 0(pu_tm bit).
Proof.
 intros bit tg s[_ Hquiet].
 destruct(pu_instructions_recurrent bit tg(S s))as(k&Hk&Hfire).
 exfalso;apply(Hquiet k);[lia|exact Hfire].
Qed.

Theorem pu_both_zero : forall bit,NonHalt(pu_tm bit) /\ Bounds 0%N 0%N(pu_tm bit).
Proof. intro bit;split;[apply pu_nonhalt|split;[apply pu_state_zero|apply pu_instruction_zero]]. Qed.
Print Assumptions pu_instruction_zero.
