From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement StatementTr Spec CTape Instructions.
From BBB24SparseTwos Require Import TwosCounter.
From BBB24CounterEntry Require Import ContextCounter CounterEntry.
Import ListNotations.
Example all_four_entries:forall w,
 csteps(rb_tm w)5 c0=Some(ctx_main[w]0 S1).
Proof. exact rb_entry_checked. Qed.
Example nonblank_left_context_is_preserved:forall b0,
 csteps(tc_tm b0)11(ctx_main[S3;S2;S1]0 S1)=Some(ctx_main[S3;S2;S1]1 S1).
Proof. intro b0;exact(ContextCounter.main_next b0[S3;S2;S1]0). Qed.
Example all_seven_return_after_each_prefix:forall w tg,tg<>(StB,S0)->forall N,
 exists k,N<=k/\FiresAt(rb_tm w)tg k.
Proof. intros;exact(entry_seven_recurrent(rb_b0 w)[w]5(rb_enters w)tg H N). Qed.
Example erased_blank_still_halts:csteps erased 2 c0=None.
Proof. reflexivity. Qed.
Example erased_context_suffix_does_not_halt:
 csteps erased 11(ctx_main[S1;S2;S3]0 S1)=Some(ctx_main[S1;S2;S3]1 S1).
Proof. exact(ContextCounter.main_next None[S1;S2;S3]0). Qed.
Example each_exact_score:forall w,AttainsTr(rb_tm w)2/\QHBoundTr 2(rb_tm w).
Proof. intro w;split;[apply rb_instruction_attains|apply rb_instruction_bound]. Qed.
Example bound_one_is_false:forall w,~QHBoundTr 1(rb_tm w).
Proof.
 intros w H;destruct(rb_instruction_attains w)as(tg&s&Hlast&E).
 pose proof(H tg s Hlast);lia.
Qed.
Print Assumptions each_exact_score.
