From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement StatementTr Spec CTape Instructions.
From BBB24SparseTwos Require Import TwosCounter.
From BBB24ThreeCounter Require Import ThreeCounter ThreeEntry ConjugateThree.
Import ListNotations.
Example alternate_sentinel_entry:csteps three_tm 2 c0=Some(main3[]0 S1).
Proof. exact three_entry_checked. Qed.
Example alternate_sentinel_counts:forall b0 context,
 csteps(tc_tm b0)11(main3 context 0 S1)=Some(main3 context 1 S1).
Proof. intros;exact(ThreeCounter.main_next b0 context 0). Qed.
Example positive_block_restores_the_three_sentinel:forall b0 l r,
 csteps(tc_tm b0)7(at_two(S2::S3::l)r)=Some(front(S2::S2::S3::l)r).
Proof. intros;exact(three_block b0 1 ltac:(lia)l r). Qed.
Example zero_block_does_not_restore_the_three_sentinel:
 csteps three_tm 3(at_two[S3][])<>Some(front[S2;S3][]).
Proof. vm_compute;discriminate. Qed.
Example exact_direct_score:AttainsTr three_tm 2/\QHBoundTr 2 three_tm.
Proof. split;[exact three_instruction_attains|exact three_instruction_bound]. Qed.
Example direct_bound_one_is_false:~QHBoundTr 1 three_tm.
Proof.
 intro H;destruct three_instruction_attains as(tg&s&Hlast&E).
 pose proof(H tg s Hlast);lia.
Qed.
Print Assumptions exact_direct_score.
Example exact_conjugate_score:
 AttainsTr conjugate_three_tm 1/\QHBoundTr 1 conjugate_three_tm.
Proof. split;[exact conjugate_three_attains|exact ThreeConjugate.instruction_bound]. Qed.
Example conjugate_bound_zero_is_false:~QHBoundTr 0 conjugate_three_tm.
Proof.
 intro H;destruct conjugate_three_attains as(tg&s&Hlast&E).
 pose proof(H tg s Hlast);lia.
Qed.
Print Assumptions exact_conjugate_score.
