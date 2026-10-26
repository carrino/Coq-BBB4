From Coq Require Import Arith Lia.
From SmallBB Require Import Statement StatementTr Size Bounds Spec Champions Census32 Value32State.
Theorem BBB32_value : BBB32_statement.
Proof.
 split; [exact BBB32_state_value|]. split.
 - exists champion32; split; [exact champion32_admissible|].
   exists (StB,S1),54; split; [exact champion32_instr_quiet|reflexivity].
 - intros tm B Had (tg & s & Hq & <-). exact (proj2(bbb32_upper tm Had)tg s Hq).
Qed.
Print Assumptions BBB32_value.
