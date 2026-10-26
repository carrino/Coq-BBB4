From Coq Require Import Arith Lia.
From SmallBB Require Import Statement StatementTr Size Bounds Spec Champions Census32State.

Theorem BBB32_state_value : BBBSt_is 3 2 55.
Proof.
 split.
 - exists champion32; split; [exact champion32_admissible|].
   exists StB,54; split; [exact champion32_state_quiet|reflexivity].
 - intros tm B Had (q & s & Hq & <-). exact (bbb32_state_upper tm Had q s Hq).
Qed.
Print Assumptions BBB32_state_value.
