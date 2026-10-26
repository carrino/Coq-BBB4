From Coq Require Import Arith Lia.
From SmallBB Require Import Statement StatementTr Size Bounds Spec Champions Census23State.

Theorem BBB23_state_value : BBBSt_is 2 3 59.
Proof.
 split.
 - exists champion23_state; split; [exact champion23_state_admissible|].
   exists StA,58; split; [exact champion23_state_quiet|reflexivity].
 - intros tm B Had (q & s & Hq & <-). exact (bbb23_state_upper tm Had q s Hq).
Qed.
Print Assumptions BBB23_state_value.
