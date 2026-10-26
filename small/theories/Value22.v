From Coq Require Import Arith Lia.
From SmallBB Require Import Statement StatementTr Size Bounds Spec Champions Census22.

Theorem BBB22_value : BBB22_statement.
Proof.
  split; split.
  - exists champion22_state. split; [exact champion22_state_admissible|].
    exists StA, 5. split; [exact champion22_state_quiet|reflexivity].
  - intros tm B Had (q & s & Hq & <-). exact (proj1 (bbb22_upper tm Had) q s Hq).
  - exists champion22_instr. split; [exact champion22_instr_admissible|].
    exists (StA,S0), 7. split; [exact champion22_instr_quiet|reflexivity].
  - intros tm B Had (tg & s & Hq & <-). exact (proj2 (bbb22_upper tm Had) tg s Hq).
Qed.

Print Assumptions BBB22_value.
