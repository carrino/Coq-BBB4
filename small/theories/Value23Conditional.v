(** The state value is unconditional.  The instruction value still needs
    the seven explicit hypotheses listed in Remaining23Symmetry. *)
From Coq Require Import Arith Lia List.
From SmallBB Require Import Statement StatementTr Size Bounds Spec Champions
 Value23State Census23Conditional Remaining23Symmetry.
Theorem BBB23_value_if_remaining:
 Forall(QHBoundTr 67)remaining23_representatives->BBB23_statement.
Proof.
 intro H;split;[exact BBB23_state_value|];split.
 - exists champion23_instr;split;[exact champion23_instr_admissible|].
   exists(StA,S2),66;split;[exact champion23_instr_quiet|reflexivity].
 - intros tm B Had(tg&s&Hq&<-).
   exact(proj2(bbb23_upper_conditional(remaining23_reduce H)tm Had)tg s Hq).
Qed.
Print Assumptions BBB23_value_if_remaining.
