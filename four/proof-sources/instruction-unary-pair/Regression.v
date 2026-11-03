From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement StatementTr Spec CTape Instructions.
From BBB24Burn23S004S005Unary Require Import UnaryPhases.
From BBB24InstructionUnaryPair Require Import UnaryInstructions.
Import ListNotations.

(** Both writes are covered, including the first nonempty block and all later
    blocks. *)
Example B2_write_zero_recurrent:forall N,exists k,N<=k /\ FiresAt(pu_tm false)(StB,S2)k.
Proof. apply pu_instructions_recurrent. Qed.
Example B2_write_two_recurrent:forall N,exists k,N<=k /\ FiresAt(pu_tm true)(StB,S2)k.
Proof. apply pu_instructions_recurrent. Qed.
Example A1_in_every_nonempty_block:forall bit n,exists d,
 csteps(pu_tm bit)11(pu_main(S n)[])=Some d /\ cinstr d=(StA,S1).
Proof. intros[]n;eexists;split;reflexivity. Qed.
Example no_instruction_attainment:forall bit B,~AttainsTr(pu_tm bit)B.
Proof.
 intros bit B(tg&s&[_ Hquiet]&_).
 destruct(pu_instructions_recurrent bit tg(S s))as(k&Hk&Hf).
 exact(Hquiet k ltac:(lia)Hf).
Qed.
