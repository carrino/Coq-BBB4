From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement StatementTr Spec CTape Mirror CycleCensus Pipeline.
From BBB24Burn25S030Finite Require Import Counter BinaryBridge Trace Final.
From BBB24InstructionS030 Require Import InstructionTail Board.
Import ListNotations.

Example empty_exposed_word : csteps s30_tm 10(s30_back StB[][S2;S2])=
 Some(StB,([],S0,[S0;S0;S0;S0])).
Proof. reflexivity. Qed.
Example two_left_twos_before_escape : csteps s30_tm 19(s30_back StB[S2;S2][S2;S2])=
 Some(StB,([],S2,repeat S0 5)).
Proof. reflexivity. Qed.
Example two_left_twos_escape : csteps s30_tm 20(s30_back StB[S2;S2][S2;S2])=
 Some(StB,([],S0,repeat S0 6)).
Proof. reflexivity. Qed.
Example three_left_twos_escape : csteps s30_tm 25(s30_back StB[S2;S2;S2][S2;S2])=
 Some(StB,([],S0,repeat S0 7)).
Proof. reflexivity. Qed.
Example exact_last_instruction :
 QuietAfterTr s30_tm(StB,S2)(sf_count 1367361263048%N).
Proof. exact s30_last_instruction_B2. Qed.
Example predecessor_bound_rejected : ~QHBoundTr(sf_count 1367361263048%N)s30_tm.
Proof.
 intro H;pose proof(H(StB,S2)(sf_count 1367361263048%N)s30_last_instruction_B2)as Hb;lia.
Qed.
Example actual_B0_suffix : forall k,sf_count 1367361263049%N<=k->FiresAt s30_tm(StB,S0)k.
Proof. exact s30_instruction_B0_forever. Qed.
Example nonbinary_right_tail_can_return_to_A :
 csteps s30_tm 2(StB,([],S0,[S1]))=Some(StA,([S3;S2],S0,[])).
Proof. reflexivity. Qed.

Lemma s30_mirror_last : forall tg s,QuietAfterTr s30_tm tg s->QuietAfterTr(mirror_tm s30_tm)tg s.
Proof.
 intros tg s[Hf Hq];split.
 - apply mirror_fires;exact Hf.
 - intros n Hn Hf';apply(Hq n Hn);apply mirror_fires;exact Hf'.
Qed.
Example righthand_program : forall q s,mirror_tm s30_tm q s=
 machine_of_codes[7;10;6;11;9;12;3;2]q s.
Proof. intros q s;destruct q,s;reflexivity. Qed.
Example righthand_exact : AttainsTr(mirror_tm s30_tm)(sf_count 1367361263049%N)/\
 QHBoundTr(sf_count 1367361263049%N)(mirror_tm s30_tm).
Proof.
 split.
 - exists(StB,S2),(sf_count 1367361263048%N);split.
   + apply s30_mirror_last;exact s30_last_instruction_B2.
   + symmetry;exact s30_instruction_score_successor.
 - intros tg s[Hf Hq];apply(s30_instruction_bound tg s);split.
   + apply mirror_fires;exact Hf.
   + intros n Hn Hf';apply(Hq n Hn);apply mirror_fires;exact Hf'.
Qed.
Print Assumptions righthand_exact.
