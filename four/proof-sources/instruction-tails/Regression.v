From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement StatementTr Spec CTape.
From BBB24 Require Import Mirror CycleCensus Pipeline.
From BBB24InstructionTails Require Import SingleInstruction FiniteTails Board.
Import ListNotations.

Lemma attained_excludes_smaller : forall tm a b,
 AttainsTr tm b -> a<b -> ~QHBoundTr a tm.
Proof.
 intros tm a b(tg&s&Hlast&HB)Hab Hbound.
 pose proof(Hbound tg s Hlast);lia.
Qed.

Example former_champion_exact_instruction_score :
 AttainsTr M.sc_tm(B.sf_count 67093892759901295%N) /\
 QHBoundTr(B.sf_count 67093892759901295%N)M.sc_tm.
Proof. split;[exact former_champion_instruction_attains|exact former_champion_instruction_bound]. Qed.
Example s57_exact_instruction_score :
 AttainsTr D.sd_tm(D.sd_count D.sd_stepsN) /\
 QHBoundTr(D.sd_count D.sd_stepsN)D.sd_tm.
Proof. split;[exact s57_instruction_attains|exact s57_instruction_bound]. Qed.
Example s77_exact_instruction_score :
 AttainsTr E.s77_tm(E.s77_count 2501552%N) /\
 QHBoundTr(E.s77_count 2501552%N)E.s77_tm.
Proof. split;[exact s77_instruction_attains|exact s77_instruction_bound]. Qed.

Example former_champion_predecessor_rejected :
 ~QHBoundTr(B.sf_count 67093892759901294%N)M.sc_tm.
Proof.
 eapply attained_excludes_smaller;[exact former_champion_instruction_attains|].
 rewrite F.sf_escape_successor;lia.
Qed.
Example s57_predecessor_rejected : ~QHBoundTr(D.sd_count D.sd_lastN)D.sd_tm.
Proof.
 eapply attained_excludes_smaller;[exact s57_instruction_attains|].
 rewrite D.sd_next_count;lia.
Qed.
Example s77_predecessor_rejected : ~QHBoundTr(E.s77_count 2501551%N)E.s77_tm.
Proof.
 eapply attained_excludes_smaller;[exact s77_instruction_attains|].
 rewrite E.s77_escape_successor;lia.
Qed.

Example blank_tail_is_essential :
 csteps D.sd_tm 2(StB,([],S0,[S1]))=Some(StA,([],S1,[S3])).
Proof. reflexivity. Qed.
Example a_nonzero_head_can_return_to_A :
 csteps D.sd_tm 1(StB,([],S1,[]))=Some(StA,([],S0,[S3])).
Proof. reflexivity. Qed.
Example arbitrary_explicit_blank_padding : forall t l r,all_blank r=true ->
 exists l' r',csteps D.sd_tm t(StB,(l,S0,r))=Some(StB,(l',S0,r')) /\all_blank r'=true.
Proof. exact D.sd_B_drift. Qed.

Lemma mirror_last_instruction : forall tm tg s,
 QuietAfterTr tm tg s -> QuietAfterTr(mirror_tm tm)tg s.
Proof.
 intros tm tg s[Hfire Hquiet];split.
 - apply mirror_fires;exact Hfire.
 - intros n Hn Hfire';apply(Hquiet n Hn);apply mirror_fires;exact Hfire'.
Qed.
Lemma mirror_instruction_exact : forall tm n,
 AttainsTr tm n /\QHBoundTr n tm ->
 AttainsTr(mirror_tm tm)n /\QHBoundTr n(mirror_tm tm).
Proof.
 intros tm n[(tg&s&Hlast&HB)Hbound];split.
 - exists tg,s;split;[apply mirror_last_instruction;exact Hlast|exact HB].
 - intros other last[Hfire Hquiet];apply(Hbound other last);split.
   + apply mirror_fires;exact Hfire.
   + intros k Hk Hfire';apply(Hquiet k Hk);apply mirror_fires;exact Hfire'.
Qed.
Example former_champion_righthand_exact :
 AttainsTr(mirror_tm M.sc_tm)(B.sf_count 67093892759901295%N) /\
 QHBoundTr(B.sf_count 67093892759901295%N)(mirror_tm M.sc_tm).
Proof. apply mirror_instruction_exact;exact former_champion_exact_instruction_score. Qed.
Example former_champion_righthand_table : forall q s,
 mirror_tm M.sc_tm q s=machine_of_codes[7;10;4;9;9;15;3;6]q s.
Proof. intros q s;destruct q,s;reflexivity. Qed.
Print Assumptions former_champion_predecessor_rejected.
