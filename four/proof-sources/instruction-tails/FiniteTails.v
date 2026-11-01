(** Instruction upgrades of four independently proved finite state tails.
    All original proof sources and prefix certificates are imported unchanged. *)
From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement StatementTr Spec CTape Census.
From BBB24InstructionTails Require Import SingleInstruction.
Require Import BBB24Burn21S057Drift.RightBlankDrift.
Require Import BBB24Burn19S077Finite.FinitePrefix.
Require Import BBB24Burn19FiniteCounter.Trace.
Require Import BBB24Burn21S032Finite.Final.
Import ListNotations.
Module D := BBB24Burn21S057Drift.RightBlankDrift.
Module E := BBB24Burn19S077Finite.FiniteEscape.
Module P := BBB24Burn19S077Finite.FinitePrefix.
Module C := BBB24Burn19FiniteCounter.FiniteCounter.
Module T := BBB24Burn19FiniteCounter.Trace.
Module M := BBB24Burn21S032Finite.CutMacros.
Module B := BBB24Burn21S032Finite.BinaryBridge.
Module R := BBB24Burn21S032Finite.Trace.
Module F := BBB24Burn21S032Finite.Final.

Lemma s57_tail : forall n,D.sd_count D.sd_stepsN<=n ->
 FiresAt D.sd_tm(StB,S0)n.
Proof.
 intros n Hn;destruct D.sd_prefix_result as(l&r&Ecut&Hblank).
 destruct(D.sd_B_drift(n-D.sd_count D.sd_stepsN)l r Hblank)as(l'&r'&Et&_).
 exists(lift(StB,(l',S0,r')));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift.
 replace n with(D.sd_count D.sd_stepsN+(n-D.sd_count D.sd_stepsN))by lia.
 rewrite csteps_add,Ecut;exact Et.
Qed.
Theorem s57_instruction_bound : QHBoundTr(D.sd_count D.sd_stepsN)D.sd_tm.
Proof. eapply single_instruction_tail_bound;exact s57_tail. Qed.
Theorem s57_instruction_attains : AttainsTr D.sd_tm(D.sd_count D.sd_stepsN).
Proof. apply state_attainment_instruction;exact D.sd_attains. Qed.

Lemma s77_tail : forall n,E.s77_count 2501552%N<=n ->
 FiresAt E.s77_tm(StB,S0)n.
Proof.
 intros n Hn;destruct(E.s77_endcheck_sound _ P.s77_escape_checked)as(l&r&Ecut&Hblank).
 destruct(E.s77_B_drift(n-E.s77_count 2501552%N)l r Hblank)as(l'&r'&Et&_).
 exists(lift(StB,(l',S0,r')));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift.
 replace n with(E.s77_count 2501552%N+(n-E.s77_count 2501552%N))by lia.
 rewrite csteps_add,Ecut;exact Et.
Qed.
Theorem s77_instruction_bound : QHBoundTr(E.s77_count 2501552%N)E.s77_tm.
Proof. eapply single_instruction_tail_bound;exact s77_tail. Qed.
Theorem s77_instruction_attains : AttainsTr E.s77_tm(E.s77_count 2501552%N).
Proof. apply state_attainment_instruction;exact P.s77_attains. Qed.

Lemma finite_counter_tail : forall n,C.fc_count 1012664081%N<=n ->
 FiresAt C.fc_tm(StB,S0)n.
Proof.
 intros n Hn;destruct(C.fc_after_run _ _ T.fc_native_prefix(n-C.fc_count 1012664081%N))
 as(l&k&Et).
 exists(lift(StB,(l,S0,repeat S0 k)));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift.
 replace n with(C.fc_count 1012664081%N+(n-C.fc_count 1012664081%N))by lia;exact Et.
Qed.
Theorem finite_counter_instruction_bound : QHBoundTr(C.fc_count 1012664081%N)C.fc_tm.
Proof. eapply single_instruction_tail_bound;exact finite_counter_tail. Qed.

Lemma former_champion_tail : forall n,B.sf_count 67093892759901295%N<=n ->
 FiresAt M.sc_tm(StB,S0)n.
Proof.
 intros n Hn.
 exists(lift(StB,(repeat S2(n-B.sf_count 67093892759901295%N)++
 (S2::repeat S1(B.sf_count 530843044%N)),S0,[])));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift.
 replace n with(B.sf_count 67093892759901295%N+(n-B.sf_count 67093892759901295%N))at 1 by lia.
 rewrite csteps_add,R.sf_escape;apply M.sc_blank_B_drift.
Qed.
Theorem former_champion_instruction_bound :
 QHBoundTr(B.sf_count 67093892759901295%N)M.sc_tm.
Proof. eapply single_instruction_tail_bound;exact former_champion_tail. Qed.
Theorem former_champion_instruction_attains :
 AttainsTr M.sc_tm(B.sf_count 67093892759901295%N).
Proof. apply state_attainment_instruction;exact F.sf_attains. Qed.

Print Assumptions former_champion_instruction_bound.
Print Assumptions former_champion_instruction_attains.
