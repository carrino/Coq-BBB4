(** Exact state and instruction scores of the known BBB(2,4) champion.
    This establishes lower bounds, not a global upper bound for BBB(2,4). *)
From Coq Require Import Arith Lia List NArith.
From BBB24 Require Import Statement StatementTr Spec CTape Gap Macros RLE Replay Certificate.
Import ListNotations.

Lemma score_succ : score = S previous_index.
Proof.
  unfold score,previous_index. rewrite <- N2Nat.inj_succ. reflexivity.
Qed.
Lemma initial_decode : decode initial = InitES.
Proof. exact lift_c0. Qed.
Lemma prefix_reach : stepn champion previous_index InitES = Some (decode previous).
Proof. rewrite <- initial_decode. exact (replay_sound _ _ _ _ certificate_checked). Qed.

Definition terminal := RC StB DL []
  [(S1,1%N);(S2,2%N);(S1,13%N);(S2,414095476532%N)].
Lemma final_step_checked : replay [Basic] previous = Some (1%N,terminal).
Proof. vm_compute. reflexivity. Qed.
Lemma landing_reach : stepn champion score InitES = Some (decode terminal).
Proof.
  rewrite score_succ. replace (S previous_index) with (previous_index+1) by lia.
  rewrite stepn_add,prefix_reach. exact (replay_sound _ _ _ _ final_step_checked).
Qed.

Lemma tail_run : forall k r,
  Runs champion k (leftward StB [] r)
    (leftward StB [] (repeat S0 k ++ r)).
Proof.
  intros k r. pose proof (chain_left champion StB S0 S0 k [] r eq_refl) as H.
  rewrite app_nil_r in H.
  assert (E: leftward StB (repeat S0 k) r = leftward StB [] r).
  { apply (gap_sides StB DL); [rewrite lift_repeat_blank,lift_side_nil|]; reflexivity. }
  now rewrite E in H.
Qed.
Lemma terminal_run : forall k, exists c,
  stepn champion k (decode terminal) = Some c /\
  fst c = StB /\ instr_of c = (StB,S0).
Proof.
  intro k. exists (leftward StB [] (repeat S0 k ++ expand (rr terminal))).
  split; [apply tail_run|]. split; reflexivity.
Qed.
Lemma after_landing : forall n, score <= n -> exists c,
  stepn champion n InitES = Some c /\ fst c = StB /\ instr_of c = (StB,S0).
Proof.
  intros n Hn. replace n with (score+(n-score)) by lia.
  rewrite stepn_add,landing_reach. apply terminal_run.
Qed.

Lemma previous_state : VisitsAt champion StA previous_index.
Proof. exists (decode previous); split; [exact prefix_reach|reflexivity]. Qed.
Lemma previous_instruction : FiresAt champion (StA,S3) previous_index.
Proof. exists (decode previous); split; [exact prefix_reach|reflexivity]. Qed.
Lemma champion_quiet_A : QuietAfter champion StA previous_index.
Proof.
  split; [exact previous_state|]. intros n Hn (c&Hc&Hs).
  destruct (after_landing n ltac:(rewrite score_succ; lia)) as (c'&Hc'&Hs'&Hi).
  rewrite Hc in Hc'; injection Hc' as <-. congruence.
Qed.
Lemma champion_quiet_A3 : QuietAfterTr champion (StA,S3) previous_index.
Proof.
  split; [exact previous_instruction|]. intros n Hn Hf.
  apply (proj2 champion_quiet_A n Hn). eapply fires_visits; exact Hf.
Qed.
Theorem champion_attains_state : AttainsSt champion score.
Proof. exists StA,previous_index; split; [exact champion_quiet_A|symmetry; exact score_succ]. Qed.
Theorem champion_attains_instruction : AttainsTr champion score.
Proof. exists (StA,S3),previous_index; split; [exact champion_quiet_A3|symmetry; exact score_succ]. Qed.

Theorem champion_state_bound : QHBound score champion.
Proof.
  intros q s [Hv Hquiet]. destruct (lt_dec s score); [lia|].
  destruct Hv as (c&Hc&Hq).
  destruct (after_landing s ltac:(lia)) as (cs&Hcs&Hqs&His).
  rewrite Hc in Hcs; injection Hcs as <-. subst q.
  destruct (after_landing (S s) ltac:(lia)) as (c'&Hc'&Hq'&Hi').
  exfalso. apply (Hquiet (S s)); [lia|]. exists c'; split; [assumption|congruence].
Qed.
Theorem champion_instruction_bound : QHBoundTr score champion.
Proof.
  intros tg s [Hf Hquiet]. destruct (lt_dec s score); [lia|].
  destruct Hf as (c&Hc&Hi).
  destruct (after_landing s ltac:(lia)) as (cs&Hcs&Hqs&His).
  rewrite Hc in Hcs; injection Hcs as <-. subst tg.
  destruct (after_landing (S s) ltac:(lia)) as (c'&Hc'&Hq'&Hi').
  exfalso. apply (Hquiet (S s)); [lia|]. exists c'; split; [assumption|congruence].
Qed.
Theorem champion_nonhalting : NonHalt champion.
Proof.
  intros n Hn. destruct (after_landing (Nat.max n score) (Nat.le_max_r _ _)) as (c&Hc&_).
  replace (Nat.max n score) with (n+(Nat.max n score-n)) in Hc by (pose proof (Nat.le_max_l n score); lia).
  rewrite stepn_add,Hn in Hc. discriminate.
Qed.

Theorem champion_exact : NonHalt champion /\
  (QHBound score champion /\ AttainsSt champion score) /\
  (QHBoundTr score champion /\ AttainsTr champion score).
Proof.
  repeat split; try exact champion_nonhalting; try exact champion_state_bound;
    try exact champion_instruction_bound; try exact champion_attains_state;
    try exact champion_attains_instruction.
Qed.
Theorem BBB24_lower_bounds : BBB24_state_lower_bound score /\ BBB24_instruction_lower_bound score.
Proof.
  split; exists champion; [exact champion_attains_state|exact champion_attains_instruction].
Qed.
Print Assumptions champion_exact.
Print Assumptions BBB24_lower_bounds.
