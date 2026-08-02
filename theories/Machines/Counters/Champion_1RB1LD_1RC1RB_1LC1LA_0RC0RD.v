(** * The BBB(4) champion, boarded: 1RB1LD_1RC1RB_1LC1LA_0RC0RD

    [NonHalt /\ QHBound 32779478 /\ QuasiHaltsSt] -- the champion's own
    score, exactly, and the tightest bound its trajectory admits.  The
    machine table [tm_champion] and the score [champion_score] are the
    SPEC's (BBB4_Spec.v): this file proves facts about the very
    constants the final claim is stated with.

    THE READ, and why it is one [vm_compute] and two small inductions.

    mxdys' [Inductive] decider (busycoq BB6, [Inductive_inf], stock
    [default_config], T = 100000) decides this machine as NONHALT in
    seconds, and its top rule is

      {0inf >[A] 0inf} -->lb[n] {(1)^(n+10242) 0inf <[C] 0inf}

    -- for every [n], the blank tape reaches a configuration with at
    least [n] ones behind a LEFT-moving head in state [C], with blank
    tape ahead of it.  That is not a counter and not a bouncer: it is
    the machine's TERMINAL C-LOOP.  [tm StC S0 = 1LC] writes a one,
    steps left, and stays in [StC], so once the head is in [StC] with
    nothing but blanks to its left it never leaves [StC] again.

    Read off the raw simulator (tools/counters/champion_probe.py), the
    landing is even cleaner than the rule suggests:

      stepn 32779478 InitES  =  (StC, entirely blank tape)

    -- the machine erases its whole 10,239-cell working region and
    returns to a BLANK TAPE in state [C] at step 32,779,478, then spins
    left in [C] forever.  Measured last visits (configuration indices),
    from a 40M-step run (tools/counters/champion_probe.py --last):

      A: 32,769,237    B: 11,801,813    D: 32,779,477    C: never quiet

    so [StD]'s last visit at index 32,779,477 IS the champion's score
    32,779,478 (last-fire step, index + 1), and no state's last visit
    exceeds it.  [QHBound 32779478] is therefore exact, not slack:
    [qhbound_champion_tight] below shows [QHBound B] fails for every
    [B < 32779478].

    THE COST.  The prefix is 32,779,478 steps -- the reason
    docs/WAVE33_PROMPT.md deferred this row to "stable hardware".  It
    is affordable after all, because the fuel never has to become a
    unary [nat]: [TCyclerN.cstepsN] iterates on the BINARY numeral
    ([N.iter]), and [cstepsN_nat] is the bridge.  The whole run is
    ~9 s and a few hundred MB under [vm_compute].  On the [nat] side
    [champion_score] is [N.to_nat] of the same binary literal, and
    every arithmetic fact about it goes through [lia]'s constant
    handling -- the 32.8M-element unary numeral is never built.

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List NArith.
From BBB4 Require Import BBB4_Statement BBB4_Spec CTape.
From BBB4.Checkers Require Import TCyclerN.
From BBB4.Census Require Import TNF_QH.
Import ListNotations.

(** The table and the score are BBB4_Spec's. *)
Local Notation tm := tm_champion.

(** ** The score's binary twin -- the [vm_compute] fuel *)

Definition champ_scoreN : N := 32779478%N.

Lemma champ_scoreN_nat : N.to_nat champ_scoreN = champion_score.
Proof. reflexivity. Qed.

(** ** The terminal C-loop

    [tm StC S0 = Some (S1, DL, StC)]: write, step left, stay in [StC].
    With an empty (all-blank) left list the successor configuration has
    an empty left list again, so the shape is a fixed point of [cstep]
    and the state never changes. *)

Definition cEnd : cconf := (StC, ([], S0, [])).

Lemma tail_step : forall R, cstep tm (StC, ([], S0, R)) = Some (StC, ([], S0, S1 :: R)).
Proof. intro R. reflexivity. Qed.

Lemma rep1_snoc : forall k R, repeat S1 k ++ S1 :: R = repeat S1 (S k) ++ R.
Proof.
  induction k as [|k IH]; intro R; [reflexivity|].
  cbn [repeat app]. rewrite IH. reflexivity.
Qed.

Lemma tail_run : forall k R,
  csteps tm k (StC, ([], S0, R)) = Some (StC, ([], S0, repeat S1 k ++ R)).
Proof.
  induction k as [|k IH]; intro R; [reflexivity|].
  replace (S k) with (1 + k) by lia.
  rewrite csteps_add, csteps_1, tail_step, IH, rep1_snoc.
  reflexivity.
Qed.

Lemma tail_state : forall k, exists c,
  csteps tm k cEnd = Some c /\ fst c = StC.
Proof.
  intro k. unfold cEnd. rewrite (tail_run k []).
  eexists. split; [reflexivity | reflexivity].
Qed.

(** ** The prefix: 32,779,478 steps to the blank tape in state C

    [cstepsN] iterates [N.iter] on the binary numeral, so the fuel is
    ~25 machine words rather than 32.8M constructors.  The landing is
    compared with [ceqb], which is equality up to blank padding
    ([lpad_eqb]) -- the run leaves 10,240 blank cells in the left list
    and [lift] cannot tell them from the empty list. *)

Lemma prefix_run_N :
  match cstepsN tm champ_scoreN c0 with
  | Some c => ceqb c cEnd
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

Lemma prefix_reach : stepn tm champion_score InitES = Some (lift cEnd).
Proof.
  pose proof prefix_run_N as H.
  rewrite cstepsN_nat, champ_scoreN_nat in H.
  destruct (csteps tm champion_score c0) as [c|] eqn:Eq; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ Eq).
  f_equal. apply ceqb_lift. exact H.
Qed.

(** ** After the landing the state is always [StC] *)

Lemma after_stateC : forall n, champion_score <= n ->
  exists c, stepn tm n InitES = Some c /\ fst c = StC.
Proof.
  intros n Hn.
  replace n with (champion_score + (n - champion_score)) by lia.
  rewrite stepn_add, prefix_reach.
  destruct (tail_state (n - champion_score)) as (c & Hc & Hq).
  exists (lift c). split.
  - apply csteps_lift; exact Hc.
  - rewrite lift_state; exact Hq.
Qed.

Lemma visits_C : forall n, champion_score <= n -> VisitsAt tm StC n.
Proof. intros n Hn. exact (after_stateC n Hn). Qed.

Lemma not_visits_other : forall q n, q <> StC -> champion_score <= n ->
  ~ VisitsAt tm q n.
Proof.
  intros q n Hq Hn (c & Hc & Hfst).
  destruct (after_stateC n Hn) as (c' & Hc' & Hfst').
  rewrite Hc in Hc'. injection Hc' as <-. congruence.
Qed.

(** ** The three conclusions *)

Theorem nonhalt_champion : NonHalt tm.
Proof.
  intros n Hn.
  destruct (Nat.le_gt_cases champion_score n) as [Hle | Hlt].
  - destruct (after_stateC n Hle) as (c & Hc & _). rewrite Hn in Hc. discriminate.
  - destruct (stepn_prefix tm n champion_score InitES (lift cEnd))
      as (cm & Hcm & _); [lia | exact prefix_reach |].
    rewrite Hn in Hcm. discriminate.
Qed.

Theorem quasihalts_champion : QuasiHaltsSt tm.
Proof.
  exists StA. split.
  - exists 0. exists InitES. split; reflexivity.
  - exists champion_score. intros n Hn.
    apply not_visits_other; [discriminate | exact Hn].
Qed.

Theorem qhbound_champion : QHBound champion_score tm.
Proof.
  intros q s (Hvis & Hquiet).
  destruct (st_eqb q StC) eqn:Eq.
  { apply st_eqb_spec in Eq; subst q.
    (* [StC] is never quiet: it is visited at every index past the landing. *)
    exfalso. apply (Hquiet (S (Nat.max s champion_score))); [lia|].
    apply visits_C. lia. }
  apply st_eqb_neq in Eq.
  (* every other state's last visit is before the landing *)
  destruct (Nat.le_gt_cases champion_score s) as [Hle | Hlt].
  - exfalso. exact (not_visits_other q s Eq Hle Hvis).
  - lia.
Qed.

(** The census tier predicate for a quasihalter, at the champion's own
    score. *)
Theorem champion_tier : NonHalt tm /\ QHBound champion_score tm /\ QuasiHaltsSt tm.
Proof.
  split; [exact nonhalt_champion | split;
    [exact qhbound_champion | exact quasihalts_champion]].
Qed.

(** ** The closeout's entry point

    [champion_tier] restated under the name the closeout inventory scans
    for.  The other explicit-bound boards state [iqh_le B tm] with [B] a
    decimal literal; the champion cannot, because its bound is 32,779,478
    and a bare [nat] literal that large is left as [Nat.of_num_uint],
    which no [lia] sees through and no [vm_compute] should be asked to
    force.  So the bound rides in the DEFINITION -- [champion_score],
    [N.to_nat] of the binary literal -- and the generated stage
    discharges [champion_score <= B_champ] by [lia] on constants rather
    than by evaluating either side.  [kind = iqhch] in
    [tools/closeout/frozen_map.tsv]. *)
Definition iqh_champ (tm : TM) : Prop :=
  NonHalt tm /\ QHBound champion_score tm /\ QuasiHaltsSt tm.

Theorem iqh_champion : iqh_champ tm_champion.
Proof. exact champion_tier. Qed.

(** ** The bound is exact: [StD]'s last visit is at index 32,779,477

    A second [vm_compute] pins the configuration one step before the
    landing: after 32,779,477 steps the machine is in state [StD]
    (matching the measured last-visit table above).  Combined with
    [not_visits_other] -- no state but [StC] appears at or after the
    landing -- [StD]'s last visit is EXACTLY index 32,779,477, so:

    - [qhbound_champion_tight]: no [B < champion_score] satisfies
      [QHBound B tm] -- the bound the closeout consumes is not slack;
    - [champion_attains]: the champion [Attains] exactly
      [champion_score], the lower-bound package [Closeout/BBB4_Value.v]
      consumes for BBB(4) >= 32,779,478.

    Cost: one more ~9 s [vm_compute] over binary fuel, same shape as
    [prefix_run_N]. *)

Definition champ_prevN : N := 32779477%N.

Definition champ_prev : nat := N.to_nat champ_prevN.

Lemma champ_prevN_nat : N.to_nat champ_prevN = champ_prev.
Proof. reflexivity. Qed.

Lemma champ_prev_S : S champ_prev = champion_score.
Proof. unfold champ_prev, champ_prevN, champion_score. lia. Qed.

(** The machine is in [StD] one step before the landing. *)
Lemma prev_run_N :
  match cstepsN tm champ_prevN c0 with
  | Some c => st_eqb (fst c) StD
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

Lemma visits_D_prev : VisitsAt tm StD champ_prev.
Proof.
  pose proof prev_run_N as H.
  rewrite cstepsN_nat, champ_prevN_nat in H.
  destruct (csteps tm champ_prev c0) as [c|] eqn:Eq; [|discriminate].
  exists (lift c). split.
  - rewrite <- lift_c0. exact (csteps_lift _ _ _ _ Eq).
  - rewrite lift_state. apply st_eqb_spec. exact H.
Qed.

(** [StD] is visited at 32,779,477 and never afterwards: its last
    transition fires at step 32,779,478, the champion's score. *)
Theorem champion_quiet_after_D : QuietAfter tm StD champ_prev.
Proof.
  split; [exact visits_D_prev|].
  intros n Hn. apply not_visits_other; [discriminate|].
  rewrite <- champ_prev_S. exact Hn.
Qed.

(** No bound below the champion's own score bounds the champion. *)
Theorem qhbound_champion_tight : forall B, QHBound B tm -> champion_score <= B.
Proof.
  intros B H.
  rewrite <- champ_prev_S.
  exact (H StD champ_prev champion_quiet_after_D).
Qed.

(** The attained-score package, in the spec's own vocabulary: the
    champion [Attains] exactly [champion_score] -- the BBB(4) lower
    bound. *)
Theorem champion_attains : Attains tm_champion champion_score.
Proof.
  exists StD, champ_prev.
  split; [exact champion_quiet_after_D | exact champ_prev_S].
Qed.
