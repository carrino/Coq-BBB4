(** * The BBB(4) champion, boarded: 1RB1LD_1RC1RB_1LC1LA_0RC0RD

    [NonHalt /\ QHBound 32779478 /\ QuasiHaltsSt] -- the champion's own
    score, exactly, and the tightest bound its trajectory admits.

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
    left in [C] forever.  Measured last visits, from a 40M-step run
    (tools/counters/champion_probe.py --last):

      A: 32,769,237    B: 11,801,813    D: 32,779,477    C: never quiet

    so [StD]'s last visit at 32,779,477 IS the champion's score
    32,779,478, and no state's last visit exceeds it.  [QHBound
    32779478] is therefore exact, not slack: [qhbound_champion_tight]
    below shows [QHBound B] fails for every [B < 32779478].

    THE COST.  The prefix is 32,779,478 steps -- the reason
    docs/WAVE33_PROMPT.md deferred this row to "stable hardware".  It
    is affordable after all, because the fuel never has to become a
    unary [nat]: [TCyclerN.cstepsN] iterates on the BINARY numeral
    ([N.iter]), and [cstepsN_nat] is the bridge.  The whole run is
    ~9 s and a few hundred MB under [vm_compute].  The [nat] index
    [champ_score] is built in Horner digit form and related to its [N]
    twin by [N2Nat] congruences alone -- no large numeral is ever
    expanded.

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List NArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import TCyclerN.
From BBB4.Census Require Import TNF_QH.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB1LD_1RC1RB_1LC1LA_0RC0RD *)
Definition tm_champion : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StD
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S1 DL StC | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S0 DR StC | StD, S1 => mk S0 DR StD end.
Local Notation tm := tm_champion.

(** ** The score, in both numeral systems

    Horner digit form on the [nat] side: a bare literal this large is
    abstracted to [Nat.of_num_uint], which [lia] cannot see through
    (the same guard tools/closeout/gen_stages.py works around for
    [champion_score]).  The two are related by [N2Nat] congruences, so
    the 32.8M-element unary numeral is never built. *)

Definition champ_scoreN : N :=
  (((((((3 * 10 + 2) * 10 + 7) * 10 + 7) * 10 + 9) * 10 + 4) * 10 + 7) * 10 + 8)%N.

Definition champ_score : nat :=
  (((((((3 * 10 + 2) * 10 + 7) * 10 + 7) * 10 + 9) * 10 + 4) * 10 + 7) * 10 + 8)%nat.

Lemma champ_scoreN_nat : N.to_nat champ_scoreN = champ_score.
Proof.
  unfold champ_scoreN, champ_score. lia.
Qed.

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

Lemma prefix_reach : stepn tm champ_score InitES = Some (lift cEnd).
Proof.
  pose proof prefix_run_N as H.
  rewrite cstepsN_nat, champ_scoreN_nat in H.
  destruct (csteps tm champ_score c0) as [c|] eqn:Eq; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ Eq).
  f_equal. apply ceqb_lift. exact H.
Qed.

(** ** After the landing the state is always [StC] *)

Lemma after_stateC : forall n, champ_score <= n ->
  exists c, stepn tm n InitES = Some c /\ fst c = StC.
Proof.
  intros n Hn.
  replace n with (champ_score + (n - champ_score)) by lia.
  rewrite stepn_add, prefix_reach.
  destruct (tail_state (n - champ_score)) as (c & Hc & Hq).
  exists (lift c). split.
  - apply csteps_lift; exact Hc.
  - rewrite lift_state; exact Hq.
Qed.

Lemma visits_C : forall n, champ_score <= n -> VisitsAt tm StC n.
Proof. intros n Hn. exact (after_stateC n Hn). Qed.

Lemma not_visits_other : forall q n, q <> StC -> champ_score <= n ->
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
  destruct (Nat.le_gt_cases champ_score n) as [Hle | Hlt].
  - destruct (after_stateC n Hle) as (c & Hc & _). rewrite Hn in Hc. discriminate.
  - destruct (stepn_prefix tm n champ_score InitES (lift cEnd))
      as (cm & Hcm & _); [lia | exact prefix_reach |].
    rewrite Hn in Hcm. discriminate.
Qed.

Theorem quasihalts_champion : QuasiHaltsSt tm.
Proof.
  exists StA. split.
  - exists 0. exists InitES. split; reflexivity.
  - exists champ_score. intros n Hn.
    apply not_visits_other; [discriminate | exact Hn].
Qed.

Theorem qhbound_champion : QHBound champ_score tm.
Proof.
  intros q s (Hvis & Hquiet).
  destruct (st_eqb q StC) eqn:Eq.
  { apply st_eqb_spec in Eq; subst q.
    (* [StC] is never quiet: it is visited at every index past the landing. *)
    exfalso. apply (Hquiet (S (Nat.max s champ_score))); [lia|].
    apply visits_C. lia. }
  apply st_eqb_neq in Eq.
  (* every other state's last visit is before the landing *)
  destruct (Nat.le_gt_cases champ_score s) as [Hle | Hlt].
  - exfalso. exact (not_visits_other q s Eq Hle Hvis).
  - lia.
Qed.

(** The census tier predicate for a quasihalter, at the champion's own
    score.  [champ_score] is definitionally
    [Closeout.BBB4_Theorem.champion_score]. *)
Theorem champion_tier : NonHalt tm /\ QHBound champ_score tm /\ QuasiHaltsSt tm.
Proof.
  split; [exact nonhalt_champion | split;
    [exact qhbound_champion | exact quasihalts_champion]].
Qed.

(** ** The bound is exact -- recorded, not proved here

    [StD]'s last visit is at index 32,779,477 (measured:
    [python3 tools/counters/champion_probe.py --last]), so no [B] below
    32,779,478 bounds this machine and the score IS the champion's.
    Proving that in-file costs a SECOND 32.8M-step [vm_compute], which
    is not worth the build time for a fact the theorem above does not
    need -- [QHBound champ_score] is what the closeout consumes. *)
