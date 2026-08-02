(** * BBB4_Value: BBB(4) = 32,779,478.

    The end of the story.  Hand-written (NOT generated -- gen_stages.py
    emits [bbb4_target] with the [skipped D_remaining] disjunct whatever
    the residue is; this file is where the disjunct dies).

    Two inputs meet here:

    - the UPPER bound: [bbb4_target] (BBB4_Theorem.v, the census-backed
      closeout) says every (4,2) machine satisfies
      [QHBound champion_score], or never quasihalts, or is [skipped
      D_remaining].  As of 2026-08-01 the residue is EMPTY:
      [remaining_rows = []], so [skipped D_remaining] is uninhabited
      ([not_skipped_nil], the one lemma docs/CLAIMS.md said was
      missing) and the disjunct discharges.  A never-quasihalter
      satisfies any [QHBound] vacuously ([neverqh_qhbound]), so the
      whole upper bound collapses to one line:
      [forall tm, QHBound champion_score tm].

    - the LOWER bound: the champion 1RB1LD_1RC1RB_1LC1LA_0RC0RD has a
      state ([StD]) whose last visit is at configuration index
      32,779,477 -- score EXACTLY 32,779,478 ([champion_attains],
      kernel-checked by a second 32.8M-step [vm_compute] in the
      champion's own file).

    [BBB4_is] packages the two into the value specification: [B] is
    attained by some state of some machine, and no state of any machine
    beats it.  [BBB4_value] proves [BBB4_is champion_score], and
    [BBB4_is_unique] confirms the spec pins a single number -- so
    "BBB(4) = 32,779,478" has exactly one reading and this file proves
    it.

    Like BBB4_Theorem.v this file loads the committed census .vo
    (through CloseoutFinal): compile under the census opam switch (see
    tools/census_cache.py, docs/VERIFYING.md).  Axiom footprint:
    [functional_extensionality_dep] only ([Print Assumptions] below). *)
From Coq Require Import Arith List Lia.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import TNF_QH Deferred_Defs.
From BBB4.Closeout Require Import CloseoutKit ShadowKit CoreRows Closeout
  CloseoutFinal BBB4_Theorem.
From BBB4.Machines.Counters Require Import Champion_1RB1LD_1RC1RB_1LC1LA_0RC0RD.
Import ListNotations.

(** ** The residue disjunct is uninhabited

    [Deferred [] tm] has no derivation: the base constructor needs
    [In h []], and the swap/mirror constructors only recurse.  This is
    the lemma docs/CLAIMS.md named as the missing piece. *)

Lemma not_deferred_nil : forall tm, ~ Deferred [] tm.
Proof.
  intros tm H.
  induction H as [h tm Hin _ | u v tm _ _ _ _ IH | tm _ IH];
    [exact Hin | exact IH | exact IH].
Qed.

Lemma not_skipped_nil : forall tm, ~ skipped [] tm.
Proof.
  intros tm [H | (qs & t & _ & H)]; exact (not_deferred_nil _ H).
Qed.

(** [D_remaining] is literally the empty list ([remaining_rows = []],
    CoreRows.v): both hold by computation. *)
Lemma D_remaining_nil : D_remaining = [].
Proof. reflexivity. Qed.

Lemma not_skipped_remaining : forall tm, ~ skipped D_remaining tm.
Proof.
  intro tm. rewrite D_remaining_nil. apply not_skipped_nil.
Qed.

(** ** The unconditional upper bound *)

(** [bbb4_target] with the residue disjunct discharged: every (4,2)
    machine quasihalts with every quiet state quiet before index
    32,779,478, or never quasihalts.  No skips, no residue. *)
Theorem bbb4_unconditional : forall tm,
  QHBound champion_score tm \/ NeverQuasiHaltsSt tm.
Proof.
  intro tm.
  destruct (bbb4_target tm) as [H | [H | H]];
    [left; exact H | right; exact H
    | destruct (not_skipped_remaining tm H)].
Qed.

(** ...and since a never-quasihalter satisfies any score bound
    vacuously, the upper bound is one clause. *)
Theorem bbb4_upper : forall tm, QHBound champion_score tm.
Proof.
  intro tm.
  destruct (bbb4_unconditional tm) as [H | H];
    [exact H | apply neverqh_qhbound; exact H].
Qed.

(** ** The value

    [champ_score] (the champion file's Horner constant) and
    [champion_score] (the closeout's) are the same numeral. *)
Lemma champ_score_champion_score : champ_score = champion_score.
Proof. reflexivity. Qed.

(** [BBB4_is B]: the state-level Beeping Busy Beaver value spec for
    (4,2), in the harness scoring convention (a quiet state's score is
    its last visited configuration index + 1 -- the step at which its
    last transition fires):

    - ATTAINED: some machine has a state whose score is exactly [B];
    - MAXIMAL: no state of any machine has a score above [B]. *)
Definition BBB4_is (B : nat) : Prop :=
  (exists tm q s, QuietAfter tm q s /\ S s = B)
  /\ (forall tm, QHBound B tm).

Theorem BBB4_value : BBB4_is champion_score.
Proof.
  split.
  - destruct champion_attains as (q & s & Hq & Hs).
    exists tm_champion, q, s.
    rewrite <- champ_score_champion_score.
    exact (conj Hq Hs).
  - exact bbb4_upper.
Qed.

(** The spec pins a single number: BBB(4) = 32,779,478 has exactly one
    reading. *)
Theorem BBB4_is_unique : forall B B', BBB4_is B -> BBB4_is B' -> B = B'.
Proof.
  intros B B' [(tm & q & s & Hq & Hs) Hub] [(tm' & q' & s' & Hq' & Hs') Hub'].
  pose proof (Hub' tm q s Hq).
  pose proof (Hub tm' q' s' Hq').
  lia.
Qed.

(** The champion itself, in one breath: it quasihalts, and no smaller
    bound covers it -- its score IS the value. *)
Corollary champion_is_extremal :
  QuasiHaltsSt tm_champion
  /\ (forall B, QHBound B tm_champion -> champion_score <= B).
Proof.
  split; [exact quasihalts_champion|].
  intros B H.
  rewrite <- champ_score_champion_score.
  exact (qhbound_champion_tight B H).
Qed.

Print Assumptions BBB4_value.
Print Assumptions BBB4_is_unique.
