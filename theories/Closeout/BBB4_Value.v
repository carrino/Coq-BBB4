(** * BBB4_Value: the proof of [BBB4_statement] -- BBB(4) = 32,779,478.

    The CLAIM lives in BBB4_Spec.v: [BBB4_statement := BBB4_is
    champion_score], stated census-free in terms of BBB4_Statement.v
    alone.  THIS file is where it gets proved.  Hand-written (NOT
    generated -- gen_stages.py emits [bbb4_target] with the [skipped
    D_remaining] disjunct whatever the residue is; this file is where
    the disjunct dies).

    Two inputs meet here:

    - the UPPER bound: [bbb4_target] (BBB4_Theorem.v, the census-backed
      closeout) says every (4,2) machine satisfies
      [QHBound champion_score], or never quasihalts, or is [skipped
      D_remaining].  As of 2026-08-01 the residue is EMPTY:
      [remaining_rows = []], so [skipped D_remaining] is uninhabited
      ([not_skipped_nil]) and the disjunct discharges.  A
      never-quasihalter satisfies any [QHBound] vacuously
      ([neverqh_qhbound]), so the whole upper bound collapses to one
      line: [forall tm, QHBound champion_score tm].

    - the LOWER bound: the champion [tm_champion] (BBB4_Spec.v,
      1RB1LD_1RC1RB_1LC1LA_0RC0RD) has a state ([StD]) whose last visit
      is at configuration index 32,779,477 -- so it [Attains] exactly
      [champion_score] = 32,779,478 ([champion_attains], kernel-checked
      by a second 32.8M-step [vm_compute] in the champion's own file).

    [BBB4_value : BBB4_statement] packages the two.  Every constant in
    its statement -- [BBB4_statement], [BBB4_is], [Attains],
    [champion_score], [tm_champion] -- is BBB4_Spec's, and every
    predicate under those is BBB4_Statement.v's: to audit the claim,
    read those two files; to audit the proof, run [Print Assumptions]
    below ([functional_extensionality_dep] only).  [BBB4_is_unique]
    (BBB4_Spec.v, axiom-free) confirms the spec pins a single number,
    so "BBB(4) = 32,779,478" has exactly one reading.

    Like BBB4_Theorem.v this file loads the committed census .vo
    (through CloseoutFinal): compile under the census opam switch (see
    tools/census_cache.py, docs/VERIFYING.md). *)
From Coq Require Import Arith List Lia.
From BBB4 Require Import BBB4_Statement BBB4_Spec.
From BBB4.Census Require Import TNF_QH Deferred_Defs.
From BBB4.Closeout Require Import CloseoutKit ShadowKit CoreRows Closeout
  CloseoutFinal BBB4_Theorem.
From BBB4.Machines.Counters Require Import Champion_1RB1LD_1RC1RB_1LC1LA_0RC0RD.
Import ListNotations.

(** ** The residue disjunct is uninhabited

    [Deferred [] tm] has no derivation: the base constructor needs
    [In h []], and the swap/mirror constructors only recurse. *)

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

(** ** The value: BBB(4) = 32,779,478

    ATTAINED by the champion ([champion_attains], the kernel-checked
    exact score), and MAXIMAL because any attained score [S s] is
    bounded by [bbb4_upper]'s [QHBound]. *)

Theorem BBB4_value : BBB4_statement.
Proof.
  split.
  - exists tm_champion. exact champion_attains.
  - intros tm B' (q & s & Hq & Hs).
    rewrite <- Hs. exact (bbb4_upper tm q s Hq).
Qed.

(** The same theorem with the claim's one definition unfolded, for
    readers grepping for the value spec by name. *)
Corollary BBB4_value_is : BBB4_is champion_score.
Proof. exact BBB4_value. Qed.

(** The champion itself, in one breath: it quasihalts, and no smaller
    bound covers it -- its score IS the value. *)
Corollary champion_is_extremal :
  QuasiHaltsSt tm_champion
  /\ (forall B, QHBound B tm_champion -> champion_score <= B).
Proof.
  split; [exact quasihalts_champion | exact qhbound_champion_tight].
Qed.

Print Assumptions BBB4_value.
