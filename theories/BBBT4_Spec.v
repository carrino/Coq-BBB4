(** * BBBT4_Spec: the claim "BBB_tr(4) = 32,779,478".

    The instruction-level (transition-level) twin of BBB4_Spec.v.  This
    file STATES the claim; it does not prove it, and nothing in it
    refers to any proof.  Every definition in the claim is here, in
    BBBT4_Statement.v (instructions, [FiresAt], [QuietAfterTr]), in
    BBB4_Statement.v (the machine model) or in BBB4_Spec.v (the
    champion table and the number); those four files import only each
    other and the Coq standard library.

    Contents:

    - [AttainsTr tm B]  -- machine [tm] has an instruction whose
                           transition-level quasihalting score is
                           exactly [B];
    - [BBBT4_is B]      -- [B] is attained, and no machine attains
                           more: "BBB_tr(4) = B";
    - [BBBT4_statement] -- the claim: [BBBT4_is champion_score], with
                           [champion_score] = 32,779,478 BBB4_Spec's.

    Scoring convention (the BBB harness's transition-level bookkeeping,
    carrino/BBB, README "Transition-level bookkeeping"): an instruction
    (state, read symbol) whose LAST fire is at configuration index [s]
    ([QuietAfterTr tm t s]) scores [S s], the step-numbering convention
    of the state level.

    The value is the state level's, attained by the same machine: the
    champion's state D is last entered at index 32,779,477 reading some
    symbol [a], so instruction [(D, a)] fires there and never again.
    The transition convention is weaker to satisfy per state (a quiet
    state yields a quiet instruction, [quiet_after_st_tr]), so it could
    only have been larger; the instruction-level census and closeout
    show it is not.

    Corner cases, as at state level: a NEVER-FIRED instruction attains
    nothing ([QuietAfterTr] contains the fire), and a HALTING machine's
    instructions all score at most its halting step.

    [BBBT4_is_unique], proved below without any axiom, shows the spec
    pins a single number. *)

From Coq Require Import Arith Lia.
From BBB4 Require Import BBB4_Statement BBBT4_Statement BBB4_Spec.

(** ** Attaining a score

    [AttainsTr tm B]: some instruction of [tm] fires for the last time
    at configuration index [s] with [S s = B]. *)

Definition AttainsTr (tm : TM) (B : nat) : Prop :=
  exists t s, QuietAfterTr tm t s /\ S s = B.

(** Attaining any score is quasihalting (transition level). *)
Lemma attains_tr_qh : forall tm B, AttainsTr tm B -> QuasiHaltsTr tm.
Proof. intros tm B (t & s & Hq & _). exact (quiet_after_tr_qh tm t s Hq). Qed.

(** ** The transition-level Beeping Busy Beaver value for (4,2)

    [BBBT4_is B]: [B] is the maximum, over all 4-state 2-symbol
    machines [tm] and all instructions [t] of [tm], of the step at
    which [t] fires for the last time.  The quantifier ranges over the
    FULL function type [TM], as in [BBB4_is]. *)

Definition BBBT4_is (B : nat) : Prop :=
  (exists tm, AttainsTr tm B)
  /\ (forall tm B', AttainsTr tm B' -> B' <= B).

(** The claim. *)

Definition BBBT4_statement : Prop := BBBT4_is champion_score.

(** ** The spec pins a single number *)

Lemma BBBT4_is_unique : forall B B', BBBT4_is B -> BBBT4_is B' -> B = B'.
Proof.
  intros B B' [(tm & Ha) Hmax] [(tm' & Ha') Hmax'].
  pose proof (Hmax' tm B Ha).
  pose proof (Hmax tm' B' Ha').
  lia.
Qed.

Print Assumptions BBBT4_is_unique.
