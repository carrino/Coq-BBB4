(** * BBB4_Spec: the claim "BBB(4) = 32,779,478".

    This file STATES the claim; it does not prove it, and nothing in
    it refers to any proof.  Together with the machine model it
    imports (BBB4_Statement.v) it contains every definition that
    appears in the claim: the two files import only each other and
    the Coq standard library, and can be read top to bottom in one
    sitting.

    Contents:

    - [tm_champion]    -- the champion machine, bbchallenge text
                          1RB1LD_1RC1RB_1LC1LA_0RC0RD;
    - [champion_score] -- 32,779,478;
    - [Attains tm B]   -- machine [tm] has a state whose quasihalting
                          score is exactly [B];
    - [BBB4_is B]      -- [B] is attained, and no machine attains
                          more: "BBB(4) = B";
    - [BBB4_statement] -- the claim: [BBB4_is champion_score].

    Scoring convention (Aaronson's Beeping Busy Beaver, at state
    level, in the convention of the BBB harness repo -- carrino/BBB,
    README "Definitions"): steps are numbered 1, 2, ...; a state
    whose LAST visit is at configuration index [s]
    ([QuietAfter tm q s], BBB4_Statement.v) fires its last transition
    at step [s+1], so its score is [S s].

    Corner cases, and why they cannot move the value:

    - a HALTING machine's quiet states all score at most its halting
      step (there are no configurations after the halt), so halting
      machines are covered by the same two clauses with no special
      case -- and BB(4) = 107 is far below the champion;
    - a NEVER-VISITED ("silent") state attains nothing here, because
      [QuietAfter] contains the visit.  Under the opposite convention
      a silent state would be a trivial score-0 quasihalter; either
      way no silent state can decide which [B] satisfies [BBB4_is]
      (score 0 is attained by nobody -- [Attains] forces [B = S s] --
      and bounds nothing).

    [BBB4_is_unique], proved below without any axiom, shows the spec
    pins a single number: "BBB(4) = 32,779,478" has exactly one
    reading. *)

From Coq Require Import Arith NArith Lia.
From BBB4 Require Import BBB4_Statement.

(** ** The champion: 1RB1LD_1RC1RB_1LC1LA_0RC0RD

    bbchallenge text format, one 3-character entry per (state, read
    symbol): write symbol, head direction, next state. *)

Definition tm_champion : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB) | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DR StC) | StB, S1 => Some (mkTrans S1 DR StB)
  | StC, S0 => Some (mkTrans S1 DL StC) | StC, S1 => Some (mkTrans S1 DL StA)
  | StD, S0 => Some (mkTrans S0 DR StC) | StD, S1 => Some (mkTrans S0 DR StD)
  end.

(** ** The value

    Written as [N.to_nat] of a binary literal: a bare [nat] literal
    this large parses to an opaque [Nat.of_num_uint] blob (and would
    be a 32.8M-constructor unary term if ever evaluated); [N.to_nat]
    of the [N] literal is the same number, stated readably. *)

Definition champion_score : nat := N.to_nat 32779478.

(** ** Attaining a score

    [Attains tm B]: some state of [tm] is visited for the last time
    at configuration index [s] with [S s = B] -- its last transition
    fires at step [B], and after that the state is never entered
    again. *)

Definition Attains (tm : TM) (B : nat) : Prop :=
  exists q s, QuietAfter tm q s /\ S s = B.

(** Attaining any score is quasihalting (state level). *)
Lemma attains_qh : forall tm B, Attains tm B -> QuasiHaltsSt tm.
Proof. intros tm B (q & s & Hq & _). exact (quiet_after_qh tm q s Hq). Qed.

(** ** The Beeping Busy Beaver value specification for (4,2)

    [BBB4_is B]: [B] is the maximum, over all 4-state 2-symbol
    machines [tm] and all states [q] of [tm], of the step at which
    [q]'s last transition fires -- the maximum stated as "attained +
    no machine attains more".  The quantifier ranges over the FULL
    function type [TM]: every transition table, normalized or not,
    halting or not. *)

Definition BBB4_is (B : nat) : Prop :=
  (exists tm, Attains tm B)
  /\ (forall tm B', Attains tm B' -> B' <= B).

(** The claim. *)

Definition BBB4_statement : Prop := BBB4_is champion_score.

(** ** The spec pins a single number

    Axiom-free ([Print Assumptions] below): any two values satisfying
    [BBB4_is] are equal, so "BBB(4) = 32,779,478" has exactly one
    reading. *)

Lemma BBB4_is_unique : forall B B', BBB4_is B -> BBB4_is B' -> B = B'.
Proof.
  intros B B' [(tm & Ha) Hmax] [(tm' & Ha') Hmax'].
  pose proof (Hmax' tm B Ha).
  pose proof (Hmax tm' B' Ha').
  lia.
Qed.

Print Assumptions BBB4_is_unique.
