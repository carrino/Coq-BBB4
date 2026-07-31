(** * LapGlueIx: [LapGlue] / [LapGlueQuiet] over an ARBITRARY index.

    Both closers index their anchor family by [positive] and step it with
    [Pos.succ].  Nothing in either proof uses arithmetic: [glue_reach]
    inducts on the number of laps and [Pos.le] appears only to carry the
    "[p0 <= p]" guard the lap premise is stated with.  A counter in a radix
    other than 2 has no [positive] to index by -- its numerals are its own
    inductive type with its own successor -- so this file states the same two
    theorems over

      [I : Type]   [nxt : I -> I]   [Cf : I -> cconf]

    with the guard dropped (the lap holds at every index, which is what a
    from-scratch numeral type gives you for free).

    [Counters/TernCounter.v] is the first client: base-3 numerals, whose
    carry runs over the digit 2 and whose interior branch splits in two
    (digit 0 -> 1 and digit 1 -> 2) rather than one.

    Axiom footprint: none beyond [CTape]'s. *)

From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Counters Require Import LapGlueQuiet.
Import ListNotations.

Section GlueIx.

Variable tm : TM.
Variable I : Type.
Variable nxt : I -> I.
Variable Cf : I -> cconf.
Variable i0 : I.
Variable qa : St.
Variable t0 s0 : nat.

(** The bootstrap, at a CONCRETE index (the score bound depends on it). *)
Hypothesis Hboot : stepn tm t0 InitES = Some (lift (Cf i0)).

(** The lap, with avoidance of [qa] -- [LapGlueQuiet.Hlap] verbatim. *)
Hypothesis Hlap : forall i,
  exists n c', csteps tm n (Cf i) = Some c'
               /\ lift c' = lift (Cf (nxt i)) /\ 0 < n
               /\ AvoidRun tm qa n (Cf i).

(** Visits for every RECURRING state (everything but [qa]). *)
Hypothesis Hvis : forall i q, q <> qa ->
  exists k c, csteps tm k (Cf i) = Some c /\ fst c = q.

(** [qa]'s last visit, and the checked [qa]-free window up to the anchor. *)
Hypothesis Hvis0 : VisitsAt tm qa s0.
Hypothesis Hbq : forall n c, s0 < n < t0 ->
  stepn tm n InitES = Some c -> fst c <> qa.

(** The anchor chain, carrying [qa]-freedom of everything since [t0]. *)
Lemma gi_anchors : forall k, exists T i, k <= T /\ t0 <= T
  /\ stepn tm T InitES = Some (lift (Cf i))
  /\ (forall N c, t0 <= N < T -> stepn tm N InitES = Some c -> fst c <> qa).
Proof.
  induction k as [|k IH].
  - exists t0, i0. split; [lia|]. split; [lia|].
    split; [exact Hboot|]. intros N c HN. lia.
  - destruct IH as (T & i & HkT & Ht0T & Hstep & Hcov).
    destruct (Hlap i) as (n & c' & Hrun & Hlift & Hn & Hav).
    exists (T + n), (nxt i).
    split; [lia|]. split; [lia|].
    split.
    { rewrite stepn_add, Hstep, (csteps_lift _ _ _ _ Hrun), Hlift.
      reflexivity. }
    intros N c HN HstepN.
    destruct (Nat.lt_ge_cases N T) as [HNT | HTN].
    + exact (Hcov N c ltac:(lia) HstepN).
    + replace N with (T + (N - T)) in HstepN by lia.
      rewrite stepn_add, Hstep in HstepN.
      destruct (csteps_prefix tm (N - T) n (Cf i) c' ltac:(lia) Hrun)
        as (cm & Hcm & _).
      rewrite (csteps_lift _ _ _ _ Hcm) in HstepN.
      injection HstepN as <-.
      rewrite lift_state.
      exact (Hav (N - T) cm ltac:(lia) Hcm).
Qed.

Lemma gi_noqa : forall N c, t0 <= N ->
  stepn tm N InitES = Some c -> fst c <> qa.
Proof.
  intros N c HN Hstep.
  destruct (gi_anchors (S N)) as (T & i & HkT & Ht0T & _ & Hcov).
  exact (Hcov N c ltac:(lia) Hstep).
Qed.

Lemma gi_quiet : QuietAfter tm qa s0.
Proof.
  split; [exact Hvis0|].
  intros n Hn (c & Hc & Hqc).
  destruct (Nat.lt_ge_cases n t0) as [Hlt | Hge].
  - exact (Hbq n c ltac:(lia) Hc Hqc).
  - exact (gi_noqa n c Hge Hc Hqc).
Qed.

Lemma gi_recurs : forall q, q <> qa ->
  forall N, exists n, N <= n /\ VisitsAt tm q n.
Proof.
  intros q Hq N.
  destruct (gi_anchors N) as (T & i & HN & _ & Hstep & _).
  destruct (Hvis i q Hq) as (k & c & Hc & Hqc).
  exists (T + k). split; [lia|].
  exists (lift c). split.
  - rewrite stepn_add, Hstep. apply csteps_lift; exact Hc.
  - rewrite lift_state. exact Hqc.
Qed.

Lemma gi_nonhalt : NonHalt tm.
Proof.
  intros n Hnone.
  destruct (gi_anchors n) as (T & i & HT & _ & Hstep & _).
  replace T with (n + (T - n)) in Hstep by lia.
  rewrite stepn_add, Hnone in Hstep. discriminate.
Qed.

Lemma gi_qhbound : QHBound (S s0) tm.
Proof.
  intros q s Hq.
  destruct (st_eqb q qa) eqn:Eq.
  - apply st_eqb_spec in Eq. subst q.
    destruct Hq as (HvisS & _).
    destruct (Nat.le_gt_cases s s0) as [Hle | Hgt]; [lia|].
    exfalso. destruct gi_quiet as (_ & Hq0). exact (Hq0 s Hgt HvisS).
  - assert (Hne : q <> qa).
    { intro E. rewrite E in Eq.
      rewrite (proj2 (st_eqb_spec qa qa) eq_refl) in Eq. discriminate. }
    exfalso.
    destruct Hq as (_ & Hafter).
    destruct (gi_recurs q Hne (S s)) as (n & Hn & Hvn).
    exact (Hafter n ltac:(lia) Hvn).
Qed.

Theorem glue_qh_quiet_ix : NonHalt tm /\ QHBound (S s0) tm /\ QuasiHaltsSt tm.
Proof.
  split; [exact gi_nonhalt | split; [exact gi_qhbound |]].
  exact (quiet_after_qh tm qa s0 gi_quiet).
Qed.

End GlueIx.
