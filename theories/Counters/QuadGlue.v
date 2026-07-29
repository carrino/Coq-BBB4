(** * QuadGlue: the QUAD route's composition, as a library.

    [Tests/QuadMGShape.v] pinned the claim of WAVE26_FINDINGS section 7d at
    the skeleton level; this file is the same composition placed under
    [Counters/] so the QMG_* boards can import it.  The 41 QUAD/QUAD
    machines' interior lap is a binary increment whose carry is done by
    LINEAR SEARCH: [Theta(j)] micro laps (one round trip per digit), each an
    ordinary chain, composed here through [MeasureGlue.mrun] with abstract
    state (probe depth k, unprobed count m), the measure [mu = snd] and the
    conservation law [k + m = j].

    Axiom-free ([Print Assumptions quad_lap]: closed under the global
    context). *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape MeasureGlue.
Import ListNotations.

Section Shape.
Variable tm : TM.
Variable j : nat.                       (* the anchor's carry index *)
Variable Cf : nat -> nat -> cconf.      (* M(k) at unprobed count m *)
Variable goal : cconf.

Definition qstep (x : nat * nat) : option (nat * nat) :=
  match snd x with S m' => Some (S (fst x), m') | O => None end.

Definition qmu (x : nat * nat) : nat := snd x.

Hypothesis Hmicro : forall k m, k + S m = j ->
  exists n, csteps tm n (Cf k (S m)) = Some (Cf (S k) m) /\ 0 < n.
Hypothesis Hterm0 : forall k, k + 0 = j ->
  exists n c', csteps tm n (Cf k 0) = Some c' /\ lift c' = lift goal /\ 0 < n.

Lemma quad_lap : exists n c',
  csteps tm n (Cf 0 j) = Some c' /\ lift c' = lift goal /\ 0 < n.
Proof.
  change (Cf 0 j)
    with ((fun x : nat * nat => Cf (fst x) (snd x)) (0, j)).
  apply (mrun tm (nat * nat) qstep qmu
           (fun x => fst x + snd x = j)
           (fun x => Cf (fst x) (snd x)) goal).
  - intros [k m] [k' m'] HP Hst.
    unfold qstep in Hst; cbn [fst snd] in *.
    destruct m as [|m0]; [discriminate|].
    injection Hst as <- <-.
    cbn [fst snd] in HP.
    destruct (Hmicro k m0) as (n & Hrun & Hn); [cbn; lia|].
    split; [cbn; lia|]. split; [unfold qmu; cbn; lia|].
    exists n. split; [exact Hrun | exact Hn].
  - intros [k m] HP Hst.
    unfold qstep in Hst; cbn [fst snd] in *.
    destruct m; [|discriminate].
    exact (Hterm0 k HP).
  - cbn. lia.
Qed.

(** A visit witness INSIDE the ladder.

    [LapCertGlue.vis_via_ovf] carries a witness taken from ONE chain prefix
    at the anchor, and for a QUAD board that chain is the boot -- so a state
    that fires in a micro hop or in the terminal has no witness at all.  It
    is reachable, though: iterating [Hmicro] walks every rung, and the last
    one, [Cf j 0], is where BOTH terminals start.  This is the analogue of
    [NestedLapLift.vis_via_fill], which the nested route needed for exactly
    the same reason. *)
Lemma quad_reach : forall m k, k + m = j ->
  exists n, csteps tm n (Cf k m) = Some (Cf j 0).
Proof.
  induction m as [|m' IH]; intros k Hk.
  - exists 0. rewrite <- (Nat.add_0_r k), Hk. reflexivity.
  - destruct (Hmicro k m' Hk) as (n1 & H1 & _).
    destruct (IH (S k) ltac:(lia)) as (n2 & H2).
    exists (n1 + n2). rewrite csteps_add, H1. exact H2.
Qed.

Lemma quad_reach0 : exists n, csteps tm n (Cf 0 j) = Some (Cf j 0).
Proof. exact (quad_reach j 0 ltac:(lia)). Qed.

End Shape.
