(** * QuadMGShape: the QUAD route's composition skeleton, pinned.

    WAVE26_FINDINGS section 7d claims the 41 QUAD/QUAD machines compose
    through [MeasureGlue.mrun] with abstract state (k, m) -- probe depth and
    unprobed count -- a PURE pair-function [stepA] (no tape inspection), the
    measure [mu = snd] and the conservation law [P x = fst x + snd x = j].
    This file is that claim, kernel-checked at the skeleton level: given a
    micro hop [Cf k (S m) -> Cf (S k) m] per probe and a terminal run at
    [m = 0], the whole quadratic interior lap is one [csteps] run.  The
    next wave's boards instantiate [Cf], the hop and the terminal with the
    per-machine chains gated by tools/counters/quad_probe.py.

    Axiom-free (Print Assumptions on [quad_lap]: closed under the global
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
End Shape.
