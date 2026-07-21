(** * WaveCounter: the never-quasihalting closer for the wave family.

    The six wave_counter machines (BBB certs counter6/7/17/24/27/36) and
    the one wave4_counter (#15) are PARITY-WAVE ODOMETERS: the event
    config is a block word

      1^{B_0} 0 1^{B_1} 0 ... 0 1^{B_m}   (single-0 separators),

    the head one cell past the frontier at the edge state, and one pass
    increments the frontier (B_m += 1) then propagates a parity carry
    leftward, stopping at the first odd block (depositing +1 there) or,
    if every interior block is even and the lead is 1, SPAWNING a new
    length-1 block after the lead.  The wave depth and block lengths are
    both unbounded, so a pass is a NESTED translated cycle, NOT a single
    parametric run -- unlike the mono/spacer families [LapGlue] was built
    for.  See the wave design appendix in NEXT_SESSION.md.

    This file carries the machine-INDEPENDENT closer.  Where [LapGlue]
    indexes its anchors by a [positive] advanced by [Pos.succ], the wave
    anchors are indexed by an arbitrary state type [A] advanced by a
    total successor [nextA], constrained to a preserved invariant [Inv]
    (the parity-safety predicate: the wave never stops at the lead and
    every spawn has lead 1).  The reachability argument is identical to
    [LapGlue.glue_reach] with [Nat.iter k nextA a0] in place of the
    positive anchor.  No axioms. *)

From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement CTape.
Import ListNotations.

Section WaveGlue.

Variable tm : TM.
Variable A : Type.
Variable nextA : A -> A.
Variable Inv : A -> Prop.
Variable Cf : A -> cconf.
Variable a0 : A.

Hypothesis Hinv0 : Inv a0.
Hypothesis Hinv_step : forall a, Inv a -> Inv (nextA a).
Hypothesis Hboot : exists t0, stepn tm t0 InitES = Some (lift (Cf a0)).
Hypothesis Hlap : forall a, Inv a ->
  exists n c', csteps tm n (Cf a) = Some c' /\
               lift c' = lift (Cf (nextA a)) /\ 0 < n.
Hypothesis Hvis : forall a q, Inv a ->
  exists k c, csteps tm k (Cf a) = Some c /\ fst c = q.

(** The [k]-th anchor, and that the invariant rides the whole orbit. *)
Definition anc (k : nat) : A := Nat.iter k nextA a0.

Lemma anc_inv : forall k, Inv (anc k).
Proof.
  induction k as [|k IH].
  - exact Hinv0.
  - apply Hinv_step. exact IH.
Qed.

(** The [k]-th anchor is reached at a global index of at least [k]. *)
Lemma wglue_reach : forall k, exists T, k <= T /\
  stepn tm T InitES = Some (lift (Cf (anc k))).
Proof.
  induction k as [|k IH].
  - destruct Hboot as (t0 & H0). exists t0. split; [lia | exact H0].
  - destruct IH as (T & HT & Hstep).
    destruct (Hlap (anc k) (anc_inv k)) as (n & c' & Hrun & Hlift & Hn).
    exists (T + n). split; [lia|].
    rewrite stepn_add, Hstep.
    rewrite (csteps_lift _ _ _ _ Hrun), Hlift.
    reflexivity.
Qed.

Theorem wglue_neverqh : NeverQuasiHaltsSt tm.
Proof.
  intros q _ N.
  destruct (wglue_reach N) as (T & HN & Hstep).
  destruct (Hvis (anc N) q (anc_inv N)) as (k & c & Hc & Hqc).
  exists (T + k). split; [lia|].
  exists (lift c). split.
  - rewrite stepn_add, Hstep. apply csteps_lift; exact Hc.
  - rewrite lift_state. exact Hqc.
Qed.

End WaveGlue.
