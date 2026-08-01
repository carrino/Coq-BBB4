(** * LapGlueNeverIx: [LapGlue.glue_neverqh] over an ARBITRARY index.

    [Counters/LapGlueIx.v] lifts [LapGlueQuiet]'s QUASIHALTER closer off
    [positive] and onto an arbitrary numeral type; this is the same lift of
    [LapGlue.glue_neverqh], the never-quasihalting one.  A base-3 (or
    base-[b], or fibonacci) counter has no [positive] to index its anchors
    by -- its numerals are its own inductive type with its own successor --
    and neither closer's proof uses arithmetic, so both lift by dropping the
    index type's identity and the [p0 <= p] guard.

    It is a separate file rather than a third section of [LapGlueIx] because
    it shares none of that file's machinery: no [AvoidRun] on the lap, no
    [VisitsAt]/[QuietAfter] bookkeeping for the state that stops firing, and
    no [QHBound].  Every state recurs, so the three premises are the bare

      bootstrap   the blank tape reaches (the denotation of) [Cf i0]
      lap         [Cf i] reaches [Cf (nxt i)] in at least one step, up to
                  blank padding ([lift] equality)
      visits      from every [Cf i], EVERY state is reachable at some offset

    and the conclusion is [NeverQuasiHaltsSt] verbatim.  Which of the two
    closers a row wants is decided by its liveness and nothing else: a state
    that stops firing IS a quasihalt, so a row whose anchor state fires once
    (the three-state [Ter3Wall*] rows, whose [StA] is the target of no
    transition) needs [LapGlueIx]'s, and a row all of whose states recur
    needs this one.  [Counters/Ter3WallD.v] is the first client.

    The lap premise is stated up to [lift] for [LapGlue]'s reason: an
    overflow lap leaves one freshly-blanked cell beyond the new working area,
    so the reached configuration equals the next anchor only after stripping
    that trailing blank ([WTape.lift_app_blank]).

    Axiom footprint: none beyond [CTape]'s. *)

From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement CTape.
Import ListNotations.

Section GlueNeverIx.

Variable tm : TM.
Variable I : Type.
Variable nxt : I -> I.
Variable Cf : I -> cconf.
Variable i0 : I.

Hypothesis Hboot : exists t0, stepn tm t0 InitES = Some (lift (Cf i0)).
Hypothesis Hlap : forall i,
  exists n c', csteps tm n (Cf i) = Some c'
               /\ lift c' = lift (Cf (nxt i)) /\ 0 < n.
Hypothesis Hvis : forall i q,
  exists k c, csteps tm k (Cf i) = Some c /\ fst c = q.

(** The k-th anchor is reached at a global index of at least k. *)
Lemma gni_reach : forall k, exists T i, k <= T /\
  stepn tm T InitES = Some (lift (Cf i)).
Proof.
  induction k as [|k IH].
  - destruct Hboot as (t0 & H0). exists t0, i0. split; [lia | exact H0].
  - destruct IH as (T & i & HT & Hstep).
    destruct (Hlap i) as (n & c' & Hrun & Hlift & Hn).
    exists (T + n), (nxt i). split; [lia |].
    rewrite stepn_add, Hstep, (csteps_lift _ _ _ _ Hrun), Hlift.
    reflexivity.
Qed.

Theorem glue_neverqh_ix : NeverQuasiHaltsSt tm.
Proof.
  intros q _ N.
  destruct (gni_reach N) as (T & i & HN & Hstep).
  destruct (Hvis i q) as (k & c & Hc & Hqc).
  exists (T + k). split; [lia |].
  exists (lift c). split.
  - rewrite stepn_add, Hstep. apply csteps_lift; exact Hc.
  - rewrite lift_state. exact Hqc.
Qed.

End GlueNeverIx.
