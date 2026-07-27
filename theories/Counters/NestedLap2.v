(** * NestedLap2: the SYNC BOUNCER shape -- TWO inner counts per overflow.

    `docs/WAVE18_FINDINGS.md` §4c.  On the machines whose EXIT half measures
    EXPONENTIAL, splitting one overflow phase at the first inner all-ones fill
    and re-running the inner-family search on the SECOND half finds another
    consecutive `2^(K-1)..2^K-1` family on 11 of 16 sampled -- same state,
    same alphabet, SHIFTED TAIL.  The overflow phase is

        boot -> count -> SHIFT -> count -> exit

    which is John's reading of mxdys' sync bouncer counter verbatim ("count
    8->15, shift, count 8->15 again"): two complementary counts summing to
    `2^n - 1`, so ONE overflow costs `2^n` increments.

    **This needs no new composition theorem.**
    [NestedLapLift.nested_overflow_lift]'s [Hboot] is an ARBITRARY [csteps]
    run into [Cin v0] -- it never asked for one chain.  So instantiate that
    theorem at the SECOND inner family and build its boot out of the first
    count.  That is all this file does, in one lemma.

    Axiom footprint: [functional_extensionality_dep] only (inherited from
    [CTape.lift]; this file adds none). *)

From Coq Require Import Arith Lia List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape MonoCounter JpCounter IXPGadgets
                                  LapCertGlue LapCertGlueLift NestedLap
                                  NestedLapLift.
Import ListNotations.

Section BootViaFill.

Variable tm : TM.
Variable Cc Cin1 Cin2 : positive -> cconf.

(** The FIRST inner family's interior lap, up to [lift] -- the ordinary one. *)
Hypothesis Hin1 : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin1 v) = Some c'
               /\ lift c' = lift (Cin1 (Pos.succ v)).

(** A boot that runs an ENTIRE first count on the way.

    [boot1] reaches the first family at [v0]; the first count runs to its
    all-ones fill inside an existential ([inner_to_fill_lift], the
    [Theta(2^j)]); [mid] is the SHIFT, an ordinary affine chain from that fill
    into the second family at [w0].  The result is exactly the shape
    [nested_overflow_lift] wants for its own [Hboot]. *)
Lemma boot_via_fill : forall p v0 w0,
  (exists n c, 0 < n /\ csteps tm n (Cc p) = Some c /\ lift c = lift (Cin1 v0)) ->
  (exists n c, csteps tm n (Cin1 (fill v0)) = Some c /\ lift c = lift (Cin2 w0)) ->
  exists n c, 0 < n /\ csteps tm n (Cc p) = Some c /\ lift c = lift (Cin2 w0).
Proof.
  intros p v0 w0 (n1 & c1 & Hn1 & H1 & L1) (n2 & c2 & H2 & L2).
  destruct (inner_to_fill_lift tm Cin1 Hin1 v0) as (ni & Hi).
  assert (Hrest : stepn tm (ni + n2) (lift c1) = Some (lift c2)).
  { rewrite stepn_add, L1, Hi. exact (csteps_lift _ _ _ _ H2). }
  destruct (stepn_csteps_at tm (ni + n2) c1 (lift c2) Hrest)
    as (cf & Hcf & Hcfl).
  exists (n1 + (ni + n2)), cf. split; [lia|]. split.
  - rewrite csteps_add, H1. exact Hcf.
  - rewrite Hcfl. exact L2.
Qed.

End BootViaFill.
