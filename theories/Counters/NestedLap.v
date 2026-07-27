(** * NestedLap: an EXPONENTIAL overflow branch, composed from affine pieces.

    The residue's dominant class is a counter whose overflow lap costs
    [Theta(2^j)]: the machine counts its whole range a second time, in the
    shifted frame, before the outer counter's msb bumps
    ([WAVE14_FINDINGS.md] section 2, measured).  Five waves of notes conclude
    that this is outside the certificate model, because
    [Checkers/LapDecider.v] carries a side's count as [a*j+b] and [srun]
    returns [ca*j+cb], both affine in [j].

    THAT IS TRUE OF ONE [srun] AND IT IS THE WRONG CONCLUSION.  The lap
    obligation never mentions the cost:

      LapStep tm Cf := forall p, exists n c', csteps tm n (Cf p) = Some c'
                              /\ lift c' = lift (Cf (Pos.succ p)) /\ 0 < n

    [exists n].  An exponential lap needs a PROOF that some [n] works, never a
    formula for it.  So the overflow branch decomposes into three pieces, none
    of which is exponential:

      boot   (affine)     Cc p     -> Cin v0        one ordinary chain
      inner  (INDUCTION)  Cin v0   -> Cin (fill v0) exists n, from [Hin]
      exit   (affine)     Cin (fill v0) -> Cc (Pos.succ p)  one ordinary chain

    and the exponential cost lives entirely inside the existential that the
    middle induction produces.  [2^j] is never written down.

    This is not a new count language.  It is the observation that the checker
    needs one new ability -- to CHAIN TO A SECOND ANCHOR FAMILY -- and that
    ability is a composition theorem, not a new step in [lstep].
    **[Checkers/LapDecider.v] is not touched by this file**: [sside], [sstep],
    [srun] and [srun_sound] are all unchanged, and the boot and exit chains are
    ordinary affine [srun]s fed through the existing soundness.

    PROVENANCE.  The 163 [IXP_*] boards already prove exponential overflow
    branches exactly this way, each carrying its own private copy of the
    induction ([inner_to_fill]) beside a hand-built boot and exit.  Wave-12
    wrote the first by hand; this file is that argument, once, generically in
    the two anchor families.

    ON [fill] RATHER THAN [reach_ovf].  [LapCertGlue.reach_ovf] runs interior
    laps until the counter overflows and returns the landing value
    EXISTENTIALLY.  Here the landing value must be named, because the exit
    chain has to be derived at it -- so the induction is stated as
    [Cin v -> Cin (fill v)], with [IXPGadgets.fill] naming the all-ones value
    of [v]'s width.  [fill] is applied to whatever value the boot lands on,
    NOT to [pow2 j]: wave-15's Stage A measured that 21% of these machines run
    their inner counter at a different octave or offset, and stating it this
    way costs nothing and covers them.

    Axiom footprint: [functional_extensionality_dep] only (inherited from
    [CTape]; this file adds none). *)

From Coq Require Import Arith Lia List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape MonoCounter JpCounter IXPGadgets.
Import ListNotations.

Section InnerFill.

Variable tm : TM.
Variable Cin : positive -> cconf.

(** The inner family's INTERIOR lap -- itself affine, so an ordinary
    certificate derives it.  Note it must close EXACTLY (no [lift] slack),
    which is what every emitted interior branch already does. *)
Hypothesis Hin : forall v i q0, cview v = (i, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cin v) = Some (Cin (Pos.succ v)).

(** Run inner interior laps until the inner counter is all ones.  This is the
    only place the exponential lives, and it is an existential.  Well-founded
    induction on [tovf], which strictly decreases along interior laps -- the
    same induction as [LapCertGlue.reach_ovf]. *)
Lemma inner_to_fill : forall v, exists n, csteps tm n (Cin v) = Some (Cin (fill v)).
Proof.
  intro v; remember (tovf v) as fuel eqn:Ef; revert v Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros v Ef.
  destruct (cview v) as [i oq] eqn:Ecv; destruct oq as [q0|].
  - assert (Hnz : tovf v <> 0).
    { intro H0. destruct (tovf0_allones v H0) as (jj & Hjj).
      rewrite Hjj in Ecv; discriminate. }
    destruct (Hin v i q0 Ecv) as (n & _ & Hrun).
    destruct (IH (tovf (Pos.succ v))
                 (ltac:(rewrite tovf_succ by lia; lia))
                 (Pos.succ v) eq_refl) as (k & Hk).
    exists (n + k). rewrite csteps_add, Hrun.
    rewrite (fill_succ v i q0 Ecv) in Hk. exact Hk.
  - destruct i as [|i'].
    { exfalso. destruct v; cbn in Ecv;
        [destruct (cview v); discriminate | discriminate | discriminate]. }
    exists 0. rewrite (fill_allones v i' Ecv). reflexivity.
Qed.

End InnerFill.

Section NestedOverflow.

Variable tm : TM.
Variable Cc Cin : positive -> cconf.

Hypothesis Hin : forall v i q0, cview v = (i, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cin v) = Some (Cin (Pos.succ v)).

(** One outer overflow anchor, and the inner value its boot lands on.  [v0]
    is a function of the outer index in practice; here it is just given, so
    the theorem says nothing about how the emitter found it. *)
Variable p v0 : positive.

Hypothesis Hboot : exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cin v0).
Hypothesis Hexit : exists n c', csteps tm n (Cin (fill v0)) = Some c' /\
                                lift c' = lift (Cc (Pos.succ p)).

(** The outer overflow branch, exactly as [LapGlue.glue_neverqh] and
    [LapGlueAbs.glue_qh_abs] consume it. *)
Theorem nested_overflow : exists n c', csteps tm n (Cc p) = Some c'
                                  /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  destruct Hboot as (nb & Hnb & Hb).
  destruct (inner_to_fill tm Cin Hin v0) as (ni & Hi).
  destruct Hexit as (ne & c' & He & Hlift).
  exists (nb + (ni + ne)), c'.
  split; [| split].
  - rewrite csteps_add, Hb, csteps_add, Hi. exact He.
  - exact Hlift.
  - lia.
Qed.

End NestedOverflow.
