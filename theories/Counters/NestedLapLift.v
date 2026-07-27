(** * NestedLapLift: the nested overflow branch, with the BOOT and the INNER
    lap stated up to [lift].

    [NestedLap.nested_overflow] chains its three pieces by EXACT [cconf]
    equality on the two inner joints:

      Hboot : csteps tm n (Cc p)          = Some (Cin v0)
      Hin   : csteps tm n (Cin v)         = Some (Cin (Pos.succ v))

    Wave-16 measured that this is the same over-strictness the flat emitter
    carried for five waves ([docs/WAVE16_FINDINGS.md] section 2): a derived
    chain lands one or two TRAILING BLANKS past the anchor, and
    [CTape.lift_side l = fun n => nth n l S0] cannot see them.  Only the
    joint's syntactic form wants them gone; the lap obligation
    ([LapDecider.LapStep], [LapGlue]'s [Hlap]) never did.

    MEASURED for THIS branch (`tools/counters/nestboot2.py`, 30 machines of
    the `AFFINE`/`EXP2` bucket, K = 6):

      key enumeration only, exact joints (= wave-15's `nestboot.py`)   7 / 30
      key enumeration + the [lift] joints                             17 / 30

    and on all 17 the inner family's own interior lap derives too, so the
    [lift] joints are the binding constraint on the whole Stage-C population,
    not just on the boot.

    Everything below is [NestedLap]'s argument moved into [stepn]/[lift]
    space -- the same move [Counters/LapCertGlueLift.v] makes for
    [LapCertGlue.reach_ovf] -- and pulled back to a [csteps] run ONCE at the
    end, by [LapCertGlueLift.stepn_csteps_at].  [Checkers/LapDecider.v] is
    untouched, [NestedLap.v] is untouched, and boards whose joints close
    exactly should keep using [nested_overflow], which is strictly cheaper.

    Axiom footprint: [functional_extensionality_dep] only (inherited from
    [CTape.lift]; this file adds none). *)

From Coq Require Import Arith Lia List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape MonoCounter JpCounter IXPGadgets
                                  LapCertGlue LapCertGlueLift NestedLap.
Import ListNotations.

(** ** The inner family's landing value is an overflow anchor

    [IXPGadgets.cview_none_shape] reads the outer overflow index off the
    anchor; the emitter needs the converse for the INNER family, because the
    exit chain is derived at [fill (pow2 j)] and its glue is the alphabet
    module's [cview_none_*] lemma, which asks for [cview _ = (S j, None)]. *)
Lemma cview_fill_pow2 : forall j, cview (fill (pow2 j)) = (S j, None).
Proof.
  induction j as [|j IH]; [reflexivity|].
  cbn [pow2 fill cview]. rewrite IH. reflexivity.
Qed.

Section InnerFillLift.

Variable tm : TM.
Variable Cin : positive -> cconf.

(** The inner family's INTERIOR lap, up to [lift].  Compare
    [NestedLap.Hin], which demands the reached configuration BE
    [Cin (Pos.succ v)]. *)
Hypothesis Hin : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).

(** Run inner interior laps until the inner counter is all ones.  The
    exponential cost of the overflow lives entirely inside this existential;
    [2 ^ j] is never written down.  Same well-founded induction on
    [JpCounter.tovf] as [NestedLap.inner_to_fill], chained in [stepn] space so
    the blank slack cannot accumulate into a term mismatch. *)
Lemma inner_to_fill_lift : forall v,
  exists n, stepn tm n (lift (Cin v)) = Some (lift (Cin (fill v))).
Proof.
  intro v; remember (tovf v) as fuel eqn:Ef; revert v Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros v Ef.
  destruct (cview v) as [i oq] eqn:Ecv; destruct oq as [q0|].
  - assert (Hnz : tovf v <> 0).
    { intro H0. destruct (tovf0_allones v H0) as (jj & Hjj).
      rewrite Hjj in Ecv; discriminate. }
    destruct (Hin v i q0 Ecv) as (n & c' & _ & Hrun & Hlift).
    destruct (IH (tovf (Pos.succ v))
                 (ltac:(rewrite tovf_succ by lia; lia))
                 (Pos.succ v) eq_refl) as (k & Hk).
    exists (n + k).
    rewrite stepn_add, (csteps_lift _ _ _ _ Hrun), Hlift.
    rewrite (fill_succ v i q0 Ecv) in Hk. exact Hk.
  - destruct i as [|i'].
    { exfalso. destruct v; cbn in Ecv;
        [destruct (cview v); discriminate | discriminate | discriminate]. }
    exists 0. rewrite (fill_allones v i' Ecv). reflexivity.
Qed.

End InnerFillLift.

Section NestedOverflowLift.

Variable tm : TM.
Variable Cc Cin : positive -> cconf.

Hypothesis Hin : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).

(** A state that fires inside the EXIT half of the overflow -- i.e. from the
    inner counter's all-ones fill, after the exponentially many inner laps --
    is still visited from the outer overflow anchor.

    The emitter needs this: the overflow lap of a nested machine is boot +
    inner + exit, and [vis_of_run] can only see a prefix of ONE chain.  A
    state occurring solely in the exit chain has no witness in the boot, and
    that is measured to be the common case (8 of 30 on the sample). *)
Lemma vis_via_fill : forall (q : St) (p v0 : positive),
  (exists n c, csteps tm n (Cc p) = Some c /\ lift c = lift (Cin v0)) ->
  (exists k e, stepn tm k (lift (Cin (fill v0))) = Some e /\ fst e = q) ->
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros q p v0 (n & c & Hn & Hl) (k & e & Hk & Hq).
  destruct (inner_to_fill_lift tm Cin Hin v0) as (ni & Hi).
  exists (n + (ni + k)), e. split; [| exact Hq].
  rewrite stepn_add, (csteps_lift _ _ _ _ Hn), Hl, stepn_add, Hi. exact Hk.
Qed.

Variable p v0 : positive.

(** The boot lands ON the inner anchor only up to [lift] -- which is what the
    derived chain gives whenever it stops one blank past it. *)
Hypothesis Hboot : exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
                               /\ lift c = lift (Cin v0).
Hypothesis Hexit : exists n c', csteps tm n (Cin (fill v0)) = Some c' /\
                                lift c' = lift (Cc (Pos.succ p)).

(** The outer overflow branch, exactly as [LapGlue.glue_neverqh],
    [LapGlueQH.glue_qh] and [LapGlueAbs.glue_qh_abs] consume it. *)
Theorem nested_overflow_lift :
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  destruct Hboot as (nb & cb & Hnb & Hb & Hbl).
  destruct (inner_to_fill_lift tm Cin Hin v0) as (ni & Hi).
  destruct Hexit as (ne & ce & He & Hel).
  (* the inner run and the exit, composed on the LIFTED boot landing *)
  assert (Hrest : stepn tm (ni + ne) (lift cb) = Some (lift ce)).
  { rewrite stepn_add, Hbl, Hi. exact (csteps_lift _ _ _ _ He). }
  destruct (stepn_csteps_at tm (ni + ne) cb (lift ce) Hrest)
    as (cf & Hcf & Hcfl).
  exists (nb + (ni + ne)), cf. split; [| split].
  - rewrite csteps_add, Hb. exact Hcf.
  - rewrite Hcfl. exact Hel.
  - lia.
Qed.

End NestedOverflowLift.
