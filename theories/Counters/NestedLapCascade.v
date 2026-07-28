(** * NestedLapCascade: the overflow as a DESCENDING-OCTAVE CASCADE.

    `docs/CASCADE_EXIT.md`.  On the 72-machine exp-counter bucket (the "no
    exit chain" / "no boot chain" halves, measured EXPONENTIAL by WAVE18
    section 4b) one outer overflow phase is not one inner count, nor two, nor
    any fixed number.  It is

        level j     count 2^j .. 2^(j+1)-1        tail  head ++ rep u m
        level j-1   TWO counts, tail one unit longer
        ...
        level 0     TWO counts, tail j units longer
        closing sweep                             -> the outer successor

    with `2j+1` counts in all.  The step cost is `Theta(2^j)` -- section 4b's
    exponential, confirmed -- but what defeats [NestedLap2] is not the cost:
    it is that the NUMBER OF COUNTS IS AFFINE IN j.  [NestedLap2.boot_via_fill]
    folds ONE finished count into the next one's boot and composes with
    itself, so a board carrying it names its counts one by one; wave-22
    measured that route at 0 of 87 for exactly this reason, and
    `nestcert.MAXCOUNTS = 4` is where the naming stops.

    THE FIX IS AN INDUCTION OVER THE LEVEL, and the fractal lesson
    (`docs/HOLDOUTS_FRACTAL.md`: a carry of length m is not a gadget -- it IS
    the machine one level down) says why it closes.  Every level runs the
    SAME counter over the SAME digits; what changes is the opaque region past
    them, which grows by one unit per level and which the counter never reads.
    An [sside]'s [X] is already exactly that region, so the per-level chains
    are ordinary single-index chains and [Checkers/LapDecider.v] is not
    touched -- the same claim [NestedLap.v] makes for the flat nested branch.

    WHAT IS GENERIC HERE AND WHAT IS NOT.  Nothing below mentions a chain, a
    tail, an alphabet or [pow2]: the level step is a hypothesis, and this file
    is the composition -- descent, boot and close -- exactly as
    [NestedLapLift.nested_overflow_lift] is the composition of boot, inner and
    exit.  The emitter supplies the level step from four pieces (two counts,
    two chains), and [fill_hop] below is the shape it needs to do that.

    TWO INDICES, NOT ONE.  [D l m] carries the level AND the tail length
    separately.  They move together -- one level down is one octave off the
    count and one unit onto the tail -- so a single index would force
    [j - l] somewhere, and nat subtraction in an anchor is the wave-15
    index-shift trap in a new costume.  With both indices explicit every
    exponent is a plain [nat] built by [S], and the descent's arithmetic is
    the one lemma [k + S m = S k + m].

    Axiom footprint: [functional_extensionality_dep] only (inherited from
    [CTape.lift]; this file adds none). *)

From Coq Require Import Arith Lia List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape MonoCounter JpCounter IXPGadgets
                                  LapCertGlue LapCertGlueLift NestedLap
                                  NestedLapLift.
Import ListNotations.

(** ** Running one count out, at any tail *)

Section CountHop.

Variable tm : TM.

(** The inner family, parametrised by the TAIL its count carries.  Every level
    of the cascade is this one counter; only [T] differs, and the interior lap
    never reads [T] -- it is the chain's opaque region -- so ONE lap
    certificate discharges [Hin] at every level at once. *)
Variable Cin : list Sym -> positive -> cconf.

Hypothesis Hin : forall T v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin T v) = Some c'
               /\ lift c' = lift (Cin T (Pos.succ v)).

(** Run a count to its all-ones fill and carry on with whatever follows.

    This is the only shape the cascade needs [inner_to_fill_lift] in, because
    every level ENDS its counts with a chain rather than with an anchor: the
    [Theta(2^l)] disappears into [n] here and is never written down again. *)
Lemma fill_hop : forall T v e,
  (exists n, stepn tm n (lift (Cin T (fill v))) = Some e) ->
  exists n, stepn tm n (lift (Cin T v)) = Some e.
Proof.
  intros T v e (n & Hn).
  destruct (inner_to_fill_lift tm (Cin T) (Hin T) v) as (k & Hk).
  exists (k + n). rewrite stepn_add, Hk. exact Hn.
Qed.

(** One whole level: two counts with a chain between them, then a chain out.
    [vB]/[vA] are the two counts' starting values and [TB]/[TA] their tails;
    the two hypotheses are the level's two derived chains, run through
    [srun_sound] and the anchor glue.  Both counts cost [Theta(2^l)] and
    neither cost appears. *)
Lemma level_hop : forall TB TA vB vA e,
  (exists n, stepn tm n (lift (Cin TB (fill vB))) = Some (lift (Cin TA vA))) ->
  (exists n, stepn tm n (lift (Cin TA (fill vA))) = Some e) ->
  exists n, stepn tm n (lift (Cin TB vB)) = Some e.
Proof.
  intros TB TA vB vA e HBA HAB.
  apply fill_hop. destruct HBA as (n1 & H1).
  destruct (fill_hop TA vA e HAB) as (n2 & H2).
  exists (n1 + n2). rewrite stepn_add, H1. exact H2.
Qed.

End CountHop.

(** ** The descent *)

Section Descend.

Variable tm : TM.

(** [D l m] is the level-[l] entry configuration carrying [m] units of tail.
    The emitter instantiates it at the second count's anchor,
    [D l m := Cin (headB ++ rep unit (m + d0)) (pow2 l)], so that the boot
    lands on [D j d0] and the closing sweep starts from [D 0 (j + d0)]. *)
Variable D : nat -> nat -> cconf.

(** ONE level step, and it is the same step at every level -- that is the
    whole content of the cascade.  The emitter proves it once, from
    [level_hop] and two chains that are uniform in [l]. *)
Hypothesis Hstep : forall l m,
  exists n, stepn tm n (lift (D (S l) m)) = Some (lift (D l (S m))).

(** [k] levels of it.  The counts below are exponentially many and their cost
    is nowhere in the statement: [n] is an existential the induction builds,
    the same trick [NestedLap.inner_to_fill] plays one level down. *)
Lemma cascade_down : forall k l m,
  exists n, stepn tm n (lift (D (k + l) m)) = Some (lift (D l (k + m))).
Proof.
  induction k as [|k IH]; intros l m.
  - exists 0. reflexivity.
  - destruct (Hstep (k + l) m) as (n1 & H1).
    destruct (IH l (S m)) as (n2 & H2).
    exists (n1 + n2).
    replace (S k + l) with (S (k + l)) by lia.
    replace (S k + m) with (k + S m) by lia.
    rewrite stepn_add, H1. exact H2.
Qed.

(** All the way to the bottom, which is the only way the overflow branch uses
    it.  Stated separately so the caller never meets a stuck [k + 0]. *)
Lemma cascade_down_all : forall k m,
  exists n, stepn tm n (lift (D k m)) = Some (lift (D 0 (k + m))).
Proof.
  intros k m. destruct (cascade_down k 0 m) as (n & Hn).
  exists n. rewrite Nat.add_0_r in Hn. exact Hn.
Qed.

End Descend.

(** ** The overflow branch, composed *)

Section CascadeOverflow.

Variable tm : TM.
Variable Cc : positive -> cconf.
Variable D : nat -> nat -> cconf.

Hypothesis Hstep : forall l m,
  exists n, stepn tm n (lift (D (S l) m)) = Some (lift (D l (S m))).

(** [j] is the outer overflow index and [d0] the tail the top level already
    carries -- one unit on every machine measured so far, but the theorem does
    not care. *)
Variable p : positive.
Variable j d0 : nat.

(** The boot is an ordinary chain into the top level's anchor, up to [lift] --
    the same leniency [NestedLapLift] measured to be the binding one. *)
Hypothesis Hboot : exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
                               /\ lift c = lift (D j d0).

(** The closing sweep reads the whole grown tail, so unlike the per-level
    chains it is affine in [j] rather than in the level -- an ordinary chain
    at the outer index, landing on the outer successor. *)
Hypothesis Hclose : exists n,
  stepn tm n (lift (D 0 (j + d0))) = Some (lift (Cc (Pos.succ p))).

(** The outer overflow branch, exactly as [LapGlue.glue_neverqh],
    [LapGlueQH.glue_qh] and [LapGlueAbs.glue_qh_abs] consume it -- byte for
    byte what [nested_overflow_lift] produces, so a cascade board differs from
    a nested one only inside [lapo_]. *)
Theorem cascade_overflow :
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  destruct Hboot as (nb & cb & Hnb & Hb & Hbl).
  destruct (cascade_down_all tm D Hstep j d0) as (nd & Hd).
  destruct Hclose as (nc & Hc).
  assert (Hrest : stepn tm (nd + nc) (lift cb)
                  = Some (lift (Cc (Pos.succ p)))).
  { rewrite stepn_add, Hbl, Hd. exact Hc. }
  destruct (stepn_csteps_at tm (nd + nc) cb _ Hrest) as (cf & Hcf & Hcfl).
  exists (nb + (nd + nc)), cf. split; [| split].
  - rewrite csteps_add, Hb. exact Hcf.
  - exact Hcfl.
  - lia.
Qed.

End CascadeOverflow.

(** ** Visits through the cascade *)

Section CascadeVisit.

Variable tm : TM.
Variable Cc : positive -> cconf.
Variable D : nat -> nat -> cconf.

Hypothesis Hstep : forall l m,
  exists n, stepn tm n (lift (D (S l) m)) = Some (lift (D l (S m))).

(** A state that fires only in the CLOSING SWEEP -- after exponentially many
    counts across every level -- is still visited from the outer overflow
    anchor.  [vis_of_run] can see a prefix of one chain, and the closing sweep
    is not that chain, which is the same gap [NestedLapLift.vis_via_fill]
    fills for the flat nested branch.

    Stated at an arbitrary level [l], because a state may fire in some level's
    own transition rather than in the sweep; note [l = 0] is the one choice
    that is available at EVERY outer index, since the caller's obligation is
    universally quantified in [j] and the cascade at [j] reaches down to
    level 0 only. *)
Lemma cascade_vis_at : forall (q : St) (p : positive) (k l d0 : nat),
  (exists n c, csteps tm n (Cc p) = Some c /\ lift c = lift (D (k + l) d0)) ->
  (exists n e, stepn tm n (lift (D l (k + d0))) = Some e /\ fst e = q) ->
  exists n e, stepn tm n (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros q p k l d0 (nb & cb & Hb & Hbl) (nv & e & Hv & Hq).
  destruct (cascade_down tm D Hstep k l d0) as (nd & Hd).
  exists (nb + (nd + nv)), e. split; [| exact Hq].
  rewrite stepn_add, (csteps_lift _ _ _ _ Hb), Hbl, stepn_add, Hd.
  exact Hv.
Qed.

(** The common instance: the boot lands on level [j], the witness fires in the
    closing sweep at level 0. *)
Lemma cascade_vis : forall (q : St) (p : positive) (j d0 : nat),
  (exists n c, csteps tm n (Cc p) = Some c /\ lift c = lift (D j d0)) ->
  (exists n e, stepn tm n (lift (D 0 (j + d0))) = Some e /\ fst e = q) ->
  exists n e, stepn tm n (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros q p j d0 Hb Hv. apply (cascade_vis_at q p j 0 d0);
    [replace (j + 0) with j by lia | ]; assumption.
Qed.

End CascadeVisit.
