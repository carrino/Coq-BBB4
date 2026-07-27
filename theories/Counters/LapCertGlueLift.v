(** * LapCertGlueLift: the anchor plumbing, restated up to [lift].

    [LapCertGlue.reach_ovf] chains INTERIOR laps by EXACT [cconf] equality:

      Hint : ... -> exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p))

    so a certificate whose interior branch lands one blank short of the next
    anchor cannot use it — even though [LapGlue.glue_neverqh]'s own lap
    premise is ALREADY stated up to [lift], and the emitted overflow branch
    already exploits that.  The asymmetry is an artefact of where the
    chaining happens, not a mathematical one: trailing blanks are invisible
    to [lift] ([CTape.lift_side l = fun n => nth n l S0]), and a lap that
    closes up to [lift] is exactly as good for the closer.

    Everything below is the same argument moved into [stepn]/[lift] space,
    where [LapGlue.glue_reach] already chains — [stepn_add] plus a rewrite by
    the lift equality.  Nothing in [LapCertGlue.v] or [LapGlue.v] changes, so
    every existing board is untouched; certificates whose interior closes
    exactly should keep using the exact route, which is strictly cheaper.

    Axiom footprint: whatever [CTape.lift] carries
    ([functional_extensionality_dep]); nothing new is introduced here. *)

From Coq Require Import Arith Lia List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape MonoCounter JpCounter LapGlue
                                  LapCertGlue.
Import ListNotations.

Section AnchorReachLift.

Variable tm : TM.
Variable Cc : positive -> cconf.

(** The interior lap, up to [lift].  Compare [LapCertGlue.Hint], which
    demands the reached configuration BE [Cc (Pos.succ p)]. *)
Hypothesis Hint : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).

(** From any anchor the run reaches an OVERFLOW anchor, up to [lift].  Same
    well-founded induction on [JpCounter.tovf] as [reach_ovf]; the interior
    laps are chained in [stepn] space so the blank slack never accumulates
    into a term mismatch. *)
Lemma reach_ovf_lift : forall p, exists k p',
  stepn tm k (lift (Cc p)) = Some (lift (Cc p'))
  /\ exists j, cview p' = (S j, None).
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.
  destruct (cview p) as [j oq] eqn:Ecv; destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj).
      rewrite Hjj in Ecv; discriminate. }
    destruct (Hint p j q0 Ecv) as (n & c' & Hn & Hrun & Hlift).
    destruct (IH (tovf (Pos.succ p))
                 (ltac:(rewrite tovf_succ by lia; lia))
                 (Pos.succ p) eq_refl) as (k & p' & Hk & Hj).
    exists (n + k), p'. split; [| exact Hj].
    rewrite stepn_add, (csteps_lift _ _ _ _ Hrun), Hlift. exact Hk.
  - destruct (cview_pos p j Ecv) as (j' & ->).
    exists 0, p. split; [reflexivity | exists j'; exact Ecv].
Qed.

(** A state that only fires inside the overflow close is still visited from
    every anchor.  The [lift] twin of [LapCertGlue.vis_via_ovf]. *)
Lemma vis_via_ovf_lift : forall q : St,
  (forall p j, cview p = (S j, None) ->
     exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q) ->
  forall p, exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros q Hq p.
  destruct (reach_ovf_lift p) as (k1 & p' & H1 & (j & Hj)).
  destruct (Hq p' j Hj) as (k2 & e & H2 & He).
  exists (k1 + k2), e. split; [rewrite stepn_add, H1; exact H2 | exact He].
Qed.

End AnchorReachLift.

(** ** The closer, with the visit premise in [lift] space

    [LapGlue.glue_neverqh] asks for [Hvis] as a CONCRETE [csteps] run from
    [Cf p].  Its proof immediately pushes that through [csteps_lift], so the
    concreteness is never used — this is the same theorem with the premise
    weakened to what the proof actually consumes.  [LapGlue.glue_reach] is
    reused verbatim, so the lap side is unchanged. *)
Theorem glue_neverqh_lift : forall (tm : TM) (Cf : positive -> cconf) p0,
  (exists t0, stepn tm t0 InitES = Some (lift (Cf p0))) ->
  (forall p, (p0 <= p)%positive ->
     exists n c', csteps tm n (Cf p) = Some c'
                  /\ lift c' = lift (Cf (Pos.succ p)) /\ 0 < n) ->
  (forall p q, (p0 <= p)%positive ->
     exists k e, stepn tm k (lift (Cf p)) = Some e /\ fst e = q) ->
  NeverQuasiHaltsSt tm.
Proof.
  intros tm Cf p0 Hboot Hlap Hvis q _ N.
  destruct (glue_reach tm Cf p0 Hboot Hlap N) as (T & p & Hp & HN & Hstep).
  destruct (Hvis p q Hp) as (k & e & He & Hqe).
  exists (T + k). split; [lia|].
  exists e. split; [rewrite stepn_add, Hstep; exact He | exact Hqe].
Qed.

(** A concrete visit witness is a [lift] one; this is how a board that only
    needs the interior slack keeps its existing per-state [srun_st] proofs. *)
Lemma vis_lift_of_csteps : forall (tm : TM) (Cc : positive -> cconf) p q,
  (exists k c, csteps tm k (Cc p) = Some c /\ fst c = q) ->
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros tm Cc p q (k & c & Hk & Hq).
  exists k, (lift c). split; [apply csteps_lift; exact Hk |].
  rewrite lift_state; exact Hq.
Qed.

(** ** …and back again

    [CTape.stepn_csteps] says a blank-start run is computable; the same
    induction works from ANY concrete configuration, because [cstep] fails
    exactly where [step] does ([CTape.cstep_lift_rev]).  Consequence, and it
    is what keeps [glue_qh] / [glue_qh_abs] from needing [lift] twins of their
    own: a visit witness in [stepn] space can be pulled back to the CONCRETE
    [csteps] premise those closers ask for.  Only the LAP has to be weakened
    ([reach_ovf_lift] above), because chaining laps needs the reached
    configuration to BE the next anchor, not merely to lift to it. *)
Lemma stepn_csteps_at : forall (tm : TM) m cc e,
  stepn tm m (lift cc) = Some e ->
  exists cc', csteps tm m cc = Some cc' /\ lift cc' = e.
Proof.
  induction m; intros cc e H.
  - simpl in H. injection H as <-. exists cc. split; reflexivity.
  - cbn [stepn] in H.
    destruct (step tm (lift cc)) as [c1|] eqn:Estep; [|discriminate].
    destruct (cstep_lift_rev tm cc c1 Estep) as (cc1 & Hcc1 & Hl1).
    rewrite <- Hl1 in H.
    destruct (IHm cc1 e H) as (cc' & Hcc' & Hl').
    exists cc'. split; [| exact Hl'].
    cbn [csteps]. rewrite Hcc1. exact Hcc'.
Qed.

Lemma vis_csteps_of_lift : forall (tm : TM) (Cc : positive -> cconf) p q,
  (exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros tm Cc p q (k & e & Hk & Hq).
  destruct (stepn_csteps_at tm k (Cc p) e Hk) as (c & Hc & Hl).
  exists k, c. split; [exact Hc |].
  rewrite <- lift_state, Hl. exact Hq.
Qed.
