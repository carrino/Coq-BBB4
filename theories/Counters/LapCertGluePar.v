(** * LapCertGluePar: a visit witnessed at ONE octave parity is enough

    [LapCertGlueLift.vis_via_ovf_lift] asks for a witness at EVERY overflow
    anchor.  A TWO-FORM board (`tools/counters/tailcert.py`) has two overflow
    arms -- one per octave parity -- and they are genuinely different runs: a
    state can fire in the parity-0 arm and nowhere in the parity-1 one, which
    files the row at `no visit witness for state <q> at octave parity <b>`
    even though the state is plainly live.

    It is enough to witness it at ONE parity, because the overflow anchors
    ALTERNATE.  From any anchor, [reach_ovf_lift] runs to an overflow anchor
    using INTERIOR laps only, and [RegGlue.podd_succ_int] says an interior
    increment never leaves its octave -- so the overflow anchor it lands on
    carries the parity it started with ([reach_ovf_par_lift] below is that
    same induction with the parity carried along).  If that is the wrong
    parity, ONE more lap crosses into the next octave
    ([RegGlue.podd_succ_fill] flips it) and the overflow anchor after it
    carries the parity we want.

    So the premise weakens from "a witness at every overflow anchor" to "a
    witness at every overflow anchor of parity [beta]", at the cost of the
    FULL lap [Hlap] -- which every board already proves as its [lap_*].

    Axiom footprint: whatever [CTape.lift] carries
    ([functional_extensionality_dep]); nothing new is introduced here. *)

From Coq Require Import Arith Bool Lia List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape MonoCounter JpCounter LapGlue
                                  LapCertGlue LapCertGlueLift IXPGadgets
                                  RegGlue.
Import ListNotations.

Section AnchorReachPar.

Variable tm : TM.
Variable Cc : positive -> cconf.

(** The INTERIOR lap, up to [lift] -- the board's [lapi_*]. *)
Hypothesis Hint : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).

(** The OVERFLOW lap -- the board's [lapo_*].  Stated exactly where the
    two-form boards prove it, i.e. at [cview p = (S (S j), None)]: the peel's
    leftover anchor [p = 1] carries [cview p = (S 0, None)] and no board
    proves a lap there.  It is not needed: [2 <= p] is preserved along the
    run, and an overflow anchor [2 <= p'] always has index [S (S j)]. *)
Hypothesis Hovf : forall p j, cview p = (S (S j), None) ->
  exists n c', csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.

(** [LapCertGlueLift.reach_ovf_lift], with the octave parity -- and the
    monotonicity of the anchor index -- carried along. *)
Lemma reach_ovf_par_lift : forall p, exists k p',
  stepn tm k (lift (Cc p)) = Some (lift (Cc p'))
  /\ (exists j, cview p' = (S j, None))
  /\ podd p' = podd p /\ (p <= p')%positive.
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
                 (Pos.succ p) eq_refl) as (k & p' & Hk & Hj & Hpar & Hle).
    exists (n + k), p'. split; [| split; [exact Hj | split]].
    + rewrite stepn_add, (csteps_lift _ _ _ _ Hrun), Hlift. exact Hk.
    + rewrite Hpar. exact (podd_succ_int p j q0 Ecv).
    + apply Pos.le_trans with (Pos.succ p); [| exact Hle].
      apply Pos.lt_le_incl, Pos.lt_succ_diag_r.
  - destruct (cview_pos p j Ecv) as (j' & ->).
    exists 0, p. split; [reflexivity |].
    split; [exists j'; exact Ecv | split; [reflexivity | apply Pos.le_refl]].
Qed.

(** An overflow anchor at or above 2 has index [S (S j)]: index [S 0] is the
    anchor [p = 1] and nothing else ([IXPGadgets.cview_none_shape]). *)
Lemma ovf_index_pos : forall p j, cview p = (S j, None) -> (2 <= p)%positive ->
  exists j', j = S j'.
Proof.
  intros p [|j] E Hp; [| exists j; reflexivity].
  exfalso. rewrite (cview_none_shape p 0 E) in Hp.
  apply Hp. vm_compute. reflexivity.
Qed.

(** The weakened visit premise: ONE octave parity is enough. *)
Lemma vis_via_ovf_par_lift : forall (beta : bool) (q : St),
  (forall p j, cview p = (S (S j), None) -> podd p = beta ->
     exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q) ->
  forall p, (2 <= p)%positive ->
    exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros beta q Hq p Hp.
  destruct (reach_ovf_par_lift p) as (k1 & p' & H1 & (j & Hj) & _ & Hle).
  assert (Hp' : (2 <= p')%positive) by (apply Pos.le_trans with p; assumption).
  destruct (ovf_index_pos p' j Hj Hp') as (j' & ->).
  destruct (bool_dec (podd p') beta) as [Hb|Hb].
  - destruct (Hq p' j' Hj Hb) as (k2 & e & H2 & He).
    exists (k1 + k2), e. split; [rewrite stepn_add, H1; exact H2 | exact He].
  - (* the wrong parity: take the OVERFLOW lap, which crosses into the next
       octave, then run on to THAT octave's overflow anchor. *)
    assert (Hflip : podd (Pos.succ p') = beta).
    { rewrite (podd_succ_fill p' (S j') Hj).
      destruct (podd p'), beta; cbn in *; congruence. }
    destruct (Hovf p' j' Hj) as (n & c' & Hrun & Hlift & _).
    destruct (reach_ovf_par_lift (Pos.succ p'))
      as (k2 & p'' & H2 & (j2 & Hj2) & Hpar2 & Hle2).
    assert (Hp'' : (2 <= p'')%positive).
    { apply Pos.le_trans with (Pos.succ p'); [| exact Hle2].
      apply Pos.le_trans with p'; [exact Hp' |].
      apply Pos.lt_le_incl, Pos.lt_succ_diag_r. }
    destruct (ovf_index_pos p'' j2 Hj2 Hp'') as (j2' & ->).
    destruct (Hq p'' j2' Hj2 (eq_trans Hpar2 Hflip)) as (k3 & e & H3 & He).
    exists (k1 + (n + (k2 + k3))), e. split; [| exact He].
    rewrite stepn_add, H1, stepn_add, (csteps_lift _ _ _ _ Hrun), Hlift.
    rewrite stepn_add, H2. exact H3.
Qed.

End AnchorReachPar.
