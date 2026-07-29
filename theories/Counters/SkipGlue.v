(** * SkipGlue: anchor plumbing for SKIP counters.

    The "no overflow phase" bucket (WAVE26 section 8) is counters that NEVER
    REST AT A POWER OF TWO: the overflow sweep writes the LSB pair's data
    cell last, already incremented, so the overflow lap runs
    [fill (2^k - 1) -> 2^k + s] for a small machine-specific skip [s]
    (measured 1 or 2).  The anchor family therefore has VIRTUAL members at
    the skipped values -- the machine's real transient forms -- and the
    per-machine board defines

      Cc p = if p is skipped then VIRT p else E p ++ tail.

    This file is the plumbing that closes such a family with
    [LapGlue.glue_neverqh] directly:

    - [pexp]: the power-of-two view of [positive] ([pexp p = Some k] iff
      [p = pow2 k]), with the successor lemmas the board's case analysis
      needs ([pexp_succ_int]: an interior successor is never a power of
      two; [pexp_succ_fill]: an overflow successor always is);
    - [pexpi]: the [2^(S k) + 1] view, for the skip-2 machines' SECOND
      virtual anchor;
    - [reach_ovf_skip] / [vis_via_skip]: [LapCertGlue.reach_ovf] and
      [vis_via_ovf] with the interior-lap hypothesis GUARDED by "not a
      virtual anchor" and everything restricted to [p0 <= p], so the
      concrete small-[p] anchors (where the virtual forms degenerate)
      never have to carry laps at all.  Virtual anchors escape through
      their own laps -- stated up to [lift], chained in [stepn] space
      via [LapCertGlueLift.stepn_csteps_at]'s companions.

    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]);
    nothing new. *)

From Coq Require Import Arith Lia List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape MonoCounter JpCounter LapGlue
                                  LapCertGlue LapCertGlueLift IXPGadgets.
Import ListNotations.

(** ** The power-of-two view *)

Fixpoint pexp (p : positive) : option nat :=
  match p with
  | xH => Some 0
  | xO q => match pexp q with Some k => Some (S k) | None => None end
  | xI _ => None
  end.

Lemma pexp_pow2 : forall k, pexp (pow2 k) = Some k.
Proof. induction k; simpl; [reflexivity | rewrite IHk; reflexivity]. Qed.

Lemma pexp_some : forall p k, pexp p = Some k -> p = pow2 k.
Proof.
  induction p; intros k H; simpl in H.
  - discriminate.
  - destruct (pexp p) as [k'|] eqn:E; [|discriminate].
    injection H as <-. simpl. f_equal. exact (IHp k' eq_refl).
  - injection H as <-. reflexivity.
Qed.

Lemma pexp_zero : forall p, pexp p = Some 0 -> p = xH.
Proof.
  intros p H. exact (pexp_some p 0 H).
Qed.

Lemma pexp_shape : forall p k, pexp p = Some (S k) ->
  exists r, p = xO r /\ pexp r = Some k.
Proof.
  intros p k H. destruct p as [q|q|]; simpl in H.
  - discriminate.
  - destruct (pexp q) as [k'|] eqn:E; [|discriminate].
    injection H as <-. exists q. split; [reflexivity | exact E].
  - discriminate.
Qed.

(** The successor of a power of two ([2^(S k) + 1 = xI (pow2 k)]) is not
    a power of two. *)
Lemma pexp_succ_virt : forall p k, pexp p = Some (S k) ->
  pexp (Pos.succ p) = None.
Proof.
  intros p k H. destruct (pexp_shape p k H) as (r & -> & _). reflexivity.
Qed.

(** An interior successor is never a power of two: only an all-ones value
    overflows into one. *)
Lemma pexp_succ_int : forall p j q0, cview p = (j, Some q0) ->
  pexp (Pos.succ p) = None.
Proof.
  induction p; intros j q0 H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E. inversion H; subst j r.
    simpl. rewrite (IHp j' q0 eq_refl). reflexivity.
  - reflexivity.
  - discriminate.
Qed.

(** An overflow successor always is one: [cview p = (j, None)] says [p] is
    [j] ones, whose successor is [pow2 j]. *)
Lemma pexp_succ_fill : forall p j, cview p = (j, None) ->
  pexp (Pos.succ p) = Some j.
Proof.
  induction p; intros j H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E. inversion H; subst j r.
    simpl. rewrite (IHp j' eq_refl). reflexivity.
  - destruct (cview p) as [j' r]; discriminate.
  - inversion H; subst j. reflexivity.
Qed.

Lemma succ_fill_pow2 : forall p j, cview p = (j, None) ->
  Pos.succ p = pow2 j.
Proof.
  intros p j H. exact (pexp_some _ _ (pexp_succ_fill p j H)).
Qed.

(** ** The [2^(S k) + 1] view (skip-2's second virtual anchor) *)

Definition pexpi (p : positive) : option nat :=
  match p with xI q => pexp q | _ => None end.

Lemma pexpi_some : forall p k, pexpi p = Some k -> p = xI (pow2 k).
Proof.
  intros p k H. destruct p as [q|q|]; simpl in H; try discriminate.
  f_equal. exact (pexp_some q k H).
Qed.

(** The successor of [2^(S k) + 1]: at [k = 0] it is [4 = pow2 2]; at
    [k = S k'] it is [xO (xI (pow2 k'))], an ordinary anchor. *)
Lemma pexpi_succ_shape : forall p k, pexpi p = Some (S k) ->
  Pos.succ p = xO (xI (pow2 k)).
Proof.
  intros p k H. rewrite (pexpi_some p (S k) H). reflexivity.
Qed.

Lemma pexpi_succ_virt : forall p k, pexp p = Some (S k) ->
  pexpi (Pos.succ p) = Some k.
Proof.
  intros p k H. destruct (pexp_shape p k H) as (r & -> & Hr). exact Hr.
Qed.

Lemma pexpi_succ_int : forall p j q0, cview p = (j, Some q0) ->
  pexp p = None -> pexpi (Pos.succ p) = None.
Proof.
  intros p j q0 H Hx. destruct p as [q|q|]; simpl in *.
  - reflexivity.
  - destruct (pexp q); [discriminate | reflexivity].
  - discriminate.
Qed.

Lemma pexpi_succ_fill : forall p j, cview p = (j, None) ->
  pexpi (Pos.succ p) = None.
Proof.
  intros p j H. rewrite (succ_fill_pow2 p j H).
  destruct j; reflexivity.
Qed.

(** A [2^(S (S k)) + 1] anchor is interior-shaped, with one low set bit. *)
Lemma pexpi_cview : forall p k, pexpi p = Some (S k) ->
  cview p = (1, Some (pow2 k)).
Proof.
  intros p k H. rewrite (pexpi_some p (S k) H). reflexivity.
Qed.

(** A power of two above 2 never has the overflow (all-ones) shape. *)
Lemma pexp_not_fill : forall p j k, cview p = (S j, None) ->
  pexp p = Some (S k) -> False.
Proof.
  intros p j k Hc Hx.
  destruct (pexp_shape p k Hx) as (r & -> & _). cbn in Hc. discriminate.
Qed.

(** ** Reach and visits over a family with virtual anchors *)

Section SkipReach.

Variable tm : TM.
Variable Cc : positive -> cconf.
(** Which anchors are virtual (the machine's transient forms). *)
Variable virt : positive -> bool.
(** Anchors below [p0] carry no laps at all -- the boot lands at [p0]. *)
Variable p0 : positive.

(** The interior lap closes EXACTLY on every non-virtual anchor. *)
Hypothesis Hint : forall p j q0, (p0 <= p)%positive ->
  cview p = (j, Some q0) -> virt p = false ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).

(** A non-virtual interior anchor's successor is again non-virtual (its
    virtual anchors sit just above a power of two, i.e. just after an
    overflow). *)
Hypothesis Hsucc : forall p j q0, cview p = (j, Some q0) ->
  virt p = false -> virt (Pos.succ p) = false.

(** From any non-virtual anchor at or above [p0], the run reaches an
    OVERFLOW anchor exactly -- [LapCertGlue.reach_ovf] with the virtual
    anchors fenced off. *)
Lemma reach_ovf_skip : forall p, (p0 <= p)%positive -> virt p = false ->
  exists k p', csteps tm k (Cc p) = Some (Cc p')
               /\ (p0 <= p')%positive
               /\ exists j, cview p' = (S j, None).
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf);
    intros p Ef Hp Hv.
  destruct (cview p) as [j oq] eqn:Ecv; destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj).
      rewrite Hjj in Ecv; discriminate. }
    destruct (Hint p j q0 Hp Ecv Hv) as (n & Hn & Hrun).
    assert (Hp' : (p0 <= Pos.succ p)%positive).
    { eapply Pos.le_trans; [exact Hp|].
      apply Pos.lt_le_incl, Pos.lt_succ_diag_r. }
    destruct (IH (tovf (Pos.succ p))
                 (ltac:(rewrite tovf_succ by lia; lia))
                 (Pos.succ p) eq_refl Hp' (Hsucc p j q0 Ecv Hv))
      as (k & p' & Hk & Hpp' & Hj).
    exists (n + k), p'.
    split; [rewrite csteps_add, Hrun; exact Hk | split; [exact Hpp' | exact Hj]].
  - destruct (cview_pos p j Ecv) as (j' & ->).
    exists 0, p. split; [reflexivity | split; [exact Hp | exists j'; exact Ecv]].
Qed.

(** Every virtual anchor at or above [p0] has its own lap, up to [lift]. *)
Hypothesis Hvlap : forall p, (p0 <= p)%positive -> virt p = true ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).

(** At most two consecutive anchors at or above [p0] are virtual (skip 1
    or 2; below [p0] the skip-2 sets overlap at 2,3,4,5 and the bound is
    false, which is why it is guarded). *)
Hypothesis Hvrun : forall p, (p0 <= p)%positive -> virt p = true ->
  virt (Pos.succ p) = true -> virt (Pos.succ (Pos.succ p)) = false.

(** A state witnessed at every overflow anchor is visited from EVERY anchor
    at or above [p0]: non-virtual anchors chain interior laps to the next
    overflow ([reach_ovf_skip]); virtual anchors first escape through their
    own laps (one or two, in [stepn]/[lift] space) and continue from the
    non-virtual anchor they land on. *)
Lemma vis_via_skip : forall q : St,
  (forall p j, (p0 <= p)%positive -> cview p = (S j, None) ->
     exists k c, csteps tm k (Cc p) = Some c /\ fst c = q) ->
  forall p, (p0 <= p)%positive ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros q Hq.
  (* the non-virtual case, once *)
  assert (Hnv : forall p, (p0 <= p)%positive -> virt p = false ->
    exists k c, csteps tm k (Cc p) = Some c /\ fst c = q).
  { intros p Hp Hv.
    destruct (reach_ovf_skip p Hp Hv) as (k1 & p' & H1 & Hp' & (j & Hj)).
    destruct (Hq p' j Hp' Hj) as (k2 & c & H2 & Hc).
    exists (k1 + k2), c.
    split; [rewrite csteps_add, H1; exact H2 | exact Hc]. }
  (* one virtual lap, in stepn space *)
  assert (Hstep1 : forall p, (p0 <= p)%positive -> virt p = true ->
    exists n, 0 < n /\
      stepn tm n (lift (Cc p)) = Some (lift (Cc (Pos.succ p)))).
  { intros p Hp Hv.
    destruct (Hvlap p Hp Hv) as (n & c' & Hn & Hrun & Hl).
    exists n. split; [exact Hn|].
    rewrite (csteps_lift _ _ _ _ Hrun). f_equal. exact Hl. }
  intros p Hp.
  assert (Hps : (p0 <= Pos.succ p)%positive).
  { eapply Pos.le_trans; [exact Hp|].
    apply Pos.lt_le_incl, Pos.lt_succ_diag_r. }
  assert (Hpss : (p0 <= Pos.succ (Pos.succ p))%positive).
  { eapply Pos.le_trans; [exact Hps|].
    apply Pos.lt_le_incl, Pos.lt_succ_diag_r. }
  destruct (virt p) eqn:V1; [| exact (Hnv p Hp V1)].
  apply (vis_csteps_of_lift tm Cc).
  destruct (Hstep1 p Hp V1) as (n1 & _ & Hs1).
  destruct (virt (Pos.succ p)) eqn:V2.
  - (* two virtual laps, then non-virtual *)
    destruct (Hstep1 (Pos.succ p) Hps V2) as (n2 & _ & Hs2).
    destruct (vis_lift_of_csteps tm Cc _ q
                (Hnv (Pos.succ (Pos.succ p)) Hpss (Hvrun p Hp V1 V2)))
      as (k & e & Hk & He).
    exists (n1 + (n2 + k)), e. split; [| exact He].
    rewrite stepn_add, Hs1, stepn_add, Hs2. exact Hk.
  - (* one virtual lap, then non-virtual *)
    destruct (vis_lift_of_csteps tm Cc _ q (Hnv (Pos.succ p) Hps V2))
      as (k & e & Hk & He).
    exists (n1 + k), e. split; [| exact He].
    rewrite stepn_add, Hs1. exact Hk.
Qed.

End SkipReach.
