(** * LapCertGlue: the anchor-family plumbing every lap certificate needs.

    [Checkers/LapDecider.v] turns a certificate into the two lap branches
    (interior carry / overflow).  What is left is the bookkeeping the
    hand-written boards each re-proved:

    - [cview_pos]: [cview p = (0, None)] never happens, so the overflow
      branch always has the shape [(S j, None)];
    - [reach_ovf]: from ANY anchor the run reaches an OVERFLOW anchor, by
      well-founded induction on [JpCounter.tovf] (strictly decreasing along
      interior laps).  This needs the interior lap to close EXACTLY — which
      it does; only the overflow branch loses a trailing blank;
    - [vis_via_ovf]: therefore a state that only fires inside the overflow
      close is still visited from every anchor, which is what the [Hvis]
      premise of [LapGlue.glue_neverqh] asks for.

    Waves 8-12 wrote this induction once per machine ([reach_fin2] in every
    emitted board).  Here it is once. *)

From Coq Require Import Arith Lia List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape MonoCounter JpCounter.
Import ListNotations.

(** [cview p = (0, None)] is unreachable: [xH] gives [(1, None)], [xO]
    gives [Some], and [xI] gives a successor count. *)
Lemma cview_pos : forall p j, cview p = (j, None) -> exists j', j = S j'.
Proof.
  destruct p as [p|p|]; cbn; intros j H.
  - destruct (cview p) as [jj r]. inversion H. exists jj. lia.
  - discriminate.
  - inversion H. exists 0. lia.
Qed.

Section AnchorReach.

Variable tm : TM.
Variable Cc : positive -> cconf.

(** The interior lap closes EXACTLY (no trailing-blank slack).  Every emitted
    board has this: only the overflow branch needs [lift]. *)
Hypothesis Hint : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).

Lemma reach_ovf : forall p, exists k p',
  csteps tm k (Cc p) = Some (Cc p') /\ exists j, cview p' = (S j, None).
Proof.
  intro p; remember (tovf p) as fuel eqn:Ef; revert p Ef.
  induction fuel as [fuel IH] using (well_founded_induction lt_wf); intros p Ef.
  destruct (cview p) as [j oq] eqn:Ecv; destruct oq as [q0|].
  - assert (Hnz : tovf p <> 0).
    { intro H0. destruct (tovf0_allones p H0) as (jj & Hjj).
      rewrite Hjj in Ecv; discriminate. }
    destruct (Hint p j q0 Ecv) as (n & Hn & Hrun).
    destruct (IH (tovf (Pos.succ p))
                 (ltac:(rewrite tovf_succ by lia; lia))
                 (Pos.succ p) eq_refl) as (k & p' & Hk & Hj).
    exists (n + k), p'. split; [rewrite csteps_add, Hrun; exact Hk | exact Hj].
  - destruct (cview_pos p j Ecv) as (j' & ->).
    exists 0, p. split; [reflexivity | exists j'; exact Ecv].
Qed.

(** A state that only fires in the overflow close is still visited from every
    anchor: run interior laps until the counter overflows, then fire. *)
Lemma vis_via_ovf : forall q : St,
  (forall p j, cview p = (S j, None) ->
     exists k c, csteps tm k (Cc p) = Some c /\ fst c = q) ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros q Hq p.
  destruct (reach_ovf p) as (k1 & p' & H1 & (j & Hj)).
  destruct (Hq p' j Hj) as (k2 & c & H2 & Hc).
  exists (k1 + k2), c. split; [rewrite csteps_add, H1; exact H2 | exact Hc].
Qed.

End AnchorReach.
