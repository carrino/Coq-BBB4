(** * LapGlueQHTr: monotone-counter laps on the QUASIHALTING side.

    [LapGlueTr.glue_neverqhtr] closes a counter to [NeverQuasiHaltsTr]
    by running the whole lap argument on the wrapped machine
    [tm_wrap_trs tm pins] from the blank tape, [pins] being the
    instructions that never fire.  A quiet-instruction counter
    (SCOPING_INSTR.md 7.3a: a LIVE-class machine whose initial
    transition, typically A0, is never taken again) fires its dead
    instructions in the boot prefix, so the wrapped machine would halt
    there.  Here the boot runs on the ORIGINAL machine, up to a boot
    index [t0] with configuration [Cf p0], and only the laps and the
    per-instruction fires run on the wrapped machine from there:

    - the wrapped run from [Cf p0] never halts (the laps chain
      forever), so by [WrapTr.wrap_trs_agree] it IS the original
      machine's run from index [t0] and no pinned instruction fires
      at any index >= t0: a pinned instruction's last fire is before
      [t0];
    - every unpinned instruction fires from every anchor, so it fires
      after any index;
    - a pinned instruction that fired in the prefix is a quasihalt
      witness.

    Conclusion: [NonHalt], the unfolded [QHBoundTr t0] and
    [QuasiHaltsTr] -- the shape [provqh_tr] needs.  Every board lemma
    of the never-QH counter boards (laps, fires) is reused as is; only
    the boot lemma and the closer change. *)

From Coq Require Import Arith Lia List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr.
From BBB4.Checkers Require Import WrapTr LapDecider TCyclerQHTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import WTape MonoCounter JpCounter LapGlue LapCertGlue LapGlueTr.
Import ListNotations.

Section GlueQHTr.

Variable tm : TM.
Variable pins : list Instr.       (** claimed never to fire after the boot *)
Variable Cf : positive -> cconf.
Variable p0 : positive.
Variable t0 : nat.                (** the boot index *)

(** the boot, on the ORIGINAL machine (the lifted form the boards'
    boot lemmas produce) *)
Hypothesis Hboot : stepn tm t0 InitES = Some (lift (Cf p0)).
(** the laps and the fires, on the WRAPPED machine, from the anchors *)
Hypothesis Hlap : forall p, (p0 <= p)%positive ->
  exists n c', csteps (tm_wrap_trs tm pins) n (Cf p) = Some c' /\
               lift c' = lift (Cf (Pos.succ p)) /\ 0 < n.
Hypothesis Hfire : forall t, ~ In t pins -> forall p, (p0 <= p)%positive ->
  exists k c, csteps (tm_wrap_trs tm pins) k (Cf p) = Some c /\ cinstr c = t.
(** some pinned instruction fired in the prefix (the quasihalt witness) *)
Hypothesis Hwit : existsb (fun tg => cfires tm c0 t0 tg) pins = true.

Let tmw := tm_wrap_trs tm pins.
Let cb := lift (Cf p0).

Lemma reach_from : forall k, exists T p, (p0 <= p)%positive /\ k <= T /\
  stepn tmw T cb = Some (lift (Cf p)).
Proof.
  induction k.
  - exists 0, p0. split; [apply Pos.le_refl|]. split; [lia | reflexivity].
  - destruct IHk as (T & p & Hp & HT & Hstep).
    destruct (Hlap p Hp) as (n & c' & Hrun & Hlift & Hn).
    exists (T + n), (Pos.succ p).
    split.
    { eapply Pos.le_trans; [exact Hp|]. apply Pos.lt_le_incl, Pos.lt_succ_diag_r. }
    split; [lia|].
    rewrite stepn_add, Hstep. rewrite <- Hlift.
    apply csteps_lift; exact Hrun.
Qed.

Lemma wrapped_nonhalt_from : forall n, stepn tmw n cb <> None.
Proof.
  intro n.
  destruct (reach_from n) as (T & p & _ & HT & Hstep).
  destruct (stepn_prefix tmw n T cb _ HT Hstep) as (cm & Hcm & _).
  rewrite Hcm. discriminate.
Qed.

Lemma agree_from : forall k,
  stepn tmw k cb = stepn tm k cb /\
  (forall c', stepn tm k cb = Some c' -> ~ In (instr_of c') pins).
Proof. exact (wrap_trs_agree tm pins cb wrapped_nonhalt_from). Qed.

Lemma boot_lift : stepn tm t0 InitES = Some cb.
Proof. exact Hboot. Qed.

(** the original run past the boot is the wrapped run from the boot *)
Lemma run_from : forall n, t0 <= n ->
  stepn tm n InitES = stepn tmw (n - t0) cb.
Proof.
  intros n Hn.
  replace n with (t0 + (n - t0)) at 1 by lia.
  rewrite stepn_add, boot_lift.
  destruct (agree_from (n - t0)) as [Heq _]. symmetry. exact Heq.
Qed.

Lemma pinned_quiet : forall tg, In tg pins ->
  forall n, t0 <= n -> ~ FiresAt tm tg n.
Proof.
  intros tg Hin n Hn (c & Hc & Ht).
  rewrite run_from in Hc by exact Hn.
  destruct (agree_from (n - t0)) as [Heq Hnot].
  rewrite Heq in Hc.
  apply (Hnot c Hc). rewrite Ht. exact Hin.
Qed.

Lemma unpinned_live : forall tg, ~ In tg pins ->
  forall N, exists n, N <= n /\ FiresAt tm tg n.
Proof.
  intros tg Hnp N.
  destruct (reach_from N) as (T & p & Hp & HT & Hstep).
  destruct (Hfire tg Hnp p Hp) as (k & ck & Hk & Hck).
  exists (t0 + T + k). split; [lia|].
  exists (lift ck). split.
  - rewrite run_from by lia.
    replace (t0 + T + k - t0) with (T + k) by lia.
    rewrite stepn_add, Hstep. apply csteps_lift; exact Hk.
  - rewrite cinstr_lift. exact Hck.
Qed.

Theorem glue_qhboundtr :
  NonHalt tm
  /\ (forall tg s, QuietAfterTr tm tg s -> S s <= t0)
  /\ QuasiHaltsTr tm.
Proof.
  split.
  { intros n HN.
    destruct (le_lt_dec t0 n) as [Hge | Hlt].
    - rewrite run_from in HN by exact Hge.
      exact (wrapped_nonhalt_from (n - t0) HN).
    - destruct (stepn_prefix tm n t0 InitES cb) as (cm & Hcm & _);
        [lia | exact boot_lift |].
      rewrite Hcm in HN. discriminate. }
  split.
  - intros tg s [Hs Hafter].
    destruct (tr_inb tg pins) eqn:E.
    + apply tr_inb_spec in E.
      destruct (le_lt_dec t0 s) as [Hge | Hlt]; [|lia].
      exfalso. exact (pinned_quiet tg E s Hge Hs).
    + assert (Hnin : ~ In tg pins).
      { intro Hin. apply tr_inb_spec in Hin. rewrite Hin in E. discriminate. }
      destruct (unpinned_live tg Hnin (S s)) as (n & Hn & Hf).
      exfalso. apply (Hafter n); [lia | exact Hf].
  - apply existsb_exists in Hwit as (tg & Hin & Hpre).
    destruct (cfires_sound _ _ _ _ Hpre) as (i & ci & Hi & Hs & Hq).
    exists tg. split.
    + exists i, (lift ci). split.
      * rewrite <- lift_c0. apply csteps_lift; exact Hs.
      * rewrite cinstr_lift. exact Hq.
    + exists t0. intros n Hn. exact (pinned_quiet tg Hin n Hn).
Qed.

End GlueQHTr.
