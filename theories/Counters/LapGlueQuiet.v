(** * LapGlueQuiet: laps that AVOID a state imply bounded quasihalting.

    The closer for the residue's "no visit witness (StA is targeted)"
    machines (docs/WAVE16_FINDINGS.md section 6b): genuine quasihalters whose
    quiet state IS a transition target, so [LapGlueQH.glue_qh]'s syntactic
    [Huntarget] is false — the targeting transition simply never fires after
    the bootstrap.  [LapGlueAbs.glue_qh_abs] cannot take them either: its
    [closed_b] is a DIGRAPH fact over all symbols, and any set holding the
    targeting state must hold the quiet one.

    The fact that IS true is trajectory-level, and the lap certificates
    already carry it: the chains are a faithful forward model (mxdys'
    condition — "my inductive decider can only decide a TM when it can model
    the forward behavior exactly"), so whether the quiet state ever fires
    inside a lap is COMPUTABLE from the certificate.  [Checkers/LapAvoid.v]
    computes it; this file consumes it:

    - [AvoidRun tm qa n c]: no configuration in the first [n] steps from [c]
      is in state [qa];
    - [glue_qh_quiet]: a bootstrap reaching the anchor at a CONCRETE index
      [t0], laps that all avoid [qa], visits for every other state, one
      checked visit of [qa] at [s0], and a checked [qa]-free window
      [(s0, t0)] give [NonHalt /\ QHBound (S s0) /\ QuasiHaltsSt] — the
      R_QH triple with the exact last-visit bound.

    The run from index [t0] on is exactly the concatenation of the laps
    ([LapGlue.glue_reach]'s induction, kept at the [lift] level so overflow
    laps may close up to a trailing blank), so [qa]-freedom of every lap
    covers every index [>= t0]; the finite window [(s0, t0)] is checked by
    computation ([cavoid]); nothing before [s0] matters, because [s0] is a
    visit and [QuietAfter] only bounds visits AFTER the last one.

    Axiom footprint: [functional_extensionality_dep] only (inherited from
    [CTape]; this file adds none). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import LapGlue.
From BBB4.Census Require Import TNF_QH.
Import ListNotations.

(** ** Runs that avoid a state *)

Definition AvoidRun (tm : TM) (qa : St) (n : nat) (c : cconf) : Prop :=
  forall m cm, m < n -> csteps tm m c = Some cm -> fst cm <> qa.

Lemma avoid_0 : forall tm qa c, AvoidRun tm qa 0 c.
Proof. intros tm qa c m cm Hm _. lia. Qed.

Lemma avoid_add : forall tm qa n1 n2 c c1,
  csteps tm n1 c = Some c1 ->
  AvoidRun tm qa n1 c -> AvoidRun tm qa n2 c1 ->
  AvoidRun tm qa (n1 + n2) c.
Proof.
  intros tm qa n1 n2 c c1 Hc H1 H2 m cm Hm Hstep.
  destruct (Nat.lt_ge_cases m n1) as [Hlt | Hge].
  - exact (H1 m cm Hlt Hstep).
  - replace m with (n1 + (m - n1)) in Hstep by lia.
    rewrite csteps_add, Hc in Hstep.
    apply (H2 (m - n1) cm); [lia | exact Hstep].
Qed.

Lemma st_neq_of_negb : forall q qa : St, negb (st_eqb q qa) = true -> q <> qa.
Proof.
  intros q qa H E. rewrite E in H.
  rewrite (proj2 (st_eqb_spec qa qa) eq_refl) in H. discriminate.
Qed.

(** ** The concrete checker for the bootstrap window *)

Fixpoint cavoid (tm : TM) (qa : St) (n : nat) (c : cconf) : bool :=
  match n with
  | 0 => true
  | S m => negb (st_eqb (fst c) qa)
           && match cstep tm c with
              | Some c' => cavoid tm qa m c'
              | None => false
              end
  end.

Lemma cavoid_sound : forall tm qa n c,
  cavoid tm qa n c = true -> AvoidRun tm qa n c.
Proof.
  intros tm qa n; induction n as [|n IH]; intros c H m cm Hm Hstep.
  - lia.
  - cbn in H. apply andb_true_iff in H as [Hq H].
    destruct (cstep tm c) as [c'|] eqn:E; [|discriminate].
    destruct m as [|m'].
    + cbn in Hstep. injection Hstep as <-. exact (st_neq_of_negb _ _ Hq).
    + cbn in Hstep. rewrite E in Hstep.
      apply (IH c' H m' cm); [lia | exact Hstep].
Qed.

(** A concrete visit witness from the blank tape. *)
Lemma visits_at_c0 : forall tm q s c,
  csteps tm s c0 = Some c -> fst c = q -> VisitsAt tm q s.
Proof.
  intros tm q s c H Hq.
  exists (lift c). split.
  - rewrite <- lift_c0. apply csteps_lift. exact H.
  - rewrite lift_state. exact Hq.
Qed.

(** The whole bootstrap-window obligation as ONE boolean: run to index [k],
    then check [d] states.  A board discharges it by [vm_compute]. *)
Definition bootquiet_chk (tm : TM) (qa : St) (k d : nat) : bool :=
  match csteps tm k c0 with
  | Some c1 => cavoid tm qa d c1
  | None => false
  end.

Lemma bootquiet_chk_sound : forall tm qa k d,
  bootquiet_chk tm qa k d = true ->
  forall n c, k <= n < k + d -> stepn tm n InitES = Some c -> fst c <> qa.
Proof.
  unfold bootquiet_chk; intros tm qa k d H n c Hn Hstep.
  destruct (csteps tm k c0) as [c1|] eqn:E; [|discriminate].
  destruct (stepn_csteps tm n c Hstep) as (cc & Hcc & Hlift).
  replace n with (k + (n - k)) in Hcc by lia.
  rewrite csteps_add, E in Hcc.
  rewrite <- Hlift, lift_state.
  exact (cavoid_sound tm qa d c1 H (n - k) cc ltac:(lia) Hcc).
Qed.

(** The visit witness, same shape. *)
Definition bootvis_chk (tm : TM) (qa : St) (s : nat) : bool :=
  match csteps tm s c0 with
  | Some c => st_eqb (fst c) qa
  | None => false
  end.

Lemma bootvis_chk_sound : forall tm qa s,
  bootvis_chk tm qa s = true -> VisitsAt tm qa s.
Proof.
  unfold bootvis_chk; intros tm qa s H.
  destruct (csteps tm s c0) as [c|] eqn:E; [|discriminate].
  exact (visits_at_c0 tm qa s c E (proj1 (st_eqb_spec _ _) H)).
Qed.

(** ** The glue *)

Section GlueQuiet.

Variable tm : TM.
Variable Cf : positive -> cconf.
Variable p0 : positive.
Variable qa : St.
Variable t0 s0 : nat.

(** The bootstrap, at a CONCRETE index (the bound depends on it). *)
Hypothesis Hboot : stepn tm t0 InitES = Some (lift (Cf p0)).

(** [LapGlue]'s lap premise, strengthened with avoidance of [qa]. *)
Hypothesis Hlap : forall p, (p0 <= p)%positive ->
  exists n c', csteps tm n (Cf p) = Some c'
               /\ lift c' = lift (Cf (Pos.succ p)) /\ 0 < n
               /\ AvoidRun tm qa n (Cf p).

(** Visits for every RECURRING state (everything but [qa]). *)
Hypothesis Hvis : forall p q, (p0 <= p)%positive -> q <> qa ->
  exists k c, csteps tm k (Cf p) = Some c /\ fst c = q.

(** [qa]'s last visit, and the checked [qa]-free window up to the anchor. *)
Hypothesis Hvis0 : VisitsAt tm qa s0.
Hypothesis Hbq : forall n c, s0 < n < t0 ->
  stepn tm n InitES = Some c -> fst c <> qa.

Lemma gq_lap_plain : forall p, (p0 <= p)%positive ->
  exists n c', csteps tm n (Cf p) = Some c'
               /\ lift c' = lift (Cf (Pos.succ p)) /\ 0 < n.
Proof.
  intros p Hp. destruct (Hlap p Hp) as (n & c' & H1 & H2 & H3 & _).
  exists n, c'. auto.
Qed.

(** The anchor chain, carrying [qa]-freedom of everything since [t0].  The
    anchors march ([LapGlue.glue_reach]'s induction) and every global index in
    [[T, T+n)] projects into the lap from [Cf p] by [csteps_prefix] +
    [csteps_lift], where [AvoidRun] speaks. *)
Lemma gq_anchors : forall k, exists T p, (p0 <= p)%positive /\ k <= T /\ t0 <= T
  /\ stepn tm T InitES = Some (lift (Cf p))
  /\ (forall N c, t0 <= N < T -> stepn tm N InitES = Some c -> fst c <> qa).
Proof.
  induction k as [|k IH].
  - exists t0, p0.
    split; [apply Pos.le_refl|]. split; [lia|]. split; [lia|].
    split; [exact Hboot|]. intros N c HN. lia.
  - destruct IH as (T & p & Hp & HkT & Ht0T & Hstep & Hcov).
    destruct (Hlap p Hp) as (n & c' & Hrun & Hlift & Hn & Hav).
    exists (T + n), (Pos.succ p).
    split.
    { eapply Pos.le_trans; [exact Hp|].
      apply Pos.lt_le_incl, Pos.lt_succ_diag_r. }
    split; [lia|]. split; [lia|].
    split.
    { rewrite stepn_add, Hstep, (csteps_lift _ _ _ _ Hrun), Hlift.
      reflexivity. }
    intros N c HN HstepN.
    destruct (Nat.lt_ge_cases N T) as [HNT | HTN].
    + exact (Hcov N c ltac:(lia) HstepN).
    + replace N with (T + (N - T)) in HstepN by lia.
      rewrite stepn_add, Hstep in HstepN.
      destruct (csteps_prefix tm (N - T) n (Cf p) c' ltac:(lia) Hrun)
        as (cm & Hcm & _).
      rewrite (csteps_lift _ _ _ _ Hcm) in HstepN.
      injection HstepN as <-.
      rewrite lift_state.
      exact (Hav (N - T) cm ltac:(lia) Hcm).
Qed.

Lemma gq_noqa : forall N c, t0 <= N ->
  stepn tm N InitES = Some c -> fst c <> qa.
Proof.
  intros N c HN Hstep.
  destruct (gq_anchors (S N)) as (T & p & _ & HkT & Ht0T & _ & Hcov).
  exact (Hcov N c ltac:(lia) Hstep).
Qed.

Lemma gq_quiet : QuietAfter tm qa s0.
Proof.
  split; [exact Hvis0|].
  intros n Hn (c & Hc & Hqc).
  destruct (Nat.lt_ge_cases n t0) as [Hlt | Hge].
  - exact (Hbq n c ltac:(lia) Hc Hqc).
  - exact (gq_noqa n c Hge Hc Hqc).
Qed.

Lemma gq_recurs : forall q, q <> qa ->
  forall N, exists n, N <= n /\ VisitsAt tm q n.
Proof.
  intros q Hq N.
  destruct (glue_reach tm Cf p0 (ex_intro _ t0 Hboot) gq_lap_plain N)
    as (T & p & Hp & HN & Hstep).
  destruct (Hvis p q Hp Hq) as (k & c & Hc & Hqc).
  exists (T + k). split; [lia|].
  exists (lift c). split.
  - rewrite stepn_add, Hstep. apply csteps_lift; exact Hc.
  - rewrite lift_state. exact Hqc.
Qed.

Lemma gq_nonhalt : NonHalt tm.
Proof.
  intros n Hnone.
  destruct (glue_reach tm Cf p0 (ex_intro _ t0 Hboot) gq_lap_plain n)
    as (T & p & _ & HT & Hstep).
  replace T with (n + (T - n)) in Hstep by lia.
  rewrite stepn_add, Hnone in Hstep. discriminate.
Qed.

Lemma gq_qhbound : QHBound (S s0) tm.
Proof.
  intros q s Hq.
  destruct (st_eqb q qa) eqn:Eq.
  - apply st_eqb_spec in Eq. subst q.
    destruct Hq as (HvisS & _).
    destruct (Nat.le_gt_cases s s0) as [Hle | Hgt]; [lia|].
    exfalso. destruct gq_quiet as (_ & Hq0). exact (Hq0 s Hgt HvisS).
  - assert (Hne : q <> qa).
    { intro E. rewrite E in Eq.
      rewrite (proj2 (st_eqb_spec qa qa) eq_refl) in Eq. discriminate. }
    exfalso.
    destruct Hq as (_ & Hafter).
    destruct (gq_recurs q Hne (S s)) as (n & Hn & Hvn).
    exact (Hafter n ltac:(lia) Hvn).
Qed.

Theorem glue_qh_quiet : NonHalt tm /\ QHBound (S s0) tm /\ QuasiHaltsSt tm.
Proof.
  split; [exact gq_nonhalt | split; [exact gq_qhbound |]].
  exact (quiet_after_qh tm qa s0 gq_quiet).
Qed.

End GlueQuiet.
