(** * LapGlueQH: monotone-counter laps + an un-targeted start state
      imply bounded quasihalting.

    The R_QH sibling of [LapGlue.glue_neverqh], for the residue's
    QUASIHALTING counters: machines whose start state fires in the
    bootstrap and never again, after which a counter runs forever.

    [glue_neverqh] needs every state to recur.  These machines have
    exactly one state that does not, so they are genuine quasihalters and
    [NeverQuasiHaltsSt] is false for them -- they need this closer instead.

    The quiet obligation is discharged SYNTACTICALLY.  If no transition of
    [tm] targets [StA], then [StA] can be visited only at configuration
    index 0 (every later configuration's state is some transition's target),
    so [QuietAfter tm StA 0] holds outright -- no trajectory analysis, no
    closure.  That is exactly the shape of the machines this targets: their
    bootstrap state is never re-entered.

    Conclusion: [NonHalt tm /\ QHBound 1 tm /\ QuasiHaltsSt tm].  The bound
    is 1, not [B_census = 2000]: the only quiet state made its last visit at
    index 0.  (Census/Assembly's [boarded] takes an existential bound, so any
    [B] composes -- see [iqhB_to_boarded].)

    Axiom footprint: [functional_extensionality_dep] only (inherited from
    [CTape]; this file adds none). *)

From Coq Require Import Arith Lia List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
Import ListNotations.

Section GlueQH.

Variable tm : TM.
Variable Cf : positive -> cconf.
Variable p0 : positive.

(** The bootstrap and lap premises are VERBATIM [LapGlue]'s, so a machine
    already carrying a lap proof needs nothing new here. *)
Hypothesis Hboot : exists t0, stepn tm t0 InitES = Some (lift (Cf p0)).
Hypothesis Hlap : forall p, (p0 <= p)%positive ->
  exists n c', csteps tm n (Cf p) = Some c' /\
               lift c' = lift (Cf (Pos.succ p)) /\ 0 < n.

(** Visits are required only for the RECURRING states -- every state except
    the quiet start state.  This is the one premise weaker than
    [glue_neverqh]'s. *)
Hypothesis Hvis : forall p q, (p0 <= p)%positive -> q <> StA ->
  exists k c, csteps tm k (Cf p) = Some c /\ fst c = q.

(** No transition targets the start state (a syntactic check on the table). *)
Hypothesis Huntarget : forall q b tr, tm q b = Some tr -> t_next tr <> StA.

(** ** The start state is visited only at index 0 *)

Lemma untargeted_only_zero : forall n c,
  stepn tm n InitES = Some c -> fst c = StA -> n = 0.
Proof.
  intros n c H Hq.
  destruct n as [|m]; [reflexivity|].
  exfalso.
  (* peel the LAST step: stepn (m+1) = stepn m then one step *)
  replace (S m) with (m + 1) in H by lia.
  rewrite stepn_add in H.
  destruct (stepn tm m InitES) as [cm|] eqn:Em; [|discriminate].
  simpl in H.
  destruct (step tm cm) as [c1|] eqn:Es; [|discriminate].
  simpl in H. injection H as <-.
  (* c1 came from a transition, whose target is not StA *)
  unfold step in Es.
  destruct cm as (qm, tp).
  destruct (tm qm (t_head tp)) as [tr|] eqn:Etr; [|discriminate].
  injection Es as <-.
  simpl in Hq.
  exact (Huntarget qm (t_head tp) tr Etr Hq).
Qed.

Lemma qz_quiet : QuietAfter tm StA 0.
Proof.
  split.
  - exists InitES. split; reflexivity.
  - intros n Hn (c & Hc & Hq).
    pose proof (untargeted_only_zero n c Hc Hq). lia.
Qed.

(** ** The anchors march (verbatim [LapGlue.glue_reach]) *)

Lemma glueqh_reach : forall k, exists T p, (p0 <= p)%positive /\ k <= T /\
  stepn tm T InitES = Some (lift (Cf p)).
Proof.
  induction k.
  - destruct Hboot as (t0 & H0).
    exists t0, p0. split; [apply Pos.le_refl|]. split; [lia | exact H0].
  - destruct IHk as (T & p & Hp & HT & Hstep).
    destruct (Hlap p Hp) as (n & c' & Hrun & Hlift & Hn).
    exists (T + n), (Pos.succ p).
    split.
    { eapply Pos.le_trans; [exact Hp|].
      apply Pos.lt_le_incl, Pos.lt_succ_diag_r. }
    split; [lia|].
    rewrite stepn_add, Hstep.
    rewrite (csteps_lift _ _ _ _ Hrun), Hlift.
    reflexivity.
Qed.

(** ** Every other state recurs at unboundedly large indices *)

Lemma glueqh_recurs : forall q, q <> StA ->
  forall N, exists n, N <= n /\ VisitsAt tm q n.
Proof.
  intros q Hq N.
  destruct (glueqh_reach N) as (T & p & Hp & HN & Hstep).
  destruct (Hvis p q Hp Hq) as (k & c & Hc & Hqc).
  exists (T + k). split; [lia|].
  exists (lift c). split.
  - rewrite stepn_add, Hstep. apply csteps_lift; exact Hc.
  - rewrite lift_state. exact Hqc.
Qed.

(** ** The three conclusions *)

Lemma glueqh_nonhalt : NonHalt tm.
Proof.
  intros n Hnone.
  destruct (glueqh_reach n) as (T & p & _ & HT & Hstep).
  replace T with (n + (T - n)) in Hstep by lia.
  rewrite stepn_add, Hnone in Hstep. discriminate.
Qed.

(** [StA] is the only quiet state, and its last visit is index 0. *)
Lemma glueqh_qhbound : QHBound 1 tm.
Proof.
  intros q s Hq.
  destruct (st_eqb q StA) eqn:Eq.
  - (* the quiet state: its only visit is at 0, so s = 0 *)
    apply st_eqb_spec in Eq. subst q.
    destruct Hq as (Hvis0 & _).
    destruct Hvis0 as (c & Hc & Hqc).
    pose proof (untargeted_only_zero s c Hc Hqc) as ->. lia.
  - (* any other state recurs, contradicting QuietAfter *)
    exfalso.
    assert (Hne : q <> StA).
    { intro E. rewrite E in Eq. rewrite (proj2 (st_eqb_spec StA StA) eq_refl) in Eq.
      discriminate. }
    destruct Hq as (_ & Hafter).
    destruct (glueqh_recurs q Hne (S s)) as (n & Hn & Hvn).
    exact (Hafter n ltac:(lia) Hvn).
Qed.

Lemma glueqh_quasihalts : QuasiHaltsSt tm.
Proof. exact (quiet_after_qh tm StA 0 qz_quiet). Qed.

Theorem glue_qh : NonHalt tm /\ QHBound 1 tm /\ QuasiHaltsSt tm.
Proof.
  split; [exact glueqh_nonhalt | split;
    [exact glueqh_qhbound | exact glueqh_quasihalts]].
Qed.

End GlueQH.
