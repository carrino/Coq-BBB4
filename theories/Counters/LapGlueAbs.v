(** * LapGlueAbs: an ABSORBING state set bounds every quiet state's last visit.

    The third closer, beside [LapGlue.glue_neverqh] (every state recurs) and
    [LapGlueQH.glue_qh] (the START state is targeted by nothing).  It settles
    the residue's remaining quasihalting counters: machines whose lap derives
    COMPLETELY -- anchor, both interior branches, overflow -- but where some
    state has no visit witness inside the lap, so [glue_neverqh] is simply
    false for them and [glue_qh]'s syntactic hypothesis does not apply
    because the quiet state IS targeted somewhere in the table.

    THE OBSERVATION.  [glue_qh] argues that a state targeted by no transition
    can only be the state at configuration index 0.  That is the [d = 0] case
    of a much more useful fact: if a set [Sset] of states is CLOSED under the
    transition table, and the machine is inside [Sset] at index [d], then it
    is inside [Sset] at every index from [d] on -- so every state outside
    [Sset] made all of its visits before [d].  The transition targeting the
    quiet state is then irrelevant: what matters is that its SOURCE has become
    unreachable, which the closure sees and a syntactic scan of the table
    does not.

    Measured over the residue's 149 complete-lap-no-visit-witness machines:
    141 admit such an [Sset], every one of them at [d <= 6].  The 121 that
    [glue_qh] could not touch (their quiet state is targeted) are included --
    the targeting transition fires only during the bootstrap, which is exactly
    what "the source left [Sset]" means.

    WHAT IS PROVED.  [NonHalt tm /\ QHBound d tm /\ QuasiHaltsSt tm], the R_QH
    triple.  The bound is [d], not [B_census = 2000], and [qhbound_mono] lifts
    it; [d <= 6] on every machine measured, so the bound is far inside the
    census tier and inside the champion's 32.8M prefix.

    WHY THIS IS NOT THE "STATES VISITED" BUILD.  [WAVE13_FINDINGS.md] section 6
    proposed reaching the same machines by teaching [wsteps_frame]/[cycL]/
    [cycR] to report every INTERMEDIATE state of a run, so that a lap could be
    shown to avoid the quiet state.  That is a much larger build -- a new
    soundness theorem for each primitive of the step language -- and it is not
    needed: the quiet state is not avoided by accident of the trajectory, it
    is unreachable in the transition digraph from where the machine already
    is.  The closure argument sees that directly and costs one induction.

    Axiom footprint: [functional_extensionality_dep] only (inherited from
    [CTape]; this file adds none). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From BBB4.Census Require Import TNF_QH.
Import ListNotations.

(** ** Reflective state-set membership

    A board's [Sset] is a literal list, so every side condition below is a
    [vm_compute]. *)

Definition st_inb (q : St) (l : list St) : bool := existsb (st_eqb q) l.

Lemma st_inb_true : forall q l, st_inb q l = true -> In q l.
Proof.
  intros q l H. unfold st_inb in H.
  apply existsb_exists in H as (x & Hx & Hq).
  apply st_eqb_spec in Hq. now subst.
Qed.

Lemma st_inb_false : forall q l, st_inb q l = false -> ~ In q l.
Proof.
  intros q l H Hin. unfold st_inb in H.
  assert (Hex : exists x, In x l /\ st_eqb q x = true).
  { exists q. split; [exact Hin | apply st_eqb_refl]. }
  apply existsb_exists in Hex. now rewrite H in Hex.
Qed.

(** The four states and the two symbols, exhaustively. *)
Definition all_st : list St := [StA; StB; StC; StD].
Definition all_sym : list Sym := [S0; S1].

Lemma all_st_spec : forall q, In q all_st.
Proof. destruct q; cbn; tauto. Qed.

Lemma all_sym_spec : forall b, In b all_sym.
Proof. destruct b; cbn; tauto. Qed.

(** [Sset] is closed under the table: no transition leaves it. *)
Definition closed_b (tm : TM) (l : list St) : bool :=
  forallb (fun q =>
    if st_inb q l
    then forallb (fun b => match tm q b with
                           | None => true
                           | Some tr => st_inb (t_next tr) l
                           end) all_sym
    else true) all_st.

Lemma closed_b_sound : forall tm l, closed_b tm l = true ->
  forall q b tr, In q l -> tm q b = Some tr -> In (t_next tr) l.
Proof.
  intros tm l H q b tr Hq Htr.
  unfold closed_b in H. rewrite forallb_forall in H.
  specialize (H q (all_st_spec q)).
  destruct (st_inb q l) eqn:Eq.
  - rewrite forallb_forall in H.
    specialize (H b (all_sym_spec b)).
    rewrite Htr in H. now apply st_inb_true.
  - now apply st_inb_false in Eq.
Qed.

(** ** The absorbing-set induction *)

Section Absorb.

Variable tm : TM.
Variable Sset : list St.
Hypothesis Hclosed : forall q b tr,
  In q Sset -> tm q b = Some tr -> In (t_next tr) Sset.

Lemma absorb_step : forall c c',
  In (fst c) Sset -> step tm c = Some c' -> In (fst c') Sset.
Proof.
  intros [q tp] c' Hq Hs; cbn in Hq |- *.
  unfold step in Hs.
  destruct (tm q (t_head tp)) as [tr|] eqn:E; [|discriminate].
  injection Hs as <-; cbn.
  exact (Hclosed q (t_head tp) tr Hq E).
Qed.

Lemma absorb_forward : forall n c, In (fst c) Sset ->
  forall c', stepn tm n c = Some c' -> In (fst c') Sset.
Proof.
  induction n as [|n IH]; intros c Hc c' H; cbn in H.
  - injection H as <-. exact Hc.
  - destruct (step tm c) as [c1|] eqn:E; [|discriminate].
    exact (IH c1 (absorb_step c c1 Hc E) c' H).
Qed.

(** The machine is inside [Sset] at index [d] (a concrete prefix run). *)
Variable d : nat.
Variable cd : cconf.
Hypothesis Hd : csteps tm d c0 = Some cd.
Hypothesis HdS : In (fst cd) Sset.

(** Hence every state OUTSIDE [Sset] is quiet from [d] on. *)
Lemma absorb_quiet_from : forall q, ~ In q Sset -> QuietFrom tm q d.
Proof.
  intros q Hq n Hn (c & Hc & Hqc).
  apply Hq. rewrite <- Hqc.
  replace n with (d + (n - d)) in Hc by lia.
  rewrite stepn_add, <- lift_c0, (csteps_lift _ _ _ _ Hd) in Hc.
  apply (absorb_forward (n - d) (lift cd)); [now rewrite lift_state | exact Hc].
Qed.

End Absorb.

(** ** The closer

    Premises are VERBATIM [LapGlueQH.glue_qh]'s, except that the visit
    obligation is restricted to [Sset] (rather than to "everything but
    [StA]") and the syntactic un-targeting hypothesis is replaced by the
    closure plus the prefix run. *)

Section GlueAbs.

Variable tm : TM.
Variable Cf : positive -> cconf.
Variable p0 : positive.
Variable Sset : list St.
Variable d : nat.

Hypothesis Hboot : exists t0, stepn tm t0 InitES = Some (lift (Cf p0)).
Hypothesis Hlap : forall p, (p0 <= p)%positive ->
  exists n c', csteps tm n (Cf p) = Some c' /\
               lift c' = lift (Cf (Pos.succ p)) /\ 0 < n.

(** Visits are required only for the states the lap actually reaches. *)
Hypothesis Hvis : forall p q, (p0 <= p)%positive -> In q Sset ->
  exists k c, csteps tm k (Cf p) = Some c /\ fst c = q.

Hypothesis Hclosed : forall q b tr,
  In q Sset -> tm q b = Some tr -> In (t_next tr) Sset.

(** The machine is inside [Sset] at index [d].  Stated existentially so a
    board discharges it with [eexists; split; [vm_compute; reflexivity | ...]]
    and never has to spell the intermediate configuration out. *)
Hypothesis Hd : exists cd, csteps tm d c0 = Some cd /\ In (fst cd) Sset.

(** The start state is outside [Sset] -- it is the [QuasiHaltsSt] witness,
    visited at index 0 and never from [d] on. *)
Hypothesis HAout : ~ In StA Sset.

(** [absorb_quiet_from] specialised to this section's prefix run. *)
Lemma glueabs_quiet : forall q, ~ In q Sset -> QuietFrom tm q d.
Proof.
  intros q Hq. destruct Hd as (cd & Hcd & HcdS).
  exact (absorb_quiet_from tm Sset Hclosed d cd Hcd HcdS q Hq).
Qed.

(** *** The anchors march (verbatim [LapGlue.glue_reach]) *)

Lemma glueabs_reach : forall k, exists T p, (p0 <= p)%positive /\ k <= T /\
  stepn tm T InitES = Some (lift (Cf p)).
Proof.
  induction k as [|k IHk].
  - destruct Hboot as (t0 & H0).
    exists t0, p0. split; [apply Pos.le_refl|]. split; [lia | exact H0].
  - destruct IHk as (T & p & Hp & HT & Hstep).
    destruct (Hlap p Hp) as (n & c' & Hrun & Hlift & Hn).
    exists (T + n), (Pos.succ p).
    split.
    { eapply Pos.le_trans; [exact Hp|].
      apply Pos.lt_le_incl, Pos.lt_succ_diag_r. }
    split; [lia|].
    rewrite stepn_add, Hstep, (csteps_lift _ _ _ _ Hrun), Hlift.
    reflexivity.
Qed.

Lemma glueabs_recurs : forall q, In q Sset ->
  forall N, exists n, N <= n /\ VisitsAt tm q n.
Proof.
  intros q Hq N.
  destruct (glueabs_reach N) as (T & p & Hp & HN & Hstep).
  destruct (Hvis p q Hp Hq) as (k & c & Hc & Hqc).
  exists (T + k). split; [lia|].
  exists (lift c). split.
  - rewrite stepn_add, Hstep. apply csteps_lift; exact Hc.
  - rewrite lift_state. exact Hqc.
Qed.

(** *** The three conclusions *)

Lemma glueabs_nonhalt : NonHalt tm.
Proof.
  intros n Hnone.
  destruct (glueabs_reach n) as (T & p & _ & HT & Hstep).
  replace T with (n + (T - n)) in Hstep by lia.
  rewrite stepn_add, Hnone in Hstep. discriminate.
Qed.

Lemma glueabs_qhbound : QHBound d tm.
Proof.
  intros q s Hq.
  destruct (st_inb q Sset) eqn:E.
  - (* inside [Sset]: [q] recurs, so it is never quiet *)
    exfalso. destruct Hq as (_ & Hafter).
    destruct (glueabs_recurs q (st_inb_true _ _ E) (S s)) as (n & Hn & Hv).
    exact (Hafter n ltac:(lia) Hv).
  - (* outside: quiet from [d], so the last visit is before [d] *)
    destruct Hq as (Hvis0 & _).
    assert (Hlt : ~ (d <= s)).
    { intro Hle.
      exact (glueabs_quiet q (st_inb_false _ _ E) s Hle Hvis0). }
    lia.
Qed.

Lemma glueabs_quasihalts : QuasiHaltsSt tm.
Proof.
  exists StA. split.
  - exists 0, InitES. split; reflexivity.
  - exists d. exact (glueabs_quiet StA HAout).
Qed.

Theorem glue_qh_abs : NonHalt tm /\ QHBound d tm /\ QuasiHaltsSt tm.
Proof.
  split; [exact glueabs_nonhalt | split;
    [exact glueabs_qhbound | exact glueabs_quasihalts]].
Qed.

End GlueAbs.
