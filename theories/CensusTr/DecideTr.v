(** * CensusTr/DecideTr: the transition-level census decider skeleton.

    The transition-level fork of Census/Decide.v's pipeline, phase-0
    scope (SCOPING_INSTR.md section 5): the tiers that STRENGTHEN
    MECHANICALLY are ported now -- halting, in-place cycles, translated
    cycles, and the three lookup tiers -- and everything else falls to
    [R_Unknown].  A cycle repeats the exact head-relative
    configuration, head symbol included, so the cycle tiers' conclusion
    lifts from "quiet states last visited before the anchor" to "quiet
    INSTRUCTIONS last fired before the anchor" with the same
    certificates and the same computational checks.

    Everything computational is REUSED from Census/Decide.v --
    [find_halt], the one-pass loop scan ([lp_candidates], [lp_check],
    [scan_loops]), the lookup maps ([dmap_of], [deferred_lookup]) --
    so a transition-level walk pops nodes at the same cost as the
    state-level one on these tiers.  Only the soundness layer is new.

    The n-gram / rank / wrapped-QHBound / RepWL tiers are NOT here
    yet: machines they used to decide fall through to [R_Unknown] and
    surface in the collection walk's back queue -- that back queue IS
    the burn-down list this skeleton exists to produce. *)

From Coq Require Import Arith Lia Bool List NArith PArith ZArith.
From Coq Require Import FSets.FMapPositive.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape GTape Mirror.
From BBB4.Checkers Require Import Cycle TCycler.
From BBB4.Census Require Import TNF_QH Decide.
From BBB4.CensusTr Require Import TNF_QHTr.
Import ListNotations.

Set Default Goal Selector "!".

(** ** The cycle tiers at transition level

    [glift] plants the window's head cell regardless of the abstract
    far-tape [rho], so a pumped window occurrence fires the same
    instruction. *)

Lemma glift_instr : forall rho rho' g,
  instr_of (glift rho g) = instr_of (glift rho' g).
Proof. intros rho rho' [q [[l h] r]]. reflexivity. Qed.

(** fires at or after an in-place cycle's start recur forever, so any
    eventually-quiet instruction last fired strictly before [n1] *)
Lemma cycle_qhboundtr : forall tm n1 p E,
  0 < p ->
  stepn tm n1 InitES = Some E ->
  stepn tm p E = Some E ->
  QHBoundTr n1 tm.
Proof.
  intros tm n1 p E Hp H1 Hloop t s [Hf Hq].
  destruct (le_lt_dec n1 s) as [Hge | Hlt]; [| lia].
  exfalso.
  destruct Hf as (c & Hc & Htc).
  apply (Hq (s + p)); [lia|].
  exists c. split; [| exact Htc].
  replace (s + p) with (n1 + (p + (s - n1))) by lia.
  rewrite stepn_add, H1.
  change (stepn tm (p + (s - n1)) E = Some c).
  rewrite stepn_add, Hloop.
  change (stepn tm (s - n1) E = Some c).
  replace s with (n1 + (s - n1)) in Hc by lia.
  rewrite stepn_add, H1 in Hc.
  exact Hc.
Qed.

Lemma cycle_leaf_check_sound_tr : forall tm n1 p,
  cycle_leaf_check tm n1 p = true ->
  NonHalt tm /\ QHBoundTr n1 tm.
Proof.
  intros tm n1 p H.
  unfold cycle_leaf_check in H.
  apply andb_prop in H as [Hp H].
  apply Nat.ltb_lt in Hp.
  destruct (csteps tm n1 c0) as [a|] eqn:Ea; [|discriminate].
  destruct (csteps tm (n1 + p) c0) as [b|] eqn:Eb; [|discriminate].
  apply ceqb_lift in H.
  pose proof (csteps_lift tm n1 c0 a Ea) as Ha.
  pose proof (csteps_lift tm (n1 + p) c0 b Eb) as Hb.
  rewrite lift_c0 in Ha, Hb.
  rewrite <- H in Hb.
  assert (Hloop : stepn tm p (lift a) = Some (lift a)).
  { rewrite stepn_add, Ha in Hb. exact Hb. }
  split.
  - exact (cycle_nonhalt tm n1 p (lift a) Hp Ha Hloop).
  - exact (cycle_qhboundtr tm n1 p (lift a) Hp Ha Hloop).
Qed.

Lemma tcycler_leaf_check_sound_tr : forall tm n1 P W,
  tcycler_leaf_check tm n1 P W = true ->
  NonHalt tm /\ QHBoundTr n1 tm.
Proof.
  intros tm n1 P W H.
  unfold tcycler_leaf_check in H.
  apply andb_prop in H as [Hp H].
  apply Nat.ltb_lt in Hp.
  destruct (csteps tm n1 c0) as [[q1 [[l1 h1] r1]]|] eqn:E1; [|discriminate].
  destruct (gsteps tm P (q1, (firstn_pad W l1, h1, r1))) as [g2|] eqn:E2;
    [|discriminate].
  pose proof (anchor_instance tm n1 W q1 l1 h1 r1 E1) as HA.
  set (g1 := (q1, (firstn_pad W l1, h1, r1)) : cconf) in *.
  set (rho0 := fun n => nthb l1 (n + W)) in *.
  split.
  - (* non-halting, exactly as at state level *)
    intros n HN.
    destruct (le_lt_dec n1 n) as [Hge | Hlt].
    + destruct (tcycler_fold tm n1 P g1 g2 rho0 Hp HA E2 H n Hge)
        as (i & gi & rho & Hi & Hgi & Hfold).
      rewrite Hfold in HN. discriminate.
    + destruct (csteps_prefix tm n n1 c0 (q1, (l1, h1, r1)))
        as (cm & Hcm & _); [lia | exact E1 |].
      assert (Hl : stepn tm n InitES = Some (lift cm)).
      { rewrite <- lift_c0. apply csteps_lift; assumption. }
      rewrite Hl in HN. discriminate.
  - (* any quiet instruction last fired before the anchor *)
    intros t s [Hf Hq].
    destruct (le_lt_dec n1 s) as [Hge | Hlt]; [| lia].
    exfalso.
    destruct Hf as (c & Hc & Htc).
    destruct (tcycler_fold tm n1 P g1 g2 rho0 Hp HA E2 H s Hge)
      as (i & gi & rho & Hi & Hgi & Hfold).
    rewrite Hfold in Hc. injection Hc as <-.
    (* pump the window occurrence one lap past s: the pumped config
       fires the same instruction ([glift_instr]) *)
    destruct (tcycler_laps tm n1 P g1 g2 rho0 HA E2 H (S s)) as [rho' Hrho'].
    apply (Hq (n1 + (S s) * P + i)); [nia|].
    exists (glift rho' gi).
    split.
    + replace (n1 + (S s) * P + i) with ((n1 + (S s) * P) + i) by lia.
      rewrite stepn_add, Hrho'.
      apply gsteps_lift; exact Hgi.
    + rewrite (glift_instr rho' rho gi). exact Htc.
Qed.

Corollary tcycler_leaf_check_sound_tr_L : forall tm n1 P W,
  tcycler_leaf_check (mirror_tm tm) n1 P W = true ->
  NonHalt tm /\ QHBoundTr n1 tm.
Proof.
  intros tm n1 P W H.
  destruct (tcycler_leaf_check_sound_tr (mirror_tm tm) n1 P W H) as [Hnh Hb].
  split.
  - apply mirror_nonhalt; exact Hnh.
  - apply qhboundtr_mirror; exact Hb.
Qed.

(** ** The pipeline (phase-0 tier stack) *)

Section PipelineTr.

Variable B : nat.              (** global transition-score bound *)
Variable D : list TM.          (** the deferred list (empty in the
                                   collection walk; frozen afterwards) *)
Variable halt_gas : nat.       (** gas for the halt search + cheap scan rung *)
Variable loop_gas : nat.       (** gas for the full loop-scan rung *)
Variable Prov : list TM.       (** proven [NeverQuasiHaltsTr] machines *)
Hypothesis HP : Forall NeverQuasiHaltsTr Prov.
Variable ProvQH : list TM.     (** proven census-grade transition-QH machines *)
Hypothesis HPQ :
  Forall (fun tm => NonHalt tm /\ QHBoundTr B tm /\ QuasiHaltsTr tm) ProvQH.

(** the reused one-pass candidates, re-checked by the reused verified
    checkers, concluded at transition level *)
Lemma lp_check_sound_tr : forall tm cand,
  lp_check B tm cand = true -> NonHalt tm /\ QHBoundTr B tm.
Proof.
  intros tm cand H.
  destruct cand as [n1 p | [|] n1 P];
    unfold lp_check in H;
    apply andb_prop in H as [Hb H];
    apply Nat.leb_le in Hb.
  - destruct (cycle_leaf_check_sound_tr tm n1 p H) as [Hnh Hq].
    split; [exact Hnh | exact (qhboundtr_mono n1 B tm Hb Hq)].
  - destruct (tcycler_leaf_check_sound_tr_L tm n1 P _ H) as [Hnh Hq].
    split; [exact Hnh | exact (qhboundtr_mono n1 B tm Hb Hq)].
  - destruct (tcycler_leaf_check_sound_tr tm n1 P _ H) as [Hnh Hq].
    split; [exact Hnh | exact (qhboundtr_mono n1 B tm Hb Hq)].
Qed.

Lemma scan_loops_sound_tr : forall tm gas,
  scan_loops B tm gas = true -> NonHalt tm /\ QHBoundTr B tm.
Proof.
  intros tm gas H.
  unfold scan_loops in H.
  rewrite anyb_existsb in H.
  apply existsb_exists in H.
  destruct H as (cand & _ & Hc).
  exact (lp_check_sound_tr tm cand Hc).
Qed.

(** the phase-0 decider: halting, lookups, cycles, defer the rest *)
Definition decide_easy_tr (pm qm dm : DeferredMap) (tm : TM) : QHResult :=
  match find_halt tm halt_gas 0 c0 with
  | Some (n, s, i) => if S n <=? B then R_Halt s i else R_Unknown
  | None =>
      if deferred_lookup pm tm then R_NeverQH else
      if deferred_lookup qm tm then R_QH else
      if deferred_lookup dm tm then R_Deferred else
      if scan_loops B tm halt_gas then R_Leaf else
      if scan_loops B tm loop_gas then R_Leaf else
      R_Unknown
  end.

Theorem decide_easy_tr_WF :
  QHDeciderTr_WF B D
    (decide_easy_tr (dmap_of Prov) (dmap_of ProvQH) (dmap_of D)).
Proof.
  intro tm.
  unfold decide_easy_tr.
  destruct (find_halt tm halt_gas 0 c0) as [[[n s] i]|] eqn:Eh.
  { destruct (S n <=? B) eqn:EB; [|exact I].
    apply Nat.leb_le in EB.
    destruct (find_halt_sound tm halt_gas 0 c0 n s i (eq_refl) Eh)
      as (tp & Hst & Hhd & Hnone).
    exists n, tp. auto. }
  destruct (deferred_lookup (dmap_of Prov) tm) eqn:Ep.
  { rewrite Forall_forall in HP.
    apply HP. apply deferred_lookup_In; exact Ep. }
  destruct (deferred_lookup (dmap_of ProvQH) tm) eqn:Epq.
  { rewrite Forall_forall in HPQ.
    apply HPQ. apply deferred_lookup_In; exact Epq. }
  destruct (deferred_lookup (dmap_of D) tm) eqn:Ed.
  { apply deferred_lookup_In; exact Ed. }
  destruct (scan_loops B tm halt_gas) eqn:El1.
  { exact (scan_loops_sound_tr tm halt_gas El1). }
  destruct (scan_loops B tm loop_gas) eqn:El2.
  { exact (scan_loops_sound_tr tm loop_gas El2). }
  exact I.
Qed.

End PipelineTr.
