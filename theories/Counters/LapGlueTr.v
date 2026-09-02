(** * LapGlueTr: monotone-counter laps imply never-quasihalting at the
    INSTRUCTION level.

    [LapGlue.glue_neverqh] closes a counter to [NeverQuasiHaltsSt] from
    a bootstrap, a lap and per-STATE visits.  The transition-level
    obligation ([NeverQuasiHaltsTr]: every instruction that ever fires
    fires unboundedly often) needs two more things, and the wrap trick
    of Checkers/WrapTr supplies both without touching the lap checker:

    - run the WHOLE lap argument on the wrapped machine
      [tm_wrap_trs tm pins], where [pins] are the instructions the
      certificate claims never fire.  The wrapped machine halts the
      moment a pinned instruction fires, so laps chaining forever on
      it prove at once that it never halts and -- by
      [WrapTr.wrap_trs_agree] -- that its run IS [tm]'s run and no
      pinned instruction ever fires in it;
    - per-INSTRUCTION visits for the unpinned instructions: from every
      anchor, each fires at some offset.  A lap-chain prefix's end
      configuration has a concrete head symbol, so the same prefix that
      witnessed a state at the state level witnesses the instruction
      here ([fire_of_run]).

    Everything else is [glue_neverqh]'s proof verbatim: the k-th anchor
    sits at global index >= k, and each anchor launches a fire of every
    unpinned instruction. *)

From Coq Require Import Arith Lia List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers Require Import WrapTr LapDecider.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import WTape MonoCounter JpCounter LapGlue LapCertGlue.
Import ListNotations.

Section GlueTr.

Variable tm : TM.
Variable pins : list Instr.       (** claimed never to fire *)
Variable Cf : positive -> cconf.
Variable p0 : positive.

(** the lap argument, on the WRAPPED machine *)
Hypothesis Hboot : exists t0,
  stepn (tm_wrap_trs tm pins) t0 InitES = Some (lift (Cf p0)).
Hypothesis Hlap : forall p, (p0 <= p)%positive ->
  exists n c', csteps (tm_wrap_trs tm pins) n (Cf p) = Some c' /\
               lift c' = lift (Cf (Pos.succ p)) /\ 0 < n.
(** every unpinned instruction fires from every anchor *)
Hypothesis Hfire : forall t, ~ In t pins -> forall p, (p0 <= p)%positive ->
  exists k c, csteps (tm_wrap_trs tm pins) k (Cf p) = Some c /\ cinstr c = t.

Lemma wrapped_nonhalt_tr : forall n, stepn (tm_wrap_trs tm pins) n InitES <> None.
Proof.
  intro n.
  destruct (glue_reach (tm_wrap_trs tm pins) Cf p0 Hboot Hlap n)
    as (T & p & _ & HT & Hstep).
  destruct (stepn_prefix (tm_wrap_trs tm pins) n T InitES _ HT Hstep)
    as (cm & Hcm & _).
  rewrite Hcm. discriminate.
Qed.

Theorem glue_neverqhtr : NeverQuasiHaltsTr tm.
Proof.
  intros t (n & c & Hc & Ht) N.
  pose proof (wrap_trs_agree tm pins InitES wrapped_nonhalt_tr) as Hagree.
  assert (Hnp : ~ In t pins).
  { destruct (Hagree n) as [_ Hnot]. rewrite <- Ht. exact (Hnot c Hc). }
  destruct (glue_reach (tm_wrap_trs tm pins) Cf p0 Hboot Hlap N)
    as (T & p & Hp & HN & Hstep).
  destruct (Hfire t Hnp p Hp) as (k & ck & Hk & Hck).
  exists (T + k). split; [lia|].
  exists (lift ck). split.
  - destruct (Hagree (T + k)) as [Heq _]. rewrite <- Heq.
    rewrite stepn_add, Hstep. apply csteps_lift; exact Hk.
  - rewrite cinstr_lift. exact Hck.
Qed.

End GlueTr.

(** ** Instruction witnesses from lap-chain prefixes

    [LapDecider.vis_of_run] with one more projection: the prefix's end
    configuration [c1] has head symbol [c_h c1] for every [j] and every
    tail, so it fires the instruction [(c_st c1, c_h c1)]. *)

Theorem fire_of_run : forall tm (Cf : positive -> cconf) el er l c0 c1 ca cb
                             p j XL XR,
  srun tm el er l c0 = Some (c1, ca, cb) ->
  (el = true -> XL = []) -> (er = true -> XR = []) ->
  Cf p = cden XL XR j c0 ->
  exists k c, csteps tm k (Cf p) = Some c /\ cinstr c = (c_st c1, c_h c1).
Proof.
  intros tm Cf el er l c0 c1 ca cb p j XL XR Hrun HL HR H0.
  exists (ca * j + cb), (cden XL XR j c1). split.
  - rewrite H0. exact (srun_sound tm el er l c0 c1 ca cb Hrun XL XR j HL HR).
  - reflexivity.
Qed.

(** the instruction a chain prefix ends on, as data *)
Definition srun_instr (tm : TM) (el er : bool) (l : list lstep) (c : sconf)
  : option Instr :=
  match srun tm el er l c with
  | Some (c1, _, _) => Some (c_st c1, c_h c1)
  | None => None
  end.

Theorem fire_of_run_instr : forall tm (Cf : positive -> cconf) el er l c0
                                   p j XL XR t,
  srun_instr tm el er l c0 = Some t ->
  (el = true -> XL = []) -> (er = true -> XR = []) ->
  Cf p = cden XL XR j c0 ->
  exists k c, csteps tm k (Cf p) = Some c /\ cinstr c = t.
Proof.
  intros tm Cf el er l c0 p j XL XR t Hi HL HR H0.
  unfold srun_instr in Hi.
  destruct (srun tm el er l c0) as [[[c1 ca] cb]|] eqn:E; [|discriminate].
  injection Hi as <-.
  exact (fire_of_run tm Cf el er l c0 c1 ca cb p j XL XR E HL HR H0).
Qed.

(** ** Reaching the overflow lap, per instruction

    [LapCertGlue.vis_via_ovf] for instructions: an instruction that fires
    only inside the overflow close still fires from every anchor. *)

Section FireReach.

Variable tm : TM.
Variable Cc : positive -> cconf.
Hypothesis Hint : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).

Lemma fire_via_ovf : forall t : Instr,
  (forall p j, cview p = (S j, None) ->
     exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t) ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Ht p.
  destruct (reach_ovf tm Cc Hint p) as (k1 & p' & H1 & (j & Hj)).
  destruct (Ht p' j Hj) as (k2 & c & H2 & Hc).
  exists (k1 + k2), c. split; [rewrite csteps_add, H1; exact H2 | exact Hc].
Qed.

End FireReach.

(** ** The [lift] routes, per instruction

    Twins of LapCertGlueLift's lemmas: when the interior lap closes only
    up to [lift] (one trailing blank past the anchor), the anchors are
    chained in [stepn] space and the instruction witness travels with
    them. *)

From BBB4.Counters Require Import LapCertGlueLift.

Section FireReachLift.

Variable tm : TM.
Variable Cc : positive -> cconf.
Hypothesis Hint : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).

Lemma fire_via_ovf_lift : forall t : Instr,
  (forall p j, cview p = (S j, None) ->
     exists k e, stepn tm k (lift (Cc p)) = Some e /\ instr_of e = t) ->
  forall p, exists k e, stepn tm k (lift (Cc p)) = Some e /\ instr_of e = t.
Proof.
  intros t Ht p.
  destruct (reach_ovf_lift tm Cc Hint p) as (k1 & p' & H1 & (j & Hj)).
  destruct (Ht p' j Hj) as (k2 & e & H2 & He).
  exists (k1 + k2), e. split; [rewrite stepn_add, H1; exact H2 | exact He].
Qed.

End FireReachLift.

Section FireReachInt.

Variable tm : TM.
Variable Cc : positive -> cconf.
Hypothesis Hlap : forall p, exists n c', csteps tm n (Cc p) = Some c'
                  /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.

Lemma fire_via_int_lift : forall t : Instr,
  (forall p j q0, cview p = (j, Some q0) ->
     exists k e, stepn tm k (lift (Cc p)) = Some e /\ instr_of e = t) ->
  forall p, exists k e, stepn tm k (lift (Cc p)) = Some e /\ instr_of e = t.
Proof.
  intros t Ht p.
  destruct (cview p) as [j oq] eqn:E; destruct oq as [q0|].
  - exact (Ht p j q0 E).
  - destruct (Hlap p) as (n & c' & Hrun & Hlift & _).
    destruct (cview_none_succ p j E) as (r & Hr).
    assert (Hcv : cview (Pos.succ p) = (0, Some r)) by (rewrite Hr; reflexivity).
    destruct (Ht (Pos.succ p) 0 r Hcv) as (k & e & Hk & He).
    exists (n + k), e. split; [| exact He].
    rewrite stepn_add, (csteps_lift _ _ _ _ Hrun), Hlift. exact Hk.
Qed.

End FireReachInt.

Lemma fire_lift_of_csteps : forall (tm : TM) (Cc : positive -> cconf) p t,
  (exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t) ->
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ instr_of e = t.
Proof.
  intros tm Cc p t (k & c & Hk & Ht).
  exists k, (lift c). split; [apply csteps_lift; exact Hk |].
  rewrite cinstr_lift; exact Ht.
Qed.

Lemma fire_csteps_of_lift : forall (tm : TM) (Cc : positive -> cconf) p t,
  (exists k e, stepn tm k (lift (Cc p)) = Some e /\ instr_of e = t) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros tm Cc p t (k & e & Hk & Ht).
  destruct (stepn_csteps_at tm k (Cc p) e Hk) as (c & Hc & Hl).
  exists k, c. split; [exact Hc |].
  rewrite <- cinstr_lift, Hl. exact Ht.
Qed.

(** ** The NESTED overflow, per instruction

    Twin of [NestedLapLift.vis_via_fill]: an instruction that fires only
    in the EXIT half of a nested overflow -- from the inner counter's
    all-ones fill, after the exponentially many inner laps -- still fires
    from the outer overflow anchor. *)

From BBB4.Counters Require Import IXPGadgets NestedLap NestedLapLift.

Section FireViaFill.

Variable tm : TM.
Variable Cc Cin : positive -> cconf.
Hypothesis Hin : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).

Lemma fire_via_fill : forall (t : Instr) (p v0 : positive),
  (exists n c, csteps tm n (Cc p) = Some c /\ lift c = lift (Cin v0)) ->
  (exists k e, stepn tm k (lift (Cin (fill v0))) = Some e /\ instr_of e = t) ->
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ instr_of e = t.
Proof.
  intros t p v0 (n & c & Hn & Hl) (k & e & Hk & Ht).
  destruct (inner_to_fill_lift tm Cin Hin v0) as (ni & Hi).
  exists (n + (ni + k)), e. split; [| exact Ht].
  rewrite stepn_add, (csteps_lift _ _ _ _ Hn), Hl, stepn_add, Hi. exact Hk.
Qed.

End FireViaFill.
