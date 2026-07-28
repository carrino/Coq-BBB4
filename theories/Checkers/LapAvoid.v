(** * LapAvoid: state-avoidance of a lap certificate, checked by computation.

    [Checkers/LapDecider.v]'s chains are a faithful forward model — each
    [sstep] literally runs the machine over a window ([WTape.wsteps]), and a
    cycle iterates one such unit run.  So the set of STATES the concrete run
    passes through is determined by the certificate: the window runs are
    concrete, and every iteration of a cycle's unit repeats the same window
    states under a different frame.

    This file makes that computable.  [srun_avoid tm el er qa l c] re-runs
    the chain [l] checking that no window step is in state [qa]; its
    soundness theorem says the CONCRETE run the chain denotes — all
    [ca*j+cb] steps of it, for every carry index [j] and every opaque tail —
    never visits [qa] ([LapGlueQuiet.AvoidRun]).  That is the missing premise
    of [LapGlueQuiet.glue_qh_quiet], the closer for quasihalters whose quiet
    state is a transition target (so no syntactic or digraph argument can
    exclude it) but never fires after the bootstrap.

    No new certificate data: the avoidance is recomputed from the SAME chain
    by [vm_compute], and a chain whose trace touches [qa] simply evaluates to
    [false].  [LapDecider.v] is untouched.

    Axiom footprint: none of its own ([functional_extensionality_dep] via
    [CTape] upstream). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlueQuiet.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

(** ** Window-trace avoidance

    [wavoid bl br tm qa n c]: the [n]-step windowed run from [c] stays out
    of state [qa] at offsets [0 .. n-1] (the final configuration is the NEXT
    step's offset 0, so it is checked there). *)

Fixpoint wavoid (bl br : bool) (tm : TM) (qa : St) (n : nat) (c : cconf)
  : bool :=
  match n with
  | 0 => true
  | S m => negb (st_eqb (fst c) qa)
           && match wstep bl br tm c with
              | Some c' => wavoid bl br tm qa m c'
              | None => false
              end
  end.

Lemma wavoid_sound : forall bl br tm qa n q l h r L R,
  wavoid bl br tm qa n (q, (l, h, r)) = true ->
  (bl = false -> L = []) ->
  (br = false -> R = []) ->
  AvoidRun tm qa n (q, (l ++ L, h, r ++ R)).
Proof.
  intros bl br tm qa n; induction n as [|n IH];
    intros q l h r L R H HL HR m cm Hm Hstep.
  - lia.
  - cbn [wavoid] in H. apply andb_true_iff in H as [Hq H].
    destruct (wstep bl br tm (q, (l, h, r))) as [[q1 [[l1 h1] r1]]|] eqn:E;
      [|discriminate].
    destruct m as [|m'].
    + cbn in Hstep. injection Hstep as <-. exact (st_neq_of_negb _ _ Hq).
    + cbn [csteps] in Hstep.
      rewrite (wstep_transport _ _ _ _ _ _ _ _ _ _ _ L R E HL HR) in Hstep.
      exact (IH q1 l1 h1 r1 L R H HL HR m' cm ltac:(lia) Hstep).
Qed.

(** ** Cycle avoidance: the unit window's trace, repeated

    Same inductions as [WTape.cycL]/[cycR], carrying [AvoidRun] instead of
    the endpoint: iteration [i] enters the SAME window under a deeper frame,
    so one [wavoid] check covers every iteration. *)

Lemma cycL_avoid : forall tm qa P q h u rw w,
  wsteps true true tm P (q, (u, h, rw)) = Some (q, ([], h, rw ++ w)) ->
  wavoid true true tm qa P (q, (u, h, rw)) = true ->
  forall k L R, AvoidRun tm qa (P * k) (q, (rep u k ++ L, h, rw ++ R)).
Proof.
  intros tm qa P q h u rw w Hu Hav.
  induction k as [|k IH]; intros L R.
  - intros m cm Hm _. rewrite Nat.mul_0_r in Hm. lia.
  - replace (P * S k) with (P + P * k) by lia.
    cbn [rep]. rewrite <- app_assoc.
    apply (avoid_add tm qa P (P * k) _ (q, (rep u k ++ L, h, rw ++ (w ++ R)))).
    + pose proof (wsteps_frame tm P q u h rw q [] h (rw ++ w)
                    (rep u k ++ L) R Hu) as Hstep;
        cbn [app] in Hstep; rewrite <- app_assoc in Hstep.
      exact Hstep.
    + exact (wavoid_sound true true tm qa P q u h rw (rep u k ++ L) R Hav
               ltac:(discriminate) ltac:(discriminate)).
    + exact (IH L (w ++ R)).
Qed.

Lemma cycR_avoid : forall tm qa P q h u w,
  wsteps true true tm P (q, ([], h, u)) = Some (q, (w, h, [])) ->
  wavoid true true tm qa P (q, ([], h, u)) = true ->
  forall k L R, AvoidRun tm qa (P * k) (q, (L, h, rep u k ++ R)).
Proof.
  intros tm qa P q h u w Hu Hav.
  induction k as [|k IH]; intros L R.
  - intros m cm Hm _. rewrite Nat.mul_0_r in Hm. lia.
  - replace (P * S k) with (P + P * k) by lia.
    cbn [rep]. rewrite <- app_assoc.
    apply (avoid_add tm qa P (P * k) _ (q, (w ++ L, h, rep u k ++ R))).
    + pose proof (wsteps_frame tm P q [] h u q w h []
                    L (rep u k ++ R) Hu) as Hstep;
        cbn [app] in Hstep.
      exact Hstep.
    + exact (wavoid_sound true true tm qa P q [] h u L (rep u k ++ R) Hav
               ltac:(discriminate) ltac:(discriminate)).
    + exact (IH (w ++ L) R).
Qed.

(** ** Per-step avoidance

    The window each [lstep] kind actually runs, re-checked with [wavoid].
    Rotations and folds run zero machine steps, so they are vacuously
    avoiding. *)

Definition savoid (tm : TM) (qa : St) (st : lstep) (c : sconf) : bool :=
  match st with
  | SWin n =>
      wavoid true true tm qa n
        (c_st c, (s_pre (c_l c), c_h c, s_pre (c_r c)))
  | SWinL n =>
      wavoid false true tm qa n
        (c_st c, (s_pre (c_l c), c_h c, s_pre (c_r c)))
  | SWinR n =>
      wavoid true false tm qa n
        (c_st c, (s_pre (c_l c), c_h c, s_pre (c_r c)))
  | SCycL n m =>
      wavoid true true tm qa n
        (c_st c, (s_u (c_l c), c_h c, firstn m (s_pre (c_r c))))
  | SCycR n =>
      wavoid true true tm qa n
        (c_st c, ([], c_h c, s_u (c_r c)))
  | _ => true
  end.

Theorem sstep_avoid_sound : forall tm el er qa st c c' ca cb,
  sstep tm el er st c = Some (c', ca, cb) ->
  savoid tm qa st c = true ->
  forall XL XR j,
  (el = true -> XL = []) -> (er = true -> XR = []) ->
  AvoidRun tm qa (ca * j + cb) (cden XL XR j c).
Proof.
  intros tm el er qa st c c' ca cb H Hav XL XR j HL HR.
  destruct c as [q [pl ul al bl sl] h [pr ur ar br sr]].
  destruct st as [n | n | n | n m | n | m | m | m | m | m | m];
    cbn [sstep savoid c_st c_l c_h c_r s_pre s_u s_a s_b s_post] in H, Hav.

  - (* SWin *)
    destruct (wsteps true true tm n (q, (pl, h, pr)))
      as [[q' [[xl xh] xr]]|] eqn:E; [|discriminate].
    injection H as <- <- <-.
    replace (0 * j + n) with n by lia.
    unfold cden, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    exact (wavoid_sound true true tm qa n q pl h pr _ _ Hav
             ltac:(discriminate) ltac:(discriminate)).

  - (* SWinL *)
    destruct el; [|discriminate].
    rewrite (HL eq_refl).
    destruct ul as [|? ?]; [|discriminate].
    destruct sl as [|? ?]; [|discriminate].
    destruct (wsteps false true tm n (q, (pl, h, pr)))
      as [[q' [[xl xh] xr]]|] eqn:E; [|discriminate].
    injection H as <- <- <-.
    replace (0 * j + n) with n by lia.
    unfold cden, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    rewrite rep_nil. cbn [app].
    exact (wavoid_sound false true tm qa n q pl h pr [] _ Hav
             (fun _ => eq_refl) ltac:(discriminate)).

  - (* SWinR *)
    destruct er; [|discriminate].
    rewrite (HR eq_refl).
    destruct ur as [|? ?]; [|discriminate].
    destruct sr as [|? ?]; [|discriminate].
    destruct (wsteps true false tm n (q, (pl, h, pr)))
      as [[q' [[xl xh] xr]]|] eqn:E; [|discriminate].
    injection H as <- <- <-.
    replace (0 * j + n) with n by lia.
    unfold cden, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    rewrite rep_nil. cbn [app].
    exact (wavoid_sound true false tm qa n q pl h pr _ [] Hav
             ltac:(discriminate) (fun _ => eq_refl)).

  - (* SCycL *)
    destruct pl as [|? ?]; [|discriminate].
    destruct ur as [|? ?]; [|discriminate].
    destruct (wsteps true true tm n (q, (ul, h, firstn m pr)))
      as [[q2 [[l2 h2] r2]]|] eqn:E; [|discriminate].
    destruct l2 as [|? ?]; [|discriminate].
    destruct (st_eqb q q2 && sym_eqb h h2) eqn:Eq; [|discriminate].
    apply andb_true_iff in Eq as [Eq1 Eq2].
    apply st_eqb_spec in Eq1; apply sym_eqb_spec in Eq2; subst q2 h2.
    destruct (strip (firstn m pr) r2) as [w|] eqn:Ew; [|discriminate].
    injection H as <- <- <-.
    apply strip_sound in Ew; subst r2.
    replace (n * al * j + n * bl) with (n * (al * j + bl)) by lia.
    unfold cden, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    rewrite rep_nil. cbn [app].
    assert (Hcfg : pr ++ sr ++ XR
                   = firstn m pr ++ (skipn m pr ++ sr ++ XR)).
    { symmetry. rewrite app_assoc, firstn_skipn. reflexivity. }
    rewrite Hcfg.
    exact (cycL_avoid tm qa n q h ul (firstn m pr) w E Hav
             (al * j + bl) (sl ++ XL) (skipn m pr ++ sr ++ XR)).

  - (* SCycR *)
    destruct pr as [|? ?]; [|discriminate].
    destruct ul as [|? ?]; [|discriminate].
    destruct (wsteps true true tm n (q, ([], h, ur)))
      as [[q2 [[w h2] r2]]|] eqn:E; [|discriminate].
    destruct r2 as [|? ?]; [|discriminate].
    destruct (st_eqb q q2 && sym_eqb h h2) eqn:Eq; [|discriminate].
    apply andb_true_iff in Eq as [Eq1 Eq2].
    apply st_eqb_spec in Eq1; apply sym_eqb_spec in Eq2; subst q2 h2.
    injection H as <- <- <-.
    replace (n * ar * j + n * br) with (n * (ar * j + br)) by lia.
    unfold cden, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    rewrite rep_nil. cbn [app].
    exact (cycR_avoid tm qa n q h ur w E Hav
             (ar * j + br) (pl ++ sl ++ XL) (sr ++ XR)).

  - (* SRotL *)
    destruct (srot m (mkS pl ul al bl sl)) as [l'|] eqn:E; [|discriminate].
    injection H as <- <- <-.
    replace (0 * j + 0) with 0 by lia. apply avoid_0.
  - (* SRotR *)
    destruct (srot m (mkS pr ur ar br sr)) as [r'|] eqn:E; [|discriminate].
    injection H as <- <- <-.
    replace (0 * j + 0) with 0 by lia. apply avoid_0.
  - (* SUnrotL *)
    destruct (sunrot m (mkS pl ul al bl sl)) as [l'|] eqn:E; [|discriminate].
    injection H as <- <- <-.
    replace (0 * j + 0) with 0 by lia. apply avoid_0.
  - (* SUnrotR *)
    destruct (sunrot m (mkS pr ur ar br sr)) as [r'|] eqn:E; [|discriminate].
    injection H as <- <- <-.
    replace (0 * j + 0) with 0 by lia. apply avoid_0.
  - (* SFoldL *)
    destruct (sfold m (mkS pl ul al bl sl)) as [l'|] eqn:E; [|discriminate].
    injection H as <- <- <-.
    replace (0 * j + 0) with 0 by lia. apply avoid_0.
  - (* SFoldR *)
    destruct (sfold m (mkS pr ur ar br sr)) as [r'|] eqn:E; [|discriminate].
    injection H as <- <- <-.
    replace (0 * j + 0) with 0 by lia. apply avoid_0.
Qed.

(** ** Chain avoidance *)

Fixpoint srun_avoid (tm : TM) (el er : bool) (qa : St) (l : list lstep)
  (c : sconf) : bool :=
  match l with
  | [] => true
  | st :: l' =>
      savoid tm qa st c
      && match sstep tm el er st c with
         | Some (c1, _, _) => srun_avoid tm el er qa l' c1
         | None => false
         end
  end.

Theorem srun_avoid_sound : forall tm el er qa l c c' ca cb,
  srun tm el er l c = Some (c', ca, cb) ->
  srun_avoid tm el er qa l c = true ->
  forall XL XR j,
  (el = true -> XL = []) -> (er = true -> XR = []) ->
  AvoidRun tm qa (ca * j + cb) (cden XL XR j c).
Proof.
  intros tm el er qa l; induction l as [|st l IH];
    intros c c' ca cb H Hav XL XR j HL HR; cbn in H, Hav.
  - injection H as <- <- <-.
    replace (0 * j + 0) with 0 by lia. apply avoid_0.
  - apply andb_true_iff in Hav as [Hav1 Hav2].
    destruct (sstep tm el er st c) as [[[c1 a1] b1]|] eqn:E1; [|discriminate].
    destruct (srun tm el er l c1) as [[[c2 a2] b2]|] eqn:E2; [|discriminate].
    injection H as <- <- <-.
    replace ((a1 + a2) * j + (b1 + b2))
      with ((a1 * j + b1) + (a2 * j + b2)) by lia.
    apply (avoid_add tm qa (a1 * j + b1) (a2 * j + b2) _ (cden XL XR j c1)).
    + exact (sstep_sound tm el er st c c1 a1 b1 E1 XL XR j HL HR).
    + exact (sstep_avoid_sound tm el er qa st c c1 a1 b1 E1 Hav1 XL XR j HL HR).
    + exact (IH c1 c2 a2 b2 E2 Hav2 XL XR j HL HR).
Qed.

(** ** The anchor-level export (the twin of [LapDecider.lap_of_run]) *)

Theorem avoid_of_run : forall tm (Cf : positive -> cconf) el er qa l cA cB
                              ca cb p j XL XR,
  srun tm el er l cA = Some (cB, ca, cb) ->
  srun_avoid tm el er qa l cA = true ->
  (el = true -> XL = []) -> (er = true -> XR = []) ->
  Cf p = cden XL XR j cA ->
  AvoidRun tm qa (ca * j + cb) (Cf p).
Proof.
  intros tm Cf el er qa l cA cB ca cb p j XL XR Hrun Hav HL HR H0.
  rewrite H0.
  exact (srun_avoid_sound tm el er qa l cA cB ca cb Hrun Hav XL XR j HL HR).
Qed.
