(** * LAPC_1RB1RD_1RC1LD_0LB0RC_1LB0RA: machine 1RB1RD_1RC1LD_0LB0RC_1LB0RA, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Ap_Alph_00_01_1 digit alphabet (Alph_00_01_1.v), anchored at

      Cc p = (StB, (Ap_Alph_00_01_1 p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  4*j+8 steps
      overflow  (cview p = (S j, None)):   8*j+13 steps

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 198 anchors.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter Alph_00_01_1 LapCertGlue LapCertGlueLift.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_1RB1RD_1RC1LD_0LB0RC_1LB0RA (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1RD_1RC1LD_0LB0RC_1LB0RA.

(** 1RB1RD_1RC1LD_0LB0RC_1LB0RA *)
Definition tm_1RB1RD_1RC1LD_0LB0RC_1LB0RA : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DR StD
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DL StD
  | StC, S0 => mk S0 DL StB | StC, S1 => mk S0 DR StC
  | StD, S0 => mk S1 DL StB | StD, S1 => mk S0 DR StA end.
Local Notation tm := tm_1RB1RD_1RC1LD_0LB0RC_1LB0RA.

Definition Cc_1RB1RD_1RC1LD_0LB0RC_1LB0RA (p : positive) : cconf := (StB, (Ap_Alph_00_01_1 p ++ [S0], S0, [])).
Local Notation Cc := Cc_1RB1RD_1RC1LD_0LB0RC_1LB0RA.

(** ** The certificate *)

Definition A0_1RB1RD_1RC1LD_0LB0RC_1LB0RA : sconf := mkC StB (mkS [] [S0;S1] 1 0 [S0;S0]) S0 (mkS [] [] 0 0 []).
Definition A1_1RB1RD_1RC1LD_0LB0RC_1LB0RA : sconf := mkC StB (mkS [] [S0;S0] 1 0 [S0;S1]) S0 (mkS [S0] [] 0 0 []).
Definition chi_1RB1RD_1RC1LD_0LB0RC_1LB0RA : list lstep := [SWinR 2; SCycL 2 0; SWin 4; SCycR 2; SWin 2].

Lemma run_int_1RB1RD_1RC1LD_0LB0RC_1LB0RA : srun tm false true chi_1RB1RD_1RC1LD_0LB0RC_1LB0RA A0_1RB1RD_1RC1LD_0LB0RC_1LB0RA = Some (A1_1RB1RD_1RC1LD_0LB0RC_1LB0RA, 4, 8).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB1RD_1RC1LD_0LB0RC_1LB0RA : sconf := mkC StB (mkS [] [S0;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_1RB1RD_1RC1LD_0LB0RC_1LB0RA : sconf := mkC StB (mkS [] [S0;S0] 1 1 [S1]) S0 (mkS [S0] [] 0 0 []).
Definition cho_1RB1RD_1RC1LD_0LB0RC_1LB0RA : list lstep := [SWinR 2; SCycL 2 0; SWin 2; SCycR 2; SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 1; SWinR 2; SRotL 1; SFoldL 1].

Lemma run_ovf_1RB1RD_1RC1LD_0LB0RC_1LB0RA : srun tm true true cho_1RB1RD_1RC1LD_0LB0RC_1LB0RA B0_1RB1RD_1RC1LD_0LB0RC_1LB0RA = Some (B1_1RB1RD_1RC1LD_0LB0RC_1LB0RA, 8, 13).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_1RB1RD_1RC1LD_0LB0RC_1LB0RA : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Ap_Alph_00_01_1 q0 ++ [S0]) [] j A0_1RB1RD_1RC1LD_0LB0RC_1LB0RA.
Proof.
  intros p j q0 E. destruct (Alph_00_01_1.cview_some_Alph_00_01_1 p j q0 E) as (H1 & _).
  unfold Cc_1RB1RD_1RC1LD_0LB0RC_1LB0RA, cden, A0_1RB1RD_1RC1LD_0LB0RC_1LB0RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S0;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

(** The lap ends on [S0] where the anchor has [] -- one trailing blank,
    which [lift] cannot see. *)
Lemma gei_1RB1RD_1RC1LD_0LB0RC_1LB0RA : forall p j q0, cview p = (j, Some q0) ->
  lift (cden (Ap_Alph_00_01_1 q0 ++ [S0]) [] j A1_1RB1RD_1RC1LD_0LB0RC_1LB0RA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (Alph_00_01_1.cview_some_Alph_00_01_1 p j q0 E) as (_ & H2).
  unfold Cc_1RB1RD_1RC1LD_0LB0RC_1LB0RA, cden, A1_1RB1RD_1RC1LD_0LB0RC_1LB0RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S0]) with ([] ++ [S0]).
  rewrite lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S0;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB1RD_1RC1LD_0LB0RC_1LB0RA : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  exists (4 * j + 8), (cden (Ap_Alph_00_01_1 q0 ++ [S0]) [] j A1_1RB1RD_1RC1LD_0LB0RC_1LB0RA).
  split; [lia|]. split; [| exact (gei_1RB1RD_1RC1LD_0LB0RC_1LB0RA p j q0 E)].
  rewrite (gsi_1RB1RD_1RC1LD_0LB0RC_1LB0RA p j q0 E).
  exact (srun_sound tm false true chi_1RB1RD_1RC1LD_0LB0RC_1LB0RA A0_1RB1RD_1RC1LD_0LB0RC_1LB0RA A1_1RB1RD_1RC1LD_0LB0RC_1LB0RA 4 8
           run_int_1RB1RD_1RC1LD_0LB0RC_1LB0RA (Ap_Alph_00_01_1 q0 ++ [S0]) [] j
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma gso_1RB1RD_1RC1LD_0LB0RC_1LB0RA : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_1RB1RD_1RC1LD_0LB0RC_1LB0RA.
Proof.
  intros p j E. destruct (Alph_00_01_1.cview_none_Alph_00_01_1 p j E) as (H1 & _).
  unfold Cc_1RB1RD_1RC1LD_0LB0RC_1LB0RA, cden, B0_1RB1RD_1RC1LD_0LB0RC_1LB0RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB1RD_1RC1LD_0LB0RC_1LB0RA : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB1RD_1RC1LD_0LB0RC_1LB0RA : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB1RD_1RC1LD_0LB0RC_1LB0RA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (Alph_00_01_1.cview_none_Alph_00_01_1 p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB1RD_1RC1LD_0LB0RC_1LB0RA
             = (StB, (rep [S0;S0] (S j) ++ [S1], S0, [] ++ [S0]))).
  { unfold cden, B1_1RB1RD_1RC1LD_0LB0RC_1LB0RA, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. reflexivity. }
  assert (HC : Cc (Pos.succ p) = (StB, ((rep [S0;S0] (S j) ++ [S1]) ++ [S0], S0, []))).
  { unfold Cc_1RB1RD_1RC1LD_0LB0RC_1LB0RA. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite lift_app_blank. rewrite !lbl_1RB1RD_1RC1LD_0LB0RC_1LB0RA. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_1RB1RD_1RC1LD_0LB0RC_1LB0RA : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB1RD_1RC1LD_0LB0RC_1LB0RA p j q0 E) as (n & c' & Hn & Hrun & Hlift).
    exists n, c'. split; [exact Hrun | split; [exact Hlift | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_1RB1RD_1RC1LD_0LB0RC_1LB0RA B0_1RB1RD_1RC1LD_0LB0RC_1LB0RA B1_1RB1RD_1RC1LD_0LB0RC_1LB0RA 8 13 p j' [] []).
    + exact run_ovf_1RB1RD_1RC1LD_0LB0RC_1LB0RA.
    + reflexivity.
    + reflexivity.
    + exact (gso_1RB1RD_1RC1LD_0LB0RC_1LB0RA p j' E).
    + exact (geo_1RB1RD_1RC1LD_0LB0RC_1LB0RA p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_1RB1RD_1RC1LD_0LB0RC_1LB0RA : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 1.
  assert (H : match csteps tm 1 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 1 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma viso_1RB1RD_1RC1LD_0LB0RC_1LB0RA : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_1RB1RD_1RC1LD_0LB0RC_1LB0RA = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_1RB1RD_1RC1LD_0LB0RC_1LB0RA p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB1RD_1RC1LD_0LB0RC_1LB0RA p j E)].
Qed.

Lemma vis_1RB1RD_1RC1LD_0LB0RC_1LB0RA : forall p q, exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros p q.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n c', 0 < n /\ csteps tm n (Cc p0) = Some c'
                         /\ lift c' = lift (Cc (Pos.succ p0)))
    by exact lapi_1RB1RD_1RC1LD_0LB0RC_1LB0RA.
  destruct q.

  - (* StA *)
    apply (vis_via_ovf_lift tm Cc Hi StA).
    intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
    apply (viso_1RB1RD_1RC1LD_0LB0RC_1LB0RA [SWinR 2; SCycL 2 0; SWin 2] StA ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* StB: the anchor state *)
    exists 0. eexists. split; reflexivity.
  - (* StC *)
    apply (vis_via_ovf_lift tm Cc Hi StC).
    intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
    apply (viso_1RB1RD_1RC1LD_0LB0RC_1LB0RA [SWinR 1] StC ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* StD *)
    apply (vis_via_ovf_lift tm Cc Hi StD).
    intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
    apply (viso_1RB1RD_1RC1LD_0LB0RC_1LB0RA [SWinR 2; SCycL 2 0; SWin 1] StD ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
Qed.

(** The interior lap closes only up to [lift] (one trailing blank past the
    anchor's far side), so the closer is [LapCertGlueLift.glue_neverqh_lift]:
    [LapGlue.glue_neverqh] with the visit premise in [stepn] space, which is
    what its own proof consumes. *)
Theorem nqh_1RB1RD_1RC1LD_0LB0RC_1LB0RA : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh_lift tm Cc 1). - exact boot_1RB1RD_1RC1LD_0LB0RC_1LB0RA. - intros p _. apply lap_1RB1RD_1RC1LD_0LB0RC_1LB0RA. - intros p q _. apply vis_1RB1RD_1RC1LD_0LB0RC_1LB0RA. Qed.

Theorem nonhalt_1RB1RD_1RC1LD_0LB0RC_1LB0RA : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_1RB1RD_1RC1LD_0LB0RC_1LB0RA. Qed.
