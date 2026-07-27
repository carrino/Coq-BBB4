(** * LAPC_0RB1LA_1RC1LB_0LA1RD_0LB0RC: machine 0RB1LA_1RC1LB_0LA1RD_0LB0RC, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Ap_Alph_10_11_11 digit alphabet (Alph_10_11_11.v), anchored at

      Cc p = (StB, (Ap_Alph_10_11_11 p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  4*j+12 steps
      overflow  (cview p = (S j, None)):   4*j+19 steps

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 198 anchors.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter Alph_10_11_11 LapCertGlue LapCertGlueLift.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_0RB1LA_1RC1LB_0LA1RD_0LB0RC (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB1LA_1RC1LB_0LA1RD_0LB0RC.

(** 0RB1LA_1RC1LB_0LA1RD_0LB0RC *)
Definition tm_0RB1LA_1RC1LB_0LA1RD_0LB0RC : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S1 DL StA
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S0 DL StA | StC, S1 => mk S1 DR StD
  | StD, S0 => mk S0 DL StB | StD, S1 => mk S0 DR StC end.
Local Notation tm := tm_0RB1LA_1RC1LB_0LA1RD_0LB0RC.

Definition Cc_0RB1LA_1RC1LB_0LA1RD_0LB0RC (p : positive) : cconf := (StB, (Ap_Alph_10_11_11 p ++ [S0], S0, [S1])).
Local Notation Cc := Cc_0RB1LA_1RC1LB_0LA1RD_0LB0RC.

(** ** The certificate *)

Definition A0_0RB1LA_1RC1LB_0LA1RD_0LB0RC : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S1] [] 0 0 []).
Definition A1_0RB1LA_1RC1LB_0LA1RD_0LB0RC : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1;S0] [] 0 0 []).
Definition chi_0RB1LA_1RC1LB_0LA1RD_0LB0RC : list lstep := [SWin 1; SWinR 3; SCycL 2 0; SWin 4; SCycR 2; SWin 4].

Lemma run_int_0RB1LA_1RC1LB_0LA1RD_0LB0RC : srun tm false true chi_0RB1LA_1RC1LB_0LA1RD_0LB0RC A0_0RB1LA_1RC1LB_0LA1RD_0LB0RC = Some (A1_0RB1LA_1RC1LB_0LA1RD_0LB0RC, 4, 12).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB1LA_1RC1LB_0LA1RD_0LB0RC : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S1;S0]) S0 (mkS [S1] [] 0 0 []).
Definition B1_0RB1LA_1RC1LB_0LA1RD_0LB0RC : sconf := mkC StB (mkS [] [S1;S0] 1 1 [S1;S1]) S0 (mkS [S1;S0] [] 0 0 []).
Definition cho_0RB1LA_1RC1LB_0LA1RD_0LB0RC : list lstep := [SWin 1; SWinR 3; SCycL 2 0; SWin 6; SCycR 2; SWin 4; SWinR 5; SRotL 1; SFoldL 1].

Lemma run_ovf_0RB1LA_1RC1LB_0LA1RD_0LB0RC : srun tm true true cho_0RB1LA_1RC1LB_0LA1RD_0LB0RC B0_0RB1LA_1RC1LB_0LA1RD_0LB0RC = Some (B1_0RB1LA_1RC1LB_0LA1RD_0LB0RC, 4, 19).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_0RB1LA_1RC1LB_0LA1RD_0LB0RC : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Ap_Alph_10_11_11 q0 ++ [S0]) [] j A0_0RB1LA_1RC1LB_0LA1RD_0LB0RC.
Proof.
  intros p j q0 E. destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (H1 & _).
  unfold Cc_0RB1LA_1RC1LB_0LA1RD_0LB0RC, cden, A0_0RB1LA_1RC1LB_0LA1RD_0LB0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

(** The lap ends on [S1;S0] where the anchor has [S1] -- one trailing blank,
    which [lift] cannot see. *)
Lemma gei_0RB1LA_1RC1LB_0LA1RD_0LB0RC : forall p j q0, cview p = (j, Some q0) ->
  lift (cden (Ap_Alph_10_11_11 q0 ++ [S0]) [] j A1_0RB1LA_1RC1LB_0LA1RD_0LB0RC) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (_ & H2).
  unfold Cc_0RB1LA_1RC1LB_0LA1RD_0LB0RC, cden, A1_0RB1LA_1RC1LB_0LA1RD_0LB0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S1;S0]) with ([S1] ++ [S0]).
  rewrite lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_0RB1LA_1RC1LB_0LA1RD_0LB0RC : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  exists (4 * j + 12), (cden (Ap_Alph_10_11_11 q0 ++ [S0]) [] j A1_0RB1LA_1RC1LB_0LA1RD_0LB0RC).
  split; [lia|]. split; [| exact (gei_0RB1LA_1RC1LB_0LA1RD_0LB0RC p j q0 E)].
  rewrite (gsi_0RB1LA_1RC1LB_0LA1RD_0LB0RC p j q0 E).
  exact (srun_sound tm false true chi_0RB1LA_1RC1LB_0LA1RD_0LB0RC A0_0RB1LA_1RC1LB_0LA1RD_0LB0RC A1_0RB1LA_1RC1LB_0LA1RD_0LB0RC 4 12
           run_int_0RB1LA_1RC1LB_0LA1RD_0LB0RC (Ap_Alph_10_11_11 q0 ++ [S0]) [] j
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma gso_0RB1LA_1RC1LB_0LA1RD_0LB0RC : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_0RB1LA_1RC1LB_0LA1RD_0LB0RC.
Proof.
  intros p j E. destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p j E) as (H1 & _).
  unfold Cc_0RB1LA_1RC1LB_0LA1RD_0LB0RC, cden, B0_0RB1LA_1RC1LB_0LA1RD_0LB0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_0RB1LA_1RC1LB_0LA1RD_0LB0RC : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_0RB1LA_1RC1LB_0LA1RD_0LB0RC : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB1LA_1RC1LB_0LA1RD_0LB0RC) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_0RB1LA_1RC1LB_0LA1RD_0LB0RC
             = (StB, (rep [S1;S0] (S j) ++ [S1;S1], S0, [S1] ++ [S0]))).
  { unfold cden, B1_0RB1LA_1RC1LB_0LA1RD_0LB0RC, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. reflexivity. }
  assert (HC : Cc (Pos.succ p) = (StB, ((rep [S1;S0] (S j) ++ [S1;S1]) ++ [S0], S0, [S1]))).
  { unfold Cc_0RB1LA_1RC1LB_0LA1RD_0LB0RC. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite lift_app_blank. rewrite !lbl_0RB1LA_1RC1LB_0LA1RD_0LB0RC. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_0RB1LA_1RC1LB_0LA1RD_0LB0RC : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB1LA_1RC1LB_0LA1RD_0LB0RC p j q0 E) as (n & c' & Hn & Hrun & Hlift).
    exists n, c'. split; [exact Hrun | split; [exact Hlift | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_0RB1LA_1RC1LB_0LA1RD_0LB0RC B0_0RB1LA_1RC1LB_0LA1RD_0LB0RC B1_0RB1LA_1RC1LB_0LA1RD_0LB0RC 4 19 p j' [] []).
    + exact run_ovf_0RB1LA_1RC1LB_0LA1RD_0LB0RC.
    + reflexivity.
    + reflexivity.
    + exact (gso_0RB1LA_1RC1LB_0LA1RD_0LB0RC p j' E).
    + exact (geo_0RB1LA_1RC1LB_0LA1RD_0LB0RC p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_0RB1LA_1RC1LB_0LA1RD_0LB0RC : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 21.
  assert (H : match csteps tm 21 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 21 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma viso_0RB1LA_1RC1LB_0LA1RD_0LB0RC : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_0RB1LA_1RC1LB_0LA1RD_0LB0RC = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_0RB1LA_1RC1LB_0LA1RD_0LB0RC p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB1LA_1RC1LB_0LA1RD_0LB0RC p j E)].
Qed.

Lemma vis_0RB1LA_1RC1LB_0LA1RD_0LB0RC : forall p q, exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros p q.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n c', 0 < n /\ csteps tm n (Cc p0) = Some c'
                         /\ lift c' = lift (Cc (Pos.succ p0)))
    by exact lapi_0RB1LA_1RC1LB_0LA1RD_0LB0RC.
  destruct q.

  - (* StA *)
    apply (vis_via_ovf_lift tm Cc Hi StA).
    intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
    apply (viso_0RB1LA_1RC1LB_0LA1RD_0LB0RC [SWin 1; SWinR 3; SCycL 2 0; SWin 6; SCycR 2; SWin 3] StA ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* StB: the anchor state *)
    exists 0. eexists. split; reflexivity.
  - (* StC *)
    apply (vis_via_ovf_lift tm Cc Hi StC).
    intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
    apply (viso_0RB1LA_1RC1LB_0LA1RD_0LB0RC [SWin 1] StC ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* StD *)
    apply (vis_via_ovf_lift tm Cc Hi StD).
    intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
    apply (viso_0RB1LA_1RC1LB_0LA1RD_0LB0RC [SWin 1; SWinR 1] StD ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
Qed.

(** The interior lap closes only up to [lift] (one trailing blank past the
    anchor's far side), so the closer is [LapCertGlueLift.glue_neverqh_lift]:
    [LapGlue.glue_neverqh] with the visit premise in [stepn] space, which is
    what its own proof consumes. *)
Theorem nqh_0RB1LA_1RC1LB_0LA1RD_0LB0RC : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh_lift tm Cc 1). - exact boot_0RB1LA_1RC1LB_0LA1RD_0LB0RC. - intros p _. apply lap_0RB1LA_1RC1LB_0LA1RD_0LB0RC. - intros p q _. apply vis_0RB1LA_1RC1LB_0LA1RD_0LB0RC. Qed.

Theorem nonhalt_0RB1LA_1RC1LB_0LA1RD_0LB0RC : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_0RB1LA_1RC1LB_0LA1RD_0LB0RC. Qed.
