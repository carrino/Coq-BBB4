(** * LAPT_0RB1LD_1LC1RB_0RA0LA_0LC1RC: TRANSITION-LEVEL board for machine 0RB1LD_1LC1RB_0RA0LA_0LC1RC, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Kp digit alphabet (KpCounter.v), anchored at

      Cc p = (StB, (Kp p ++ [S0], S0, [S1]))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  4*j+18 steps
      overflow  (cview p = (S j, None)):   4*j+22 steps

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 198 anchors.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter KpCounter LapCertGlue LapCertGlueLift.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
From BBB4 Require Import BBBT4_Statement.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr.
Import ListNotations.

Definition mk_0RB1LD_1LC1RB_0RA0LA_0LC1RC (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB1LD_1LC1RB_0RA0LA_0LC1RC.

(** 0RB1LD_1LC1RB_0RA0LA_0LC1RC *)
(** 0RB1LD_1LC1RB_0RA0LA_0LC1RC -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB1LD_1LC1RB_0RA0LA_0LC1RC : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S1 DL StD
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S0 DR StA | StC, S1 => mk S0 DL StA
  | StD, S0 => mk S0 DL StC | StD, S1 => mk S1 DR StC end.

(** Its mirror 0LB1RD_1RC1LB_0LA0RA_0RC1LC: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB1LD_1LC1RB_0RA0LA_0LC1RC : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S1 DR StD
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S0 DL StA | StC, S1 => mk S0 DR StA
  | StD, S0 => mk S0 DR StC | StD, S1 => mk S1 DL StC end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_0RB1LD_1LC1RB_0RA0LA_0LC1RC : list Instr := [].
Definition tmw_0RB1LD_1LC1RB_0RA0LA_0LC1RC : TM := tm_wrap_trs tmm_0RB1LD_1LC1RB_0RA0LA_0LC1RC pins_0RB1LD_1LC1RB_0RA0LA_0LC1RC.
Local Notation tm := tmw_0RB1LD_1LC1RB_0RA0LA_0LC1RC.

Lemma mirror_ok_0RB1LD_1LC1RB_0RA0LA_0LC1RC : mirror_tm tm_0RB1LD_1LC1RB_0RA0LA_0LC1RC = tmm_0RB1LD_1LC1RB_0RA0LA_0LC1RC.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_0RB1LD_1LC1RB_0RA0LA_0LC1RC (p : positive) : cconf := (StB, (Kp p ++ [S0], S0, [S1])).
Local Notation Cc := Cc_0RB1LD_1LC1RB_0RA0LA_0LC1RC.

(** ** The certificate *)

Definition A0_0RB1LD_1LC1RB_0RA0LA_0LC1RC : sconf := mkC StB (mkS [] [S1] 1 0 [S0]) S0 (mkS [S1] [] 0 0 []).
Definition A1_0RB1LD_1LC1RB_0RA0LA_0LC1RC : sconf := mkC StB (mkS [] [S0] 1 0 [S1]) S0 (mkS [S1;S0;S0] [] 0 0 []).
Definition chi_0RB1LD_1LC1RB_0RA0LA_0LC1RC : list lstep := [SWin 1; SWinR 9; SCycL 1 0; SWin 2; SRotR 1; SWin 1; SCycR 3; SWin 4; SRotL 1; SWin 1].

Lemma run_int_0RB1LD_1LC1RB_0RA0LA_0LC1RC : srun tm false true chi_0RB1LD_1LC1RB_0RA0LA_0LC1RC A0_0RB1LD_1LC1RB_0RA0LA_0LC1RC = Some (A1_0RB1LD_1LC1RB_0RA0LA_0LC1RC, 4, 18).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB1LD_1LC1RB_0RA0LA_0LC1RC : sconf := mkC StB (mkS [S1] [S1] 1 0 [S0]) S0 (mkS [S1] [] 0 0 []).
Definition B1_0RB1LD_1LC1RB_0RA0LA_0LC1RC : sconf := mkC StB (mkS [] [S0] 1 1 [S1]) S0 (mkS [S1;S0;S0] [] 0 0 []).
Definition cho_0RB1LD_1LC1RB_0RA0LA_0LC1RC : list lstep := [SWin 1; SWinR 10; SCycL 1 0; SWin 2; SRotR 1; SWin 1; SCycR 3; SWin 8; SRotL 1; SFoldL 1].

Lemma run_ovf_0RB1LD_1LC1RB_0RA0LA_0LC1RC : srun tm true true cho_0RB1LD_1LC1RB_0RA0LA_0LC1RC B0_0RB1LD_1LC1RB_0RA0LA_0LC1RC = Some (B1_0RB1LD_1LC1RB_0RA0LA_0LC1RC, 4, 22).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_0RB1LD_1LC1RB_0RA0LA_0LC1RC : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Kp q0 ++ [S0]) [] j A0_0RB1LD_1LC1RB_0RA0LA_0LC1RC.
Proof.
  intros p j q0 E. destruct (KpCounter.cview_some_K p j q0 E) as (H1 & _).
  unfold Cc_0RB1LD_1LC1RB_0RA0LA_0LC1RC, cden, A0_0RB1LD_1LC1RB_0RA0LA_0LC1RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

(** The lap ends on [S1;S0;S0] where the anchor has [S1] -- one trailing blank,
    which [lift] cannot see. *)
Lemma gei_0RB1LD_1LC1RB_0RA0LA_0LC1RC : forall p j q0, cview p = (j, Some q0) ->
  lift (cden (Kp q0 ++ [S0]) [] j A1_0RB1LD_1LC1RB_0RA0LA_0LC1RC) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (KpCounter.cview_some_K p j q0 E) as (_ & H2).
  unfold Cc_0RB1LD_1LC1RB_0RA0LA_0LC1RC, cden, A1_0RB1LD_1LC1RB_0RA0LA_0LC1RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S1;S0;S0]) with ((([S1]) ++ [S0]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_0RB1LD_1LC1RB_0RA0LA_0LC1RC : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  exists (4 * j + 18), (cden (Kp q0 ++ [S0]) [] j A1_0RB1LD_1LC1RB_0RA0LA_0LC1RC).
  split; [lia|]. split; [| exact (gei_0RB1LD_1LC1RB_0RA0LA_0LC1RC p j q0 E)].
  rewrite (gsi_0RB1LD_1LC1RB_0RA0LA_0LC1RC p j q0 E).
  exact (srun_sound tm false true chi_0RB1LD_1LC1RB_0RA0LA_0LC1RC A0_0RB1LD_1LC1RB_0RA0LA_0LC1RC A1_0RB1LD_1LC1RB_0RA0LA_0LC1RC 4 18
           run_int_0RB1LD_1LC1RB_0RA0LA_0LC1RC (Kp q0 ++ [S0]) [] j
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma gso_0RB1LD_1LC1RB_0RA0LA_0LC1RC : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_0RB1LD_1LC1RB_0RA0LA_0LC1RC.
Proof.
  intros p j E. destruct (KpCounter.cview_none_K p j E) as (H1 & _).
  unfold Cc_0RB1LD_1LC1RB_0RA0LA_0LC1RC, cden, B0_0RB1LD_1LC1RB_0RA0LA_0LC1RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_0RB1LD_1LC1RB_0RA0LA_0LC1RC : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_0RB1LD_1LC1RB_0RA0LA_0LC1RC : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB1LD_1LC1RB_0RA0LA_0LC1RC) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (KpCounter.cview_none_K p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_0RB1LD_1LC1RB_0RA0LA_0LC1RC
             = (StB, (rep [S0] (S j) ++ [S1], S0, (([S1]) ++ [S0]) ++ [S0]))).
  { unfold cden, B1_0RB1LD_1LC1RB_0RA0LA_0LC1RC, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StB, ((rep [S0] (S j) ++ [S1]) ++ [S0], S0, [S1]))).
  { unfold Cc_0RB1LD_1LC1RB_0RA0LA_0LC1RC. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lift_app_blank. rewrite !lbl_0RB1LD_1LC1RB_0RA0LA_0LC1RC. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_0RB1LD_1LC1RB_0RA0LA_0LC1RC : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB1LD_1LC1RB_0RA0LA_0LC1RC p j q0 E) as (n & c' & Hn & Hrun & Hlift).
    exists n, c'. split; [exact Hrun | split; [exact Hlift | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_0RB1LD_1LC1RB_0RA0LA_0LC1RC B0_0RB1LD_1LC1RB_0RA0LA_0LC1RC B1_0RB1LD_1LC1RB_0RA0LA_0LC1RC 4 22 p j' [] []).
    + exact run_ovf_0RB1LD_1LC1RB_0RA0LA_0LC1RC.
    + reflexivity.
    + reflexivity.
    + exact (gso_0RB1LD_1LC1RB_0RA0LA_0LC1RC p j' E).
    + exact (geo_0RB1LD_1LC1RB_0RA0LA_0LC1RC p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_0RB1LD_1LC1RB_0RA0LA_0LC1RC : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 26.
  assert (H : match csteps tm 26 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 26 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_0RB1LD_1LC1RB_0RA0LA_0LC1RC : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_0RB1LD_1LC1RB_0RA0LA_0LC1RC = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_0RB1LD_1LC1RB_0RA0LA_0LC1RC p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB1LD_1LC1RB_0RA0LA_0LC1RC p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_0RB1LD_1LC1RB_0RA0LA_0LC1RC : forall t, ~ In t pins_0RB1LD_1LC1RB_0RA0LA_0LC1RC ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n c', 0 < n /\ csteps tm n (Cc p0) = Some c'
                         /\ lift c' = lift (Cc (Pos.succ p0)))
    by exact lapi_0RB1LD_1LC1RB_0RA0LA_0LC1RC.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StA, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1LD_1LC1RB_0RA0LA_0LC1RC [SWin 1; SWinR 1] (StA, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* A1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StA, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1LD_1LC1RB_0RA0LA_0LC1RC [SWin 1; SWinR 4] (StA, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* B0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StB, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1LD_1LC1RB_0RA0LA_0LC1RC [] (StB, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* B1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StB, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1LD_1LC1RB_0RA0LA_0LC1RC [SWin 1; SWinR 8] (StB, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* C0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StC, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1LD_1LC1RB_0RA0LA_0LC1RC [SWin 1; SWinR 3] (StC, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* C1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StC, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1LD_1LC1RB_0RA0LA_0LC1RC [SWin 1] (StC, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* D0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StD, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1LD_1LC1RB_0RA0LA_0LC1RC [SWin 1; SWinR 5] (StD, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* D1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StD, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1LD_1LC1RB_0RA0LA_0LC1RC [SWin 1; SWinR 10; SCycL 1 0; SWin 2; SRotR 1; SWin 1; SCycR 3; SWin 1] (StD, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
Qed.

Theorem nqhtrm_0RB1LD_1LC1RB_0RA0LA_0LC1RC : NeverQuasiHaltsTr tmm_0RB1LD_1LC1RB_0RA0LA_0LC1RC.
Proof.
  apply (glue_neverqhtr tmm_0RB1LD_1LC1RB_0RA0LA_0LC1RC pins_0RB1LD_1LC1RB_0RA0LA_0LC1RC Cc 1).
  - exact boot_0RB1LD_1LC1RB_0RA0LA_0LC1RC.
  - intros p _. apply lap_0RB1LD_1LC1RB_0RA0LA_0LC1RC.
  - intros t Ht p _. apply fire_0RB1LD_1LC1RB_0RA0LA_0LC1RC. exact Ht.
Qed.

Theorem nqhtr_0RB1LD_1LC1RB_0RA0LA_0LC1RC : NeverQuasiHaltsTr tm_0RB1LD_1LC1RB_0RA0LA_0LC1RC.
Proof. apply (neverqhtr_mirror tm_0RB1LD_1LC1RB_0RA0LA_0LC1RC). rewrite mirror_ok_0RB1LD_1LC1RB_0RA0LA_0LC1RC. exact nqhtrm_0RB1LD_1LC1RB_0RA0LA_0LC1RC. Qed.

Theorem nonhalt_0RB1LD_1LC1RB_0RA0LA_0LC1RC : NonHalt tm_0RB1LD_1LC1RB_0RA0LA_0LC1RC.
Proof. apply never_qh_tr_nonhalt, nqhtr_0RB1LD_1LC1RB_0RA0LA_0LC1RC. Qed.
