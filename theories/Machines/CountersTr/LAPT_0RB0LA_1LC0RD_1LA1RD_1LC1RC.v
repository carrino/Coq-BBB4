(** * LAPT_0RB0LA_1LC0RD_1LA1RD_1LC1RC: TRANSITION-LEVEL board for machine 0RB0LA_1LC0RD_1LA1RD_1LC1RC, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Bp digit alphabet (BpCounter.v), anchored at

      Cc p = (StA, (Bp p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  6*j+8 steps
      overflow  (cview p = (S j, None)):   6*j+14 steps

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
                                  MonoCounter JpCounter BpCounter LapCertGlue LapCertGlueLift.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
From BBB4 Require Import BBBT4_Statement.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr.
Import ListNotations.

Definition mk_0RB0LA_1LC0RD_1LA1RD_1LC1RC (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB0LA_1LC0RD_1LA1RD_1LC1RC.

(** 0RB0LA_1LC0RD_1LA1RD_1LC1RC *)
(** 0RB0LA_1LC0RD_1LA1RD_1LC1RC -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB0LA_1LC0RD_1LA1RD_1LC1RC : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S0 DL StA
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DR StD
  | StC, S0 => mk S1 DL StA | StC, S1 => mk S1 DR StD
  | StD, S0 => mk S1 DL StC | StD, S1 => mk S1 DR StC end.

(** Its mirror 0LB0RA_1RC0LD_1RA1LD_1RC1LC: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB0LA_1LC0RD_1LA1RD_1LC1RC : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S0 DR StA
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S0 DL StD
  | StC, S0 => mk S1 DR StA | StC, S1 => mk S1 DL StD
  | StD, S0 => mk S1 DR StC | StD, S1 => mk S1 DL StC end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_0RB0LA_1LC0RD_1LA1RD_1LC1RC : list Instr := [].
Definition tmw_0RB0LA_1LC0RD_1LA1RD_1LC1RC : TM := tm_wrap_trs tmm_0RB0LA_1LC0RD_1LA1RD_1LC1RC pins_0RB0LA_1LC0RD_1LA1RD_1LC1RC.
Local Notation tm := tmw_0RB0LA_1LC0RD_1LA1RD_1LC1RC.

Lemma mirror_ok_0RB0LA_1LC0RD_1LA1RD_1LC1RC : mirror_tm tm_0RB0LA_1LC0RD_1LA1RD_1LC1RC = tmm_0RB0LA_1LC0RD_1LA1RD_1LC1RC.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_0RB0LA_1LC0RD_1LA1RD_1LC1RC (p : positive) : cconf := (StA, (Bp p ++ [S0], S0, [])).
Local Notation Cc := Cc_0RB0LA_1LC0RD_1LA1RD_1LC1RC.

(** ** The certificate *)

Definition A0_0RB0LA_1LC0RD_1LA1RD_1LC1RC : sconf := mkC StA (mkS [] [S0;S1] 1 0 [S0;S0]) S0 (mkS [] [] 0 0 []).
Definition A1_0RB0LA_1LC0RD_1LA1RD_1LC1RC : sconf := mkC StA (mkS [] [S0;S0] 1 0 [S0;S1]) S0 (mkS [S0] [] 0 0 []).
Definition chi_0RB0LA_1LC0RD_1LA1RD_1LC1RC : list lstep := [SRotL 1; SWin 2; SWinR 3; SCycL 4 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_int_0RB0LA_1LC0RD_1LA1RD_1LC1RC : srun tm false true chi_0RB0LA_1LC0RD_1LA1RD_1LC1RC A0_0RB0LA_1LC0RD_1LA1RD_1LC1RC = Some (A1_0RB0LA_1LC0RD_1LA1RD_1LC1RC, 6, 8).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB0LA_1LC0RD_1LA1RD_1LC1RC : sconf := mkC StA (mkS [S0;S1] [S0;S1] 1 0 [S0]) S0 (mkS [] [] 0 0 []).
Definition B1_0RB0LA_1LC0RD_1LA1RD_1LC1RC : sconf := mkC StA (mkS [] [S0;S0] 1 1 [S0;S1]) S0 (mkS [S0] [] 0 0 []).
Definition cho_0RB0LA_1LC0RD_1LA1RD_1LC1RC : list lstep := [SWin 2; SWinR 4; SCycL 4 0; SWin 3; SWinL 3; SCycR 2; SWin 2; SFoldL 1].

Lemma run_ovf_0RB0LA_1LC0RD_1LA1RD_1LC1RC : srun tm true true cho_0RB0LA_1LC0RD_1LA1RD_1LC1RC B0_0RB0LA_1LC0RD_1LA1RD_1LC1RC = Some (B1_0RB0LA_1LC0RD_1LA1RD_1LC1RC, 6, 14).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_0RB0LA_1LC0RD_1LA1RD_1LC1RC : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Bp q0 ++ [S0]) [] j A0_0RB0LA_1LC0RD_1LA1RD_1LC1RC.
Proof.
  intros p j q0 E. destruct (BpCounter.cview_some_B p j q0 E) as (H1 & _).
  unfold Cc_0RB0LA_1LC0RD_1LA1RD_1LC1RC, cden, A0_0RB0LA_1LC0RD_1LA1RD_1LC1RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S0;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

(** The lap ends on [S0] where the anchor has [] -- one trailing blank,
    which [lift] cannot see. *)
Lemma gei_0RB0LA_1LC0RD_1LA1RD_1LC1RC : forall p j q0, cview p = (j, Some q0) ->
  lift (cden (Bp q0 ++ [S0]) [] j A1_0RB0LA_1LC0RD_1LA1RD_1LC1RC) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (BpCounter.cview_some_B p j q0 E) as (_ & H2).
  unfold Cc_0RB0LA_1LC0RD_1LA1RD_1LC1RC, cden, A1_0RB0LA_1LC0RD_1LA1RD_1LC1RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S0]) with (([]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S0;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_0RB0LA_1LC0RD_1LA1RD_1LC1RC : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  exists (6 * j + 8), (cden (Bp q0 ++ [S0]) [] j A1_0RB0LA_1LC0RD_1LA1RD_1LC1RC).
  split; [lia|]. split; [| exact (gei_0RB0LA_1LC0RD_1LA1RD_1LC1RC p j q0 E)].
  rewrite (gsi_0RB0LA_1LC0RD_1LA1RD_1LC1RC p j q0 E).
  exact (srun_sound tm false true chi_0RB0LA_1LC0RD_1LA1RD_1LC1RC A0_0RB0LA_1LC0RD_1LA1RD_1LC1RC A1_0RB0LA_1LC0RD_1LA1RD_1LC1RC 6 8
           run_int_0RB0LA_1LC0RD_1LA1RD_1LC1RC (Bp q0 ++ [S0]) [] j
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma gso_0RB0LA_1LC0RD_1LA1RD_1LC1RC : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_0RB0LA_1LC0RD_1LA1RD_1LC1RC.
Proof.
  intros p j E. destruct (BpCounter.cview_none_B p j E) as (H1 & _).
  unfold Cc_0RB0LA_1LC0RD_1LA1RD_1LC1RC, cden, B0_0RB0LA_1LC0RD_1LA1RD_1LC1RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_0RB0LA_1LC0RD_1LA1RD_1LC1RC : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_0RB0LA_1LC0RD_1LA1RD_1LC1RC : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB0LA_1LC0RD_1LA1RD_1LC1RC) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (BpCounter.cview_none_B p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_0RB0LA_1LC0RD_1LA1RD_1LC1RC
             = (StA, (rep [S0;S0] (S j) ++ [S0;S1], S0, ([]) ++ [S0]))).
  { unfold cden, B1_0RB0LA_1LC0RD_1LA1RD_1LC1RC, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StA, ((rep [S0;S0] (S j) ++ [S0;S1]) ++ [S0], S0, []))).
  { unfold Cc_0RB0LA_1LC0RD_1LA1RD_1LC1RC. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lift_app_blank. rewrite !lbl_0RB0LA_1LC0RD_1LA1RD_1LC1RC. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_0RB0LA_1LC0RD_1LA1RD_1LC1RC : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB0LA_1LC0RD_1LA1RD_1LC1RC p j q0 E) as (n & c' & Hn & Hrun & Hlift).
    exists n, c'. split; [exact Hrun | split; [exact Hlift | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_0RB0LA_1LC0RD_1LA1RD_1LC1RC B0_0RB0LA_1LC0RD_1LA1RD_1LC1RC B1_0RB0LA_1LC0RD_1LA1RD_1LC1RC 6 14 p j' [] []).
    + exact run_ovf_0RB0LA_1LC0RD_1LA1RD_1LC1RC.
    + reflexivity.
    + reflexivity.
    + exact (gso_0RB0LA_1LC0RD_1LA1RD_1LC1RC p j' E).
    + exact (geo_0RB0LA_1LC0RD_1LA1RD_1LC1RC p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_0RB0LA_1LC0RD_1LA1RD_1LC1RC : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 8.
  assert (H : match csteps tm 8 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 8 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_0RB0LA_1LC0RD_1LA1RD_1LC1RC : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_0RB0LA_1LC0RD_1LA1RD_1LC1RC = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_0RB0LA_1LC0RD_1LA1RD_1LC1RC p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB0LA_1LC0RD_1LA1RD_1LC1RC p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_0RB0LA_1LC0RD_1LA1RD_1LC1RC : forall t, ~ In t pins_0RB0LA_1LC0RD_1LA1RD_1LC1RC ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n c', 0 < n /\ csteps tm n (Cc p0) = Some c'
                         /\ lift c' = lift (Cc (Pos.succ p0)))
    by exact lapi_0RB0LA_1LC0RD_1LA1RD_1LC1RC.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StA, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB0LA_1LC0RD_1LA1RD_1LC1RC [] (StA, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* A1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StA, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB0LA_1LC0RD_1LA1RD_1LC1RC [SWin 2; SWinR 4; SCycL 4 0; SWin 3; SWinL 2] (StA, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* B0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StB, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB0LA_1LC0RD_1LA1RD_1LC1RC [SWin 1] (StB, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* B1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StB, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB0LA_1LC0RD_1LA1RD_1LC1RC [SWin 2; SWinR 2] (StB, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* C0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StC, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB0LA_1LC0RD_1LA1RD_1LC1RC [SWin 2] (StC, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* C1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StC, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB0LA_1LC0RD_1LA1RD_1LC1RC [SWin 2; SWinR 4] (StC, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* D0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StD, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB0LA_1LC0RD_1LA1RD_1LC1RC [SWin 2; SWinR 4; SCycL 4 0; SWin 1] (StD, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* D1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StD, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB0LA_1LC0RD_1LA1RD_1LC1RC [SWin 2; SWinR 3] (StD, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
Qed.

Theorem nqhtrm_0RB0LA_1LC0RD_1LA1RD_1LC1RC : NeverQuasiHaltsTr tmm_0RB0LA_1LC0RD_1LA1RD_1LC1RC.
Proof.
  apply (glue_neverqhtr tmm_0RB0LA_1LC0RD_1LA1RD_1LC1RC pins_0RB0LA_1LC0RD_1LA1RD_1LC1RC Cc 1).
  - exact boot_0RB0LA_1LC0RD_1LA1RD_1LC1RC.
  - intros p _. apply lap_0RB0LA_1LC0RD_1LA1RD_1LC1RC.
  - intros t Ht p _. apply fire_0RB0LA_1LC0RD_1LA1RD_1LC1RC. exact Ht.
Qed.

Theorem nqhtr_0RB0LA_1LC0RD_1LA1RD_1LC1RC : NeverQuasiHaltsTr tm_0RB0LA_1LC0RD_1LA1RD_1LC1RC.
Proof. apply (neverqhtr_mirror tm_0RB0LA_1LC0RD_1LA1RD_1LC1RC). rewrite mirror_ok_0RB0LA_1LC0RD_1LA1RD_1LC1RC. exact nqhtrm_0RB0LA_1LC0RD_1LA1RD_1LC1RC. Qed.

Theorem nonhalt_0RB0LA_1LC0RD_1LA1RD_1LC1RC : NonHalt tm_0RB0LA_1LC0RD_1LA1RD_1LC1RC.
Proof. apply never_qh_tr_nonhalt, nqhtr_0RB0LA_1LC0RD_1LA1RD_1LC1RC. Qed.
