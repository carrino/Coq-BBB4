(** * LAPT_1RB0LC_1LC1RA_1LC0LD_0RA1RC: TRANSITION-LEVEL board for machine 1RB0LC_1LC1RA_1LC0LD_0RA1RC, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Jp digit alphabet (JpCounter.v), anchored at

      Cc p = (StA, (Jp p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  8*j+8 steps
      overflow  (cview p = (S j, None)):   8*j+12 steps

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
                                  MonoCounter JpCounter JpCounter LapCertGlue LapCertGlueLift.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
From BBB4 Require Import BBBT4_Statement.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr.
Import ListNotations.

Definition mk_1RB0LC_1LC1RA_1LC0LD_0RA1RC (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB0LC_1LC1RA_1LC0LD_0RA1RC.

(** 1RB0LC_1LC1RA_1LC0LD_0RA1RC *)
(** 1RB0LC_1LC1RA_1LC0LD_0RA1RC -- the real machine (its counter grows RIGHT). *)
Definition tm_1RB0LC_1LC1RA_1LC0LD_0RA1RC : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StC
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StA
  | StC, S0 => mk S1 DL StC | StC, S1 => mk S0 DL StD
  | StD, S0 => mk S0 DR StA | StD, S1 => mk S1 DR StC end.

(** Its mirror 1LB0RC_1RC1LA_1RC0RD_0LA1LC: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_1RB0LC_1LC1RA_1LC0LD_0RA1RC : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => mk S0 DR StC
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DL StA
  | StC, S0 => mk S1 DR StC | StC, S1 => mk S0 DR StD
  | StD, S0 => mk S0 DL StA | StD, S1 => mk S1 DL StC end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_1RB0LC_1LC1RA_1LC0LD_0RA1RC : list Instr := [].
Definition tmw_1RB0LC_1LC1RA_1LC0LD_0RA1RC : TM := tm_wrap_trs tmm_1RB0LC_1LC1RA_1LC0LD_0RA1RC pins_1RB0LC_1LC1RA_1LC0LD_0RA1RC.
Local Notation tm := tmw_1RB0LC_1LC1RA_1LC0LD_0RA1RC.

Lemma mirror_ok_1RB0LC_1LC1RA_1LC0LD_0RA1RC : mirror_tm tm_1RB0LC_1LC1RA_1LC0LD_0RA1RC = tmm_1RB0LC_1LC1RA_1LC0LD_0RA1RC.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_1RB0LC_1LC1RA_1LC0LD_0RA1RC (p : positive) : cconf := (StA, (Jp p ++ [S0], S0, [])).
Local Notation Cc := Cc_1RB0LC_1LC1RA_1LC0LD_0RA1RC.

(** ** The certificate *)

Definition A0_1RB0LC_1LC1RA_1LC0LD_0RA1RC : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition A1_1RB0LC_1LC1RA_1LC0LD_0RA1RC : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S0] [] 0 0 []).
Definition chi_1RB0LC_1LC1RA_1LC0LD_0RA1RC : list lstep := [SCycL 2 0; SWin 6; SCycR 6; SWinR 2].

Lemma run_int_1RB0LC_1LC1RA_1LC0LD_0RA1RC : srun tm false true chi_1RB0LC_1LC1RA_1LC0LD_0RA1RC A0_1RB0LC_1LC1RA_1LC0LD_0RA1RC = Some (A1_1RB0LC_1LC1RA_1LC0LD_0RA1RC, 8, 8).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB0LC_1LC1RA_1LC0LD_0RA1RC : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_1RB0LC_1LC1RA_1LC0LD_0RA1RC : sconf := mkC StA (mkS [] [S1;S1] 1 1 [S1]) S0 (mkS [S0] [] 0 0 []).
Definition cho_1RB0LC_1LC1RA_1LC0LD_0RA1RC : list lstep := [SCycL 2 0; SWin 2; SWinL 8; SCycR 6; SWinR 2; SRotL 2; SFoldL 1].

Lemma run_ovf_1RB0LC_1LC1RA_1LC0LD_0RA1RC : srun tm true true cho_1RB0LC_1LC1RA_1LC0LD_0RA1RC B0_1RB0LC_1LC1RA_1LC0LD_0RA1RC = Some (B1_1RB0LC_1LC1RA_1LC0LD_0RA1RC, 8, 12).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_1RB0LC_1LC1RA_1LC0LD_0RA1RC : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Jp q0 ++ [S0]) [] j A0_1RB0LC_1LC1RA_1LC0LD_0RA1RC.
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (H1 & _).
  unfold Cc_1RB0LC_1LC1RA_1LC0LD_0RA1RC, cden, A0_1RB0LC_1LC1RA_1LC0LD_0RA1RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

(** The lap ends on [S0] where the anchor has [] -- one trailing blank,
    which [lift] cannot see. *)
Lemma gei_1RB0LC_1LC1RA_1LC0LD_0RA1RC : forall p j q0, cview p = (j, Some q0) ->
  lift (cden (Jp q0 ++ [S0]) [] j A1_1RB0LC_1LC1RA_1LC0LD_0RA1RC) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (_ & H2).
  unfold Cc_1RB0LC_1LC1RA_1LC0LD_0RA1RC, cden, A1_1RB0LC_1LC1RA_1LC0LD_0RA1RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S0]) with (([]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB0LC_1LC1RA_1LC0LD_0RA1RC : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  exists (8 * j + 8), (cden (Jp q0 ++ [S0]) [] j A1_1RB0LC_1LC1RA_1LC0LD_0RA1RC).
  split; [lia|]. split; [| exact (gei_1RB0LC_1LC1RA_1LC0LD_0RA1RC p j q0 E)].
  rewrite (gsi_1RB0LC_1LC1RA_1LC0LD_0RA1RC p j q0 E).
  exact (srun_sound tm false true chi_1RB0LC_1LC1RA_1LC0LD_0RA1RC A0_1RB0LC_1LC1RA_1LC0LD_0RA1RC A1_1RB0LC_1LC1RA_1LC0LD_0RA1RC 8 8
           run_int_1RB0LC_1LC1RA_1LC0LD_0RA1RC (Jp q0 ++ [S0]) [] j
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma gso_1RB0LC_1LC1RA_1LC0LD_0RA1RC : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_1RB0LC_1LC1RA_1LC0LD_0RA1RC.
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (H1 & _).
  unfold Cc_1RB0LC_1LC1RA_1LC0LD_0RA1RC, cden, B0_1RB0LC_1LC1RA_1LC0LD_0RA1RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB0LC_1LC1RA_1LC0LD_0RA1RC : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB0LC_1LC1RA_1LC0LD_0RA1RC : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB0LC_1LC1RA_1LC0LD_0RA1RC) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB0LC_1LC1RA_1LC0LD_0RA1RC
             = (StA, (rep [S1;S1] (S j) ++ [S1], S0, ([]) ++ [S0]))).
  { unfold cden, B1_1RB0LC_1LC1RA_1LC0LD_0RA1RC, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StA, ((rep [S1;S1] (S j) ++ [S1]) ++ [S0], S0, []))).
  { unfold Cc_1RB0LC_1LC1RA_1LC0LD_0RA1RC. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lift_app_blank. rewrite !lbl_1RB0LC_1LC1RA_1LC0LD_0RA1RC. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_1RB0LC_1LC1RA_1LC0LD_0RA1RC : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB0LC_1LC1RA_1LC0LD_0RA1RC p j q0 E) as (n & c' & Hn & Hrun & Hlift).
    exists n, c'. split; [exact Hrun | split; [exact Hlift | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_1RB0LC_1LC1RA_1LC0LD_0RA1RC B0_1RB0LC_1LC1RA_1LC0LD_0RA1RC B1_1RB0LC_1LC1RA_1LC0LD_0RA1RC 8 12 p j' [] []).
    + exact run_ovf_1RB0LC_1LC1RA_1LC0LD_0RA1RC.
    + reflexivity.
    + reflexivity.
    + exact (gso_1RB0LC_1LC1RA_1LC0LD_0RA1RC p j' E).
    + exact (geo_1RB0LC_1LC1RA_1LC0LD_0RA1RC p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_1RB0LC_1LC1RA_1LC0LD_0RA1RC : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 4.
  assert (H : match csteps tm 4 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 4 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_1RB0LC_1LC1RA_1LC0LD_0RA1RC : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_1RB0LC_1LC1RA_1LC0LD_0RA1RC = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_1RB0LC_1LC1RA_1LC0LD_0RA1RC p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB0LC_1LC1RA_1LC0LD_0RA1RC p j E)].
Qed.


(** An instruction that fires ONLY inside the interior lap: [vis_via_ovf] runs to an
    OVERFLOW anchor, so it cannot see one.  This is the interior witness, and
    [LapCertGlueLift.fire_via_int_lift] carries it to every anchor. *)
Lemma firei_1RB0LC_1LC1RA_1LC0LD_0RA1RC : forall (l : list lstep) (t : Instr),
  srun_instr tm false true l A0_1RB0LC_1LC1RA_1LC0LD_0RA1RC = Some t ->
  forall p j q0, cview p = (j, Some q0) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j q0 E.
  apply (fire_of_run_instr tm Cc false true l A0_1RB0LC_1LC1RA_1LC0LD_0RA1RC p j (Jp q0 ++ [S0]) []);
    [exact Hst | discriminate | reflexivity | exact (gsi_1RB0LC_1LC1RA_1LC0LD_0RA1RC p j q0 E)].
Qed.

(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_1RB0LC_1LC1RA_1LC0LD_0RA1RC : forall t, ~ In t pins_1RB0LC_1LC1RA_1LC0LD_0RA1RC ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n c', 0 < n /\ csteps tm n (Cc p0) = Some c'
                         /\ lift c' = lift (Cc (Pos.succ p0)))
    by exact lapi_1RB0LC_1LC1RA_1LC0LD_0RA1RC.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StA, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB0LC_1LC1RA_1LC0LD_0RA1RC [] (StA, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* A1: fires only in the interior lap *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_int_lift tm Cc lap_1RB0LC_1LC1RA_1LC0LD_0RA1RC (StA, S1)).
    intros p1 j1 r1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (firei_1RB0LC_1LC1RA_1LC0LD_0RA1RC [SCycL 2 0; SWin 2] (StA, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 r1 E1).
  - (* B0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StB, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB0LC_1LC1RA_1LC0LD_0RA1RC [SCycL 2 0; SWin 2; SWinL 1] (StB, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* B1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StB, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB0LC_1LC1RA_1LC0LD_0RA1RC [SCycL 2 0; SWin 1] (StB, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* C0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StC, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB0LC_1LC1RA_1LC0LD_0RA1RC [SCycL 2 0; SWin 2; SWinL 4] (StC, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* C1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StC, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB0LC_1LC1RA_1LC0LD_0RA1RC [SCycL 2 0; SWin 2; SWinL 2] (StC, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* D0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StD, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB0LC_1LC1RA_1LC0LD_0RA1RC [SCycL 2 0; SWin 2; SWinL 8; SCycR 6; SWinR 1] (StD, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* D1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StD, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB0LC_1LC1RA_1LC0LD_0RA1RC [SCycL 2 0; SWin 2; SWinL 3] (StD, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
Qed.

Theorem nqhtrm_1RB0LC_1LC1RA_1LC0LD_0RA1RC : NeverQuasiHaltsTr tmm_1RB0LC_1LC1RA_1LC0LD_0RA1RC.
Proof.
  apply (glue_neverqhtr tmm_1RB0LC_1LC1RA_1LC0LD_0RA1RC pins_1RB0LC_1LC1RA_1LC0LD_0RA1RC Cc 1).
  - exact boot_1RB0LC_1LC1RA_1LC0LD_0RA1RC.
  - intros p _. apply lap_1RB0LC_1LC1RA_1LC0LD_0RA1RC.
  - intros t Ht p _. apply fire_1RB0LC_1LC1RA_1LC0LD_0RA1RC. exact Ht.
Qed.

Theorem nqhtr_1RB0LC_1LC1RA_1LC0LD_0RA1RC : NeverQuasiHaltsTr tm_1RB0LC_1LC1RA_1LC0LD_0RA1RC.
Proof. apply (neverqhtr_mirror tm_1RB0LC_1LC1RA_1LC0LD_0RA1RC). rewrite mirror_ok_1RB0LC_1LC1RA_1LC0LD_0RA1RC. exact nqhtrm_1RB0LC_1LC1RA_1LC0LD_0RA1RC. Qed.

Theorem nonhalt_1RB0LC_1LC1RA_1LC0LD_0RA1RC : NonHalt tm_1RB0LC_1LC1RA_1LC0LD_0RA1RC.
Proof. apply never_qh_tr_nonhalt, nqhtr_1RB0LC_1LC1RA_1LC0LD_0RA1RC. Qed.
