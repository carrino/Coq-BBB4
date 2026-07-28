(** * LAPQ_1RB1LA_1LC0RB_0LC1RD_0RB1LA: machine 1RB1LA_1LC0RB_0LC1RD_0RB1LA, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Kp digit alphabet (KpCounter.v), anchored at

      Cc p = (StC, (Kp p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  j=0: 4 ; j=S j': 2*j'+6 steps
      overflow  (cview p = (S j, None)):   2*j+6 steps

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
                                  MonoCounter JpCounter KpCounter LapCertGlue LapGlueQuiet.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider LapAvoid.
Import ListNotations.

Definition mk_1RB1LA_1LC0RB_0LC1RD_0RB1LA (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1LA_1LC0RB_0LC1RD_0RB1LA.

(** 1RB1LA_1LC0RB_0LC1RD_0RB1LA *)
(** 1RB1LA_1LC0RB_0LC1RD_0RB1LA -- the real machine (its counter grows RIGHT). *)
Definition tm_1RB1LA_1LC0RB_0LC1RD_0RB1LA : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StA
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DR StB
  | StC, S0 => mk S0 DL StC | StC, S1 => mk S1 DR StD
  | StD, S0 => mk S0 DR StB | StD, S1 => mk S1 DL StA end.

(** Its mirror 1LB1RA_1RC0LB_0RC1LD_0LB1RA: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_1RB1LA_1LC0RB_0LC1RD_0RB1LA : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => mk S1 DR StA
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S0 DL StB
  | StC, S0 => mk S0 DR StC | StC, S1 => mk S1 DL StD
  | StD, S0 => mk S0 DL StB | StD, S1 => mk S1 DR StA end.
Local Notation tm := tmm_1RB1LA_1LC0RB_0LC1RD_0RB1LA.

Lemma mirror_ok_1RB1LA_1LC0RB_0LC1RD_0RB1LA : mirror_tm tm_1RB1LA_1LC0RB_0LC1RD_0RB1LA = tmm_1RB1LA_1LC0RB_0LC1RD_0RB1LA.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_1RB1LA_1LC0RB_0LC1RD_0RB1LA (p : positive) : cconf := (StC, (Kp p ++ [S0], S0, [S1])).
Local Notation Cc := Cc_1RB1LA_1LC0RB_0LC1RD_0RB1LA.

(** ** The certificate *)

(** j = 0: the repeated block is absent, so the whole lap is concrete. *)
Definition Z0_1RB1LA_1LC0RB_0LC1RD_0RB1LA : sconf := mkC StC (mkS [S0] [] 0 0 []) S0 (mkS [S1] [] 0 0 []).
Definition Z1_1RB1LA_1LC0RB_0LC1RD_0RB1LA : sconf := mkC StC (mkS [S1] [] 0 0 []) S0 (mkS [S1] [] 0 0 []).
Definition chz_1RB1LA_1LC0RB_0LC1RD_0RB1LA : list lstep := [SWin 4].

Lemma run_z_1RB1LA_1LC0RB_0LC1RD_0RB1LA : srun tm false true chz_1RB1LA_1LC0RB_0LC1RD_0RB1LA Z0_1RB1LA_1LC0RB_0LC1RD_0RB1LA = Some (Z1_1RB1LA_1LC0RB_0LC1RD_0RB1LA, 0, 4).
Proof. vm_compute. reflexivity. Qed.

(** j = S j': one copy of the unit sits in the PREFIX, so the head always has
    a concrete cell to step onto. *)
Definition P0_1RB1LA_1LC0RB_0LC1RD_0RB1LA : sconf := mkC StC (mkS [S1] [S1] 1 0 [S0]) S0 (mkS [S1] [] 0 0 []).
Definition P1_1RB1LA_1LC0RB_0LC1RD_0RB1LA : sconf := mkC StC (mkS [S0] [S0] 1 0 [S1]) S0 (mkS [S1] [] 0 0 []).
Definition chp_1RB1LA_1LC0RB_0LC1RD_0RB1LA : list lstep := [SWin 3; SCycL 1 0; SWin 2; SCycR 1; SWin 1].

Lemma run_p_1RB1LA_1LC0RB_0LC1RD_0RB1LA : srun tm false true chp_1RB1LA_1LC0RB_0LC1RD_0RB1LA P0_1RB1LA_1LC0RB_0LC1RD_0RB1LA = Some (P1_1RB1LA_1LC0RB_0LC1RD_0RB1LA, 2, 6).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB1LA_1LC0RB_0LC1RD_0RB1LA : sconf := mkC StC (mkS [S1] [S1] 1 0 [S0]) S0 (mkS [S1] [] 0 0 []).
Definition B1_1RB1LA_1LC0RB_0LC1RD_0RB1LA : sconf := mkC StC (mkS [] [S0] 1 1 [S1]) S0 (mkS [S1] [] 0 0 []).
Definition cho_1RB1LA_1LC0RB_0LC1RD_0RB1LA : list lstep := [SWin 3; SCycL 1 0; SWin 2; SCycR 1; SWin 1; SFoldL 1].

Lemma run_ovf_1RB1LA_1LC0RB_0LC1RD_0RB1LA : srun tm true true cho_1RB1LA_1LC0RB_0LC1RD_0RB1LA B0_1RB1LA_1LC0RB_0LC1RD_0RB1LA = Some (B1_1RB1LA_1LC0RB_0LC1RD_0RB1LA, 2, 6).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gz_1RB1LA_1LC0RB_0LC1RD_0RB1LA : forall p q0, cview p = (0, Some q0) ->
  Cc p = cden (Kp q0 ++ [S0]) [] 0 Z0_1RB1LA_1LC0RB_0LC1RD_0RB1LA /\
  cden (Kp q0 ++ [S0]) [] 0 Z1_1RB1LA_1LC0RB_0LC1RD_0RB1LA = Cc (Pos.succ p).
Proof.
  intros p q0 E. destruct (KpCounter.cview_some_K p 0 q0 E) as (H1 & H2).
  unfold Cc_1RB1LA_1LC0RB_0LC1RD_0RB1LA, cden, Z0_1RB1LA_1LC0RB_0LC1RD_0RB1LA, Z1_1RB1LA_1LC0RB_0LC1RD_0RB1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gp_1RB1LA_1LC0RB_0LC1RD_0RB1LA : forall p j q0, cview p = (S j, Some q0) ->
  Cc p = cden (Kp q0 ++ [S0]) [] j P0_1RB1LA_1LC0RB_0LC1RD_0RB1LA /\
  cden (Kp q0 ++ [S0]) [] j P1_1RB1LA_1LC0RB_0LC1RD_0RB1LA = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (KpCounter.cview_some_K p (S j) q0 E) as (H1 & H2).
  unfold Cc_1RB1LA_1LC0RB_0LC1RD_0RB1LA, cden, P0_1RB1LA_1LC0RB_0LC1RD_0RB1LA, P1_1RB1LA_1LC0RB_0LC1RD_0RB1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB1LA_1LC0RB_0LC1RD_0RB1LA : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct j as [|j'].
  - destruct (gz_1RB1LA_1LC0RB_0LC1RD_0RB1LA p q0 E) as (HA & HB).
    exists (0 * 0 + 4). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chz_1RB1LA_1LC0RB_0LC1RD_0RB1LA Z0_1RB1LA_1LC0RB_0LC1RD_0RB1LA Z1_1RB1LA_1LC0RB_0LC1RD_0RB1LA 0 4
               run_z_1RB1LA_1LC0RB_0LC1RD_0RB1LA (Kp q0 ++ [S0]) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gp_1RB1LA_1LC0RB_0LC1RD_0RB1LA p j' q0 E) as (HA & HB).
    exists (2 * j' + 6). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chp_1RB1LA_1LC0RB_0LC1RD_0RB1LA P0_1RB1LA_1LC0RB_0LC1RD_0RB1LA P1_1RB1LA_1LC0RB_0LC1RD_0RB1LA 2 6
               run_p_1RB1LA_1LC0RB_0LC1RD_0RB1LA (Kp q0 ++ [S0]) [] j'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
Qed.

Lemma gso_1RB1LA_1LC0RB_0LC1RD_0RB1LA : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_1RB1LA_1LC0RB_0LC1RD_0RB1LA.
Proof.
  intros p j E. destruct (KpCounter.cview_none_K p j E) as (H1 & _).
  unfold Cc_1RB1LA_1LC0RB_0LC1RD_0RB1LA, cden, B0_1RB1LA_1LC0RB_0LC1RD_0RB1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB1LA_1LC0RB_0LC1RD_0RB1LA : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB1LA_1LC0RB_0LC1RD_0RB1LA : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB1LA_1LC0RB_0LC1RD_0RB1LA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (KpCounter.cview_none_K p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB1LA_1LC0RB_0LC1RD_0RB1LA
             = (StC, (rep [S0] (S j) ++ [S1], S0, [S1]))).
  { unfold cden, B1_1RB1LA_1LC0RB_0LC1RD_0RB1LA, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StC, ((rep [S0] (S j) ++ [S1]) ++ [S0], S0, [S1]))).
  { unfold Cc_1RB1LA_1LC0RB_0LC1RD_0RB1LA. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_1RB1LA_1LC0RB_0LC1RD_0RB1LA. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_1RB1LA_1LC0RB_0LC1RD_0RB1LA : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB1LA_1LC0RB_0LC1RD_0RB1LA p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_1RB1LA_1LC0RB_0LC1RD_0RB1LA B0_1RB1LA_1LC0RB_0LC1RD_0RB1LA B1_1RB1LA_1LC0RB_0LC1RD_0RB1LA 2 6 p j' [] []).
    + exact run_ovf_1RB1LA_1LC0RB_0LC1RD_0RB1LA.
    + reflexivity.
    + reflexivity.
    + exact (gso_1RB1LA_1LC0RB_0LC1RD_0RB1LA p j' E).
    + exact (geo_1RB1LA_1LC0RB_0LC1RD_0RB1LA p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_1RB1LA_1LC0RB_0LC1RD_0RB1LA : exists t0, stepn tm t0 InitES = Some (lift (Cc 2)).
Proof.
  exists 10.
  assert (H : match csteps tm 10 c0 with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 10 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma viso_1RB1LA_1LC0RB_0LC1RD_0RB1LA : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_1RB1LA_1LC0RB_0LC1RD_0RB1LA = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_1RB1LA_1LC0RB_0LC1RD_0RB1LA p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB1LA_1LC0RB_0LC1RD_0RB1LA p j E)].
Qed.

Lemma vis_1RB1LA_1LC0RB_0LC1RD_0RB1LA : forall p q, q <> StA -> exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q Hq.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_1RB1LA_1LC0RB_0LC1RD_0RB1LA.
  destruct q.

  - (* StA: quiet -- see the closing theorem *)
    exfalso; exact (Hq eq_refl).
  - (* StB *)
    apply (vis_via_ovf tm Cc Hi StB), viso_1RB1LA_1LC0RB_0LC1RD_0RB1LA
      with (l := [SWin 3]).
    vm_compute; reflexivity.
  - (* StC: the anchor state *)
    exists 0. eexists. split; reflexivity.
  - (* StD *)
    apply (vis_via_ovf tm Cc Hi StD), viso_1RB1LA_1LC0RB_0LC1RD_0RB1LA
      with (l := [SWin 2]).
    vm_compute; reflexivity.
Qed.

(** StA IS a transition target, so [LapGlueQH.glue_qh]'s syntactic argument
    is out; and [LapGlueAbs.closed_b] is a digraph fact, so no absorbing set
    can exclude StA either.  What is true is trajectory-level: StA's last
    visit is at index 5 (checked), the window (5, 10) is StA-free
    (checked), and EVERY lap avoids StA -- recomputed from the SAME chains by
    the kernel ([av_*] below, [Checkers/LapAvoid.v]).
    [LapGlueQuiet.glue_qh_quiet] closes with the exact bound S 5,
    weakened to the census tier's 2000. *)
Lemma av_z_1RB1LA_1LC0RB_0LC1RD_0RB1LA : srun_avoid tm false true StA chz_1RB1LA_1LC0RB_0LC1RD_0RB1LA Z0_1RB1LA_1LC0RB_0LC1RD_0RB1LA = true.
Proof. vm_compute. reflexivity. Qed.

Lemma av_p_1RB1LA_1LC0RB_0LC1RD_0RB1LA : srun_avoid tm false true StA chp_1RB1LA_1LC0RB_0LC1RD_0RB1LA P0_1RB1LA_1LC0RB_0LC1RD_0RB1LA = true.
Proof. vm_compute. reflexivity. Qed.

Lemma av_ovf_1RB1LA_1LC0RB_0LC1RD_0RB1LA : srun_avoid tm true true StA cho_1RB1LA_1LC0RB_0LC1RD_0RB1LA B0_1RB1LA_1LC0RB_0LC1RD_0RB1LA = true.
Proof. vm_compute. reflexivity. Qed.

(** The full lap, avoidance carried on both branches. *)
Lemma lapav_1RB1LA_1LC0RB_0LC1RD_0RB1LA : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n
  /\ AvoidRun tm StA n (Cc p).
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct j as [|j'].
    + destruct (gz_1RB1LA_1LC0RB_0LC1RD_0RB1LA p q0 E) as (HA & HB).
      exists (0 * 0 + 4), (Cc (Pos.succ p)).
      split.
      { rewrite HA.
        rewrite (srun_sound tm false true chz_1RB1LA_1LC0RB_0LC1RD_0RB1LA Z0_1RB1LA_1LC0RB_0LC1RD_0RB1LA Z1_1RB1LA_1LC0RB_0LC1RD_0RB1LA 0 4
                   run_z_1RB1LA_1LC0RB_0LC1RD_0RB1LA (Kp q0 ++ [S0]) [] 0
                   ltac:(discriminate) ltac:(reflexivity)).
        f_equal. exact HB. }
      split; [reflexivity|]. split; [lia|].
      exact (avoid_of_run tm Cc false true StA chz_1RB1LA_1LC0RB_0LC1RD_0RB1LA Z0_1RB1LA_1LC0RB_0LC1RD_0RB1LA Z1_1RB1LA_1LC0RB_0LC1RD_0RB1LA
               0 4 p 0 (Kp q0 ++ [S0]) [] run_z_1RB1LA_1LC0RB_0LC1RD_0RB1LA av_z_1RB1LA_1LC0RB_0LC1RD_0RB1LA
               ltac:(discriminate) ltac:(reflexivity) HA).
    + destruct (gp_1RB1LA_1LC0RB_0LC1RD_0RB1LA p j' q0 E) as (HA & HB).
      exists (2 * j' + 6), (Cc (Pos.succ p)).
      split.
      { rewrite HA.
        rewrite (srun_sound tm false true chp_1RB1LA_1LC0RB_0LC1RD_0RB1LA P0_1RB1LA_1LC0RB_0LC1RD_0RB1LA P1_1RB1LA_1LC0RB_0LC1RD_0RB1LA 2 6
                   run_p_1RB1LA_1LC0RB_0LC1RD_0RB1LA (Kp q0 ++ [S0]) [] j'
                   ltac:(discriminate) ltac:(reflexivity)).
        f_equal. exact HB. }
      split; [reflexivity|]. split; [lia|].
      exact (avoid_of_run tm Cc false true StA chp_1RB1LA_1LC0RB_0LC1RD_0RB1LA P0_1RB1LA_1LC0RB_0LC1RD_0RB1LA P1_1RB1LA_1LC0RB_0LC1RD_0RB1LA
               2 6 p j' (Kp q0 ++ [S0]) [] run_p_1RB1LA_1LC0RB_0LC1RD_0RB1LA av_p_1RB1LA_1LC0RB_0LC1RD_0RB1LA
               ltac:(discriminate) ltac:(reflexivity) HA).
  - destruct (cview_pos p j E) as (j' & ->).
    exists (2 * j' + 6), (cden [] [] j' B1_1RB1LA_1LC0RB_0LC1RD_0RB1LA).
    split.
    { rewrite (gso_1RB1LA_1LC0RB_0LC1RD_0RB1LA p j' E).
      exact (srun_sound tm true true cho_1RB1LA_1LC0RB_0LC1RD_0RB1LA B0_1RB1LA_1LC0RB_0LC1RD_0RB1LA B1_1RB1LA_1LC0RB_0LC1RD_0RB1LA 2 6
               run_ovf_1RB1LA_1LC0RB_0LC1RD_0RB1LA [] [] j'
               ltac:(reflexivity) ltac:(reflexivity)). }
    split; [exact (geo_1RB1LA_1LC0RB_0LC1RD_0RB1LA p j' E)|]. split; [lia|].
    exact (avoid_of_run tm Cc true true StA cho_1RB1LA_1LC0RB_0LC1RD_0RB1LA B0_1RB1LA_1LC0RB_0LC1RD_0RB1LA B1_1RB1LA_1LC0RB_0LC1RD_0RB1LA
             2 6 p j' [] [] run_ovf_1RB1LA_1LC0RB_0LC1RD_0RB1LA av_ovf_1RB1LA_1LC0RB_0LC1RD_0RB1LA
             ltac:(reflexivity) ltac:(reflexivity) (gso_1RB1LA_1LC0RB_0LC1RD_0RB1LA p j' E)).
Qed.

(** The bootstrap at its CONCRETE index, StA's last visit, and the checked
    StA-free window between them. *)
Lemma bootc_1RB1LA_1LC0RB_0LC1RD_0RB1LA : stepn tm 10 InitES = Some (lift (Cc 2)).
Proof.
  assert (H : match csteps tm 10 c0 with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 10 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

Lemma bvis_1RB1LA_1LC0RB_0LC1RD_0RB1LA : VisitsAt tm StA 5.
Proof. apply bootvis_chk_sound. vm_compute. reflexivity. Qed.

Lemma bq_1RB1LA_1LC0RB_0LC1RD_0RB1LA : forall n c, 5 < n < 10 ->
  stepn tm n InitES = Some c -> fst c <> StA.
Proof.
  intros n c Hn Hc.
  refine (bootquiet_chk_sound tm StA (S 5) 4 _ n c _ Hc);
    [vm_compute; reflexivity | lia].
Qed.

Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.

Theorem iqhm_1RB1LA_1LC0RB_0LC1RD_0RB1LA : iqh tmm_1RB1LA_1LC0RB_0LC1RD_0RB1LA.
Proof.
  destruct (glue_qh_quiet tm Cc 2 StA 10 5
              bootc_1RB1LA_1LC0RB_0LC1RD_0RB1LA
              (fun p _ => lapav_1RB1LA_1LC0RB_0LC1RD_0RB1LA p)
              (fun p q _ Hq => vis_1RB1LA_1LC0RB_0LC1RD_0RB1LA p q Hq)
              bvis_1RB1LA_1LC0RB_0LC1RD_0RB1LA
              bq_1RB1LA_1LC0RB_0LC1RD_0RB1LA)
    as (Hn & Hb & Hq).
  split; [exact Hn | split; [| exact Hq]].
  apply (qhbound_mono (S 5) 2000); [lia | exact Hb].
Qed.

(** Transfer to the REAL machine.  [mirror_nonhalt] and [mirror_qh]
    are Mirror.v; [qhbound_mirror] is Census/TNF_QH.v. *)
Theorem iqh_1RB1LA_1LC0RB_0LC1RD_0RB1LA : iqh tm_1RB1LA_1LC0RB_0LC1RD_0RB1LA.
Proof.
  destruct iqhm_1RB1LA_1LC0RB_0LC1RD_0RB1LA as (Hn & Hb & Hq).
  rewrite <- mirror_ok_1RB1LA_1LC0RB_0LC1RD_0RB1LA in Hn, Hb, Hq.
  split; [exact (mirror_nonhalt _ Hn)
         | split; [exact (qhbound_mirror _ _ Hb)
                  | exact (mirror_qh _ Hq)]].
Qed.

Theorem nonhalt_1RB1LA_1LC0RB_0LC1RD_0RB1LA : NonHalt tm_1RB1LA_1LC0RB_0LC1RD_0RB1LA.
Proof. apply (proj1 iqh_1RB1LA_1LC0RB_0LC1RD_0RB1LA). Qed.
