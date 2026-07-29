(** * LAPC_1RB1LD_0LB1RC_1LA0RC_0RB0LB: machine 1RB1LD_0LB1RC_1LA0RC_0RB0LB, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Dp digit alphabet (DpCounter.v), anchored at

      Cc p = (StC, (Dp p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  j=0: 12 ; j=S j': 4*j'+16 steps
      overflow  (cview p = (S j, None)):   4*j+16 steps

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
                                  MonoCounter JpCounter DpCounter LapCertGlue LapCertGlueLift.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_1RB1LD_0LB1RC_1LA0RC_0RB0LB (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1LD_0LB1RC_1LA0RC_0RB0LB.

(** 1RB1LD_0LB1RC_1LA0RC_0RB0LB *)
(** 1RB1LD_0LB1RC_1LA0RC_0RB0LB -- the real machine (its counter grows RIGHT). *)
Definition tm_1RB1LD_0LB1RC_1LA0RC_0RB0LB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StD
  | StB, S0 => mk S0 DL StB | StB, S1 => mk S1 DR StC
  | StC, S0 => mk S1 DL StA | StC, S1 => mk S0 DR StC
  | StD, S0 => mk S0 DR StB | StD, S1 => mk S0 DL StB end.

(** Its mirror 1LB1RD_0RB1LC_1RA0LC_0LB0RB: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_1RB1LD_0LB1RC_1LA0RC_0RB0LB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => mk S1 DR StD
  | StB, S0 => mk S0 DR StB | StB, S1 => mk S1 DL StC
  | StC, S0 => mk S1 DR StA | StC, S1 => mk S0 DL StC
  | StD, S0 => mk S0 DL StB | StD, S1 => mk S0 DR StB end.
Local Notation tm := tmm_1RB1LD_0LB1RC_1LA0RC_0RB0LB.

Lemma mirror_ok_1RB1LD_0LB1RC_1LA0RC_0RB0LB : mirror_tm tm_1RB1LD_0LB1RC_1LA0RC_0RB0LB = tmm_1RB1LD_0LB1RC_1LA0RC_0RB0LB.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_1RB1LD_0LB1RC_1LA0RC_0RB0LB (p : positive) : cconf := (StC, (Dp p ++ [S0], S0, [S1])).
Local Notation Cc := Cc_1RB1LD_0LB1RC_1LA0RC_0RB0LB.

(** ** The certificate *)

(** j = 0: the repeated block is absent, so the whole lap is concrete. *)
Definition Z0_1RB1LD_0LB1RC_1LA0RC_0RB0LB : sconf := mkC StC (mkS [S0;S0] [] 0 0 []) S0 (mkS [S1] [] 0 0 []).
Definition Z1_1RB1LD_0LB1RC_1LA0RC_0RB0LB : sconf := mkC StC (mkS [S1;S1] [] 0 0 []) S0 (mkS [S1;S0] [] 0 0 []).
Definition chz_1RB1LD_0LB1RC_1LA0RC_0RB0LB : list lstep := [SWin 1; SWinR 11].

Lemma run_z_1RB1LD_0LB1RC_1LA0RC_0RB0LB : srun tm false true chz_1RB1LD_0LB1RC_1LA0RC_0RB0LB Z0_1RB1LD_0LB1RC_1LA0RC_0RB0LB = Some (Z1_1RB1LD_0LB1RC_1LA0RC_0RB0LB, 0, 12).
Proof. vm_compute. reflexivity. Qed.

(** j = S j': one copy of the unit sits in the PREFIX, so the head always has
    a concrete cell to step onto. *)
Definition P0_1RB1LD_0LB1RC_1LA0RC_0RB0LB : sconf := mkC StC (mkS [S1;S1] [S1;S1] 1 0 [S0;S0]) S0 (mkS [S1] [] 0 0 []).
Definition P1_1RB1LD_0LB1RC_1LA0RC_0RB0LB : sconf := mkC StC (mkS [S0;S0] [S0;S0] 1 0 [S1;S1]) S0 (mkS [S1;S0] [] 0 0 []).
Definition chp_1RB1LD_0LB1RC_1LA0RC_0RB0LB : list lstep := [SWin 1; SWinR 5; SCycL 2 0; SWin 6; SRotR 1; SWin 1; SCycR 2; SWin 3; SRotL 1].

Lemma run_p_1RB1LD_0LB1RC_1LA0RC_0RB0LB : srun tm false true chp_1RB1LD_0LB1RC_1LA0RC_0RB0LB P0_1RB1LD_0LB1RC_1LA0RC_0RB0LB = Some (P1_1RB1LD_0LB1RC_1LA0RC_0RB0LB, 4, 16).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB1LD_0LB1RC_1LA0RC_0RB0LB : sconf := mkC StC (mkS [S1;S1] [S1;S1] 1 0 [S0]) S0 (mkS [S1] [] 0 0 []).
Definition B1_1RB1LD_0LB1RC_1LA0RC_0RB0LB : sconf := mkC StC (mkS [] [S0;S0] 1 1 [S1;S1]) S0 (mkS [S1;S0] [] 0 0 []).
Definition cho_1RB1LD_0LB1RC_1LA0RC_0RB0LB : list lstep := [SWin 1; SWinR 5; SCycL 2 0; SWin 3; SWinL 3; SRotR 1; SWin 1; SCycR 2; SWin 3; SRotL 1; SFoldL 1].

Lemma run_ovf_1RB1LD_0LB1RC_1LA0RC_0RB0LB : srun tm true true cho_1RB1LD_0LB1RC_1LA0RC_0RB0LB B0_1RB1LD_0LB1RC_1LA0RC_0RB0LB = Some (B1_1RB1LD_0LB1RC_1LA0RC_0RB0LB, 4, 16).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gz_1RB1LD_0LB1RC_1LA0RC_0RB0LB : forall p q0, cview p = (0, Some q0) ->
  Cc p = cden (Dp q0 ++ [S0]) [] 0 Z0_1RB1LD_0LB1RC_1LA0RC_0RB0LB /\
  lift (cden (Dp q0 ++ [S0]) [] 0 Z1_1RB1LD_0LB1RC_1LA0RC_0RB0LB) = lift (Cc (Pos.succ p)).
Proof.
  intros p q0 E. destruct (DpCounter.cview_some_D p 0 q0 E) as (H1 & H2).
  unfold Cc_1RB1LD_0LB1RC_1LA0RC_0RB0LB, cden, Z0_1RB1LD_0LB1RC_1LA0RC_0RB0LB, Z1_1RB1LD_0LB1RC_1LA0RC_0RB0LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - cbn [rep app Nat.mul Nat.add]; rewrite ?app_nil_r.
    change ([S1;S0]) with (([S1]) ++ [S0]).
    rewrite !lift_app_blank.
    rewrite H2; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gp_1RB1LD_0LB1RC_1LA0RC_0RB0LB : forall p j q0, cview p = (S j, Some q0) ->
  Cc p = cden (Dp q0 ++ [S0]) [] j P0_1RB1LD_0LB1RC_1LA0RC_0RB0LB /\
  lift (cden (Dp q0 ++ [S0]) [] j P1_1RB1LD_0LB1RC_1LA0RC_0RB0LB) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (DpCounter.cview_some_D p (S j) q0 E) as (H1 & H2).
  unfold Cc_1RB1LD_0LB1RC_1LA0RC_0RB0LB, cden, P0_1RB1LD_0LB1RC_1LA0RC_0RB0LB, P1_1RB1LD_0LB1RC_1LA0RC_0RB0LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - cbn [rep app Nat.mul Nat.add]; rewrite ?app_nil_r.
    change ([S1;S0]) with (([S1]) ++ [S0]).
    rewrite !lift_app_blank.
    rewrite H2; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB1LD_0LB1RC_1LA0RC_0RB0LB : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct j as [|j'].
  - destruct (gz_1RB1LD_0LB1RC_1LA0RC_0RB0LB p q0 E) as (HA & HB).
    exists (0 * 0 + 12), (cden (Dp q0 ++ [S0]) [] 0 Z1_1RB1LD_0LB1RC_1LA0RC_0RB0LB).
    split; [lia|]. split; [| exact HB].
    rewrite HA.
    exact (srun_sound tm false true chz_1RB1LD_0LB1RC_1LA0RC_0RB0LB Z0_1RB1LD_0LB1RC_1LA0RC_0RB0LB Z1_1RB1LD_0LB1RC_1LA0RC_0RB0LB 0 12
             run_z_1RB1LD_0LB1RC_1LA0RC_0RB0LB (Dp q0 ++ [S0]) [] 0
             ltac:(discriminate) ltac:(reflexivity)).
  - destruct (gp_1RB1LD_0LB1RC_1LA0RC_0RB0LB p j' q0 E) as (HA & HB).
    exists (4 * j' + 16), (cden (Dp q0 ++ [S0]) [] j' P1_1RB1LD_0LB1RC_1LA0RC_0RB0LB).
    split; [lia|]. split; [| exact HB].
    rewrite HA.
    exact (srun_sound tm false true chp_1RB1LD_0LB1RC_1LA0RC_0RB0LB P0_1RB1LD_0LB1RC_1LA0RC_0RB0LB P1_1RB1LD_0LB1RC_1LA0RC_0RB0LB 4 16
             run_p_1RB1LD_0LB1RC_1LA0RC_0RB0LB (Dp q0 ++ [S0]) [] j'
             ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma gso_1RB1LD_0LB1RC_1LA0RC_0RB0LB : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_1RB1LD_0LB1RC_1LA0RC_0RB0LB.
Proof.
  intros p j E. destruct (DpCounter.cview_none_D p j E) as (H1 & _).
  unfold Cc_1RB1LD_0LB1RC_1LA0RC_0RB0LB, cden, B0_1RB1LD_0LB1RC_1LA0RC_0RB0LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB1LD_0LB1RC_1LA0RC_0RB0LB : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB1LD_0LB1RC_1LA0RC_0RB0LB : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB1LD_0LB1RC_1LA0RC_0RB0LB) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (DpCounter.cview_none_D p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB1LD_0LB1RC_1LA0RC_0RB0LB
             = (StC, (rep [S0;S0] (S j) ++ [S1;S1], S0, ([S1]) ++ [S0]))).
  { unfold cden, B1_1RB1LD_0LB1RC_1LA0RC_0RB0LB, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StC, ((rep [S0;S0] (S j) ++ [S1;S1]) ++ [S0], S0, [S1]))).
  { unfold Cc_1RB1LD_0LB1RC_1LA0RC_0RB0LB. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lift_app_blank. rewrite !lbl_1RB1LD_0LB1RC_1LA0RC_0RB0LB. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_1RB1LD_0LB1RC_1LA0RC_0RB0LB : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB1LD_0LB1RC_1LA0RC_0RB0LB p j q0 E) as (n & c' & Hn & Hrun & Hlift).
    exists n, c'. split; [exact Hrun | split; [exact Hlift | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_1RB1LD_0LB1RC_1LA0RC_0RB0LB B0_1RB1LD_0LB1RC_1LA0RC_0RB0LB B1_1RB1LD_0LB1RC_1LA0RC_0RB0LB 4 16 p j' [] []).
    + exact run_ovf_1RB1LD_0LB1RC_1LA0RC_0RB0LB.
    + reflexivity.
    + reflexivity.
    + exact (gso_1RB1LD_0LB1RC_1LA0RC_0RB0LB p j' E).
    + exact (geo_1RB1LD_0LB1RC_1LA0RC_0RB0LB p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_1RB1LD_0LB1RC_1LA0RC_0RB0LB : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 15.
  assert (H : match csteps tm 15 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 15 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma viso_1RB1LD_0LB1RC_1LA0RC_0RB0LB : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_1RB1LD_0LB1RC_1LA0RC_0RB0LB = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_1RB1LD_0LB1RC_1LA0RC_0RB0LB p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB1LD_0LB1RC_1LA0RC_0RB0LB p j E)].
Qed.

Lemma vis_1RB1LD_0LB1RC_1LA0RC_0RB0LB : forall p q, exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros p q.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n c', 0 < n /\ csteps tm n (Cc p0) = Some c'
                         /\ lift c' = lift (Cc (Pos.succ p0)))
    by exact lapi_1RB1LD_0LB1RC_1LA0RC_0RB0LB.
  destruct q.

  - (* StA *)
    apply (vis_via_ovf_lift tm Cc Hi StA).
    intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
    apply (viso_1RB1LD_0LB1RC_1LA0RC_0RB0LB [SWin 1] StA ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* StB *)
    apply (vis_via_ovf_lift tm Cc Hi StB).
    intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
    apply (viso_1RB1LD_0LB1RC_1LA0RC_0RB0LB [SWin 1; SWinR 2] StB ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* StC: the anchor state *)
    exists 0. eexists. split; reflexivity.
  - (* StD *)
    apply (vis_via_ovf_lift tm Cc Hi StD).
    intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
    apply (viso_1RB1LD_0LB1RC_1LA0RC_0RB0LB [SWin 1; SWinR 1] StD ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
Qed.

(** The interior lap closes only up to [lift] (one trailing blank past the
    anchor's far side), so the closer is [LapCertGlueLift.glue_neverqh_lift]:
    [LapGlue.glue_neverqh] with the visit premise in [stepn] space, which is
    what its own proof consumes. *)
Theorem nqhm_1RB1LD_0LB1RC_1LA0RC_0RB0LB : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh_lift tm Cc 1). - exact boot_1RB1LD_0LB1RC_1LA0RC_0RB0LB. - intros p _. apply lap_1RB1LD_0LB1RC_1LA0RC_0RB0LB. - intros p q _. apply vis_1RB1LD_0LB1RC_1LA0RC_0RB0LB. Qed.

Theorem nqh_1RB1LD_0LB1RC_1LA0RC_0RB0LB : NeverQuasiHaltsSt tm_1RB1LD_0LB1RC_1LA0RC_0RB0LB.
Proof. apply (mirror_never_qh tm_1RB1LD_0LB1RC_1LA0RC_0RB0LB). rewrite mirror_ok_1RB1LD_0LB1RC_1LA0RC_0RB0LB. exact nqhm_1RB1LD_0LB1RC_1LA0RC_0RB0LB. Qed.

Theorem nonhalt_1RB1LD_0LB1RC_1LA0RC_0RB0LB : NonHalt tm_1RB1LD_0LB1RC_1LA0RC_0RB0LB.
Proof. apply never_qh_nonhalt, nqh_1RB1LD_0LB1RC_1LA0RC_0RB0LB. Qed.
