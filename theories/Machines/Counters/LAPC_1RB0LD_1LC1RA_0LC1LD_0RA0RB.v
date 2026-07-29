(** * LAPC_1RB0LD_1LC1RA_0LC1LD_0RA0RB: machine 1RB0LD_1LC1RA_0LC1LD_0RA0RB, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Dp digit alphabet (DpCounter.v), anchored at

      Cc p = (StC, (Dp p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  j=0: 60 ; j=S j': 20*j'+80 steps
      overflow  (cview p = (S j, None)):   20*j+80 steps

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

Definition mk_1RB0LD_1LC1RA_0LC1LD_0RA0RB (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB0LD_1LC1RA_0LC1LD_0RA0RB.

(** 1RB0LD_1LC1RA_0LC1LD_0RA0RB *)
(** 1RB0LD_1LC1RA_0LC1LD_0RA0RB -- the real machine (its counter grows RIGHT). *)
Definition tm_1RB0LD_1LC1RA_0LC1LD_0RA0RB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StD
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StA
  | StC, S0 => mk S0 DL StC | StC, S1 => mk S1 DL StD
  | StD, S0 => mk S0 DR StA | StD, S1 => mk S0 DR StB end.

(** Its mirror 1LB0RD_1RC1LA_0RC1RD_0LA0LB: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_1RB0LD_1LC1RA_0LC1LD_0RA0RB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => mk S0 DR StD
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DL StA
  | StC, S0 => mk S0 DR StC | StC, S1 => mk S1 DR StD
  | StD, S0 => mk S0 DL StA | StD, S1 => mk S0 DL StB end.
Local Notation tm := tmm_1RB0LD_1LC1RA_0LC1LD_0RA0RB.

Lemma mirror_ok_1RB0LD_1LC1RA_0LC1LD_0RA0RB : mirror_tm tm_1RB0LD_1LC1RA_0LC1LD_0RA0RB = tmm_1RB0LD_1LC1RA_0LC1LD_0RA0RB.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_1RB0LD_1LC1RA_0LC1LD_0RA0RB (p : positive) : cconf := (StC, (Dp p ++ [S0], S0, [S0;S0;S1])).
Local Notation Cc := Cc_1RB0LD_1LC1RA_0LC1LD_0RA0RB.

(** ** The certificate *)

(** j = 0: the repeated block is absent, so the whole lap is concrete. *)
Definition Z0_1RB0LD_1LC1RA_0LC1LD_0RA0RB : sconf := mkC StC (mkS [S0;S0] [] 0 0 []) S0 (mkS [S0;S0;S1] [] 0 0 []).
Definition Z1_1RB0LD_1LC1RA_0LC1LD_0RA0RB : sconf := mkC StC (mkS [S1;S1] [] 0 0 []) S0 (mkS [S0;S0;S1;S0] [] 0 0 []).
Definition chz_1RB0LD_1LC1RA_0LC1LD_0RA0RB : list lstep := [SWin 3; SWinR 57].

Lemma run_z_1RB0LD_1LC1RA_0LC1LD_0RA0RB : srun tm false true chz_1RB0LD_1LC1RA_0LC1LD_0RA0RB Z0_1RB0LD_1LC1RA_0LC1LD_0RA0RB = Some (Z1_1RB0LD_1LC1RA_0LC1LD_0RA0RB, 0, 60).
Proof. vm_compute. reflexivity. Qed.

(** j = S j': one copy of the unit sits in the PREFIX, so the head always has
    a concrete cell to step onto. *)
Definition P0_1RB0LD_1LC1RA_0LC1LD_0RA0RB : sconf := mkC StC (mkS [S1;S1] [S1;S1] 1 0 [S0;S0]) S0 (mkS [S0;S0;S1] [] 0 0 []).
Definition P1_1RB0LD_1LC1RA_0LC1LD_0RA0RB : sconf := mkC StC (mkS [S0;S0] [S0;S0] 1 0 [S1;S1]) S0 (mkS [S0;S0;S1;S0] [] 0 0 []).
Definition chp_1RB0LD_1LC1RA_0LC1LD_0RA0RB : list lstep := [SWin 3; SWinR 45; SWin 2; SWin 6; SCycL 18 2; SWin 24; SCycR 2; SRotL 2].

Lemma run_p_1RB0LD_1LC1RA_0LC1LD_0RA0RB : srun tm false true chp_1RB0LD_1LC1RA_0LC1LD_0RA0RB P0_1RB0LD_1LC1RA_0LC1LD_0RA0RB = Some (P1_1RB0LD_1LC1RA_0LC1LD_0RA0RB, 20, 80).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB0LD_1LC1RA_0LC1LD_0RA0RB : sconf := mkC StC (mkS [S1;S1] [S1;S1] 1 0 [S0]) S0 (mkS [S0;S0;S1] [] 0 0 []).
Definition B1_1RB0LD_1LC1RA_0LC1LD_0RA0RB : sconf := mkC StC (mkS [] [S0;S0] 1 1 [S1;S1]) S0 (mkS [S0;S0;S1;S0] [] 0 0 []).
Definition cho_1RB0LD_1LC1RA_0LC1LD_0RA0RB : list lstep := [SWin 3; SWinR 45; SWin 2; SWin 6; SCycL 18 2; SWin 1; SWinL 23; SCycR 2; SRotL 2; SFoldL 1].

Lemma run_ovf_1RB0LD_1LC1RA_0LC1LD_0RA0RB : srun tm true true cho_1RB0LD_1LC1RA_0LC1LD_0RA0RB B0_1RB0LD_1LC1RA_0LC1LD_0RA0RB = Some (B1_1RB0LD_1LC1RA_0LC1LD_0RA0RB, 20, 80).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gz_1RB0LD_1LC1RA_0LC1LD_0RA0RB : forall p q0, cview p = (0, Some q0) ->
  Cc p = cden (Dp q0 ++ [S0]) [] 0 Z0_1RB0LD_1LC1RA_0LC1LD_0RA0RB /\
  lift (cden (Dp q0 ++ [S0]) [] 0 Z1_1RB0LD_1LC1RA_0LC1LD_0RA0RB) = lift (Cc (Pos.succ p)).
Proof.
  intros p q0 E. destruct (DpCounter.cview_some_D p 0 q0 E) as (H1 & H2).
  unfold Cc_1RB0LD_1LC1RA_0LC1LD_0RA0RB, cden, Z0_1RB0LD_1LC1RA_0LC1LD_0RA0RB, Z1_1RB0LD_1LC1RA_0LC1LD_0RA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - cbn [rep app Nat.mul Nat.add]; rewrite ?app_nil_r.
    change ([S0;S0;S1;S0]) with (([S0;S0;S1]) ++ [S0]).
    rewrite !lift_app_blank.
    rewrite H2; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gp_1RB0LD_1LC1RA_0LC1LD_0RA0RB : forall p j q0, cview p = (S j, Some q0) ->
  Cc p = cden (Dp q0 ++ [S0]) [] j P0_1RB0LD_1LC1RA_0LC1LD_0RA0RB /\
  lift (cden (Dp q0 ++ [S0]) [] j P1_1RB0LD_1LC1RA_0LC1LD_0RA0RB) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (DpCounter.cview_some_D p (S j) q0 E) as (H1 & H2).
  unfold Cc_1RB0LD_1LC1RA_0LC1LD_0RA0RB, cden, P0_1RB0LD_1LC1RA_0LC1LD_0RA0RB, P1_1RB0LD_1LC1RA_0LC1LD_0RA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - cbn [rep app Nat.mul Nat.add]; rewrite ?app_nil_r.
    change ([S0;S0;S1;S0]) with (([S0;S0;S1]) ++ [S0]).
    rewrite !lift_app_blank.
    rewrite H2; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB0LD_1LC1RA_0LC1LD_0RA0RB : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct j as [|j'].
  - destruct (gz_1RB0LD_1LC1RA_0LC1LD_0RA0RB p q0 E) as (HA & HB).
    exists (0 * 0 + 60), (cden (Dp q0 ++ [S0]) [] 0 Z1_1RB0LD_1LC1RA_0LC1LD_0RA0RB).
    split; [lia|]. split; [| exact HB].
    rewrite HA.
    exact (srun_sound tm false true chz_1RB0LD_1LC1RA_0LC1LD_0RA0RB Z0_1RB0LD_1LC1RA_0LC1LD_0RA0RB Z1_1RB0LD_1LC1RA_0LC1LD_0RA0RB 0 60
             run_z_1RB0LD_1LC1RA_0LC1LD_0RA0RB (Dp q0 ++ [S0]) [] 0
             ltac:(discriminate) ltac:(reflexivity)).
  - destruct (gp_1RB0LD_1LC1RA_0LC1LD_0RA0RB p j' q0 E) as (HA & HB).
    exists (20 * j' + 80), (cden (Dp q0 ++ [S0]) [] j' P1_1RB0LD_1LC1RA_0LC1LD_0RA0RB).
    split; [lia|]. split; [| exact HB].
    rewrite HA.
    exact (srun_sound tm false true chp_1RB0LD_1LC1RA_0LC1LD_0RA0RB P0_1RB0LD_1LC1RA_0LC1LD_0RA0RB P1_1RB0LD_1LC1RA_0LC1LD_0RA0RB 20 80
             run_p_1RB0LD_1LC1RA_0LC1LD_0RA0RB (Dp q0 ++ [S0]) [] j'
             ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma gso_1RB0LD_1LC1RA_0LC1LD_0RA0RB : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_1RB0LD_1LC1RA_0LC1LD_0RA0RB.
Proof.
  intros p j E. destruct (DpCounter.cview_none_D p j E) as (H1 & _).
  unfold Cc_1RB0LD_1LC1RA_0LC1LD_0RA0RB, cden, B0_1RB0LD_1LC1RA_0LC1LD_0RA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB0LD_1LC1RA_0LC1LD_0RA0RB : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB0LD_1LC1RA_0LC1LD_0RA0RB : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB0LD_1LC1RA_0LC1LD_0RA0RB) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (DpCounter.cview_none_D p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB0LD_1LC1RA_0LC1LD_0RA0RB
             = (StC, (rep [S0;S0] (S j) ++ [S1;S1], S0, ([S0;S0;S1]) ++ [S0]))).
  { unfold cden, B1_1RB0LD_1LC1RA_0LC1LD_0RA0RB, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StC, ((rep [S0;S0] (S j) ++ [S1;S1]) ++ [S0], S0, [S0;S0;S1]))).
  { unfold Cc_1RB0LD_1LC1RA_0LC1LD_0RA0RB. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lift_app_blank. rewrite !lbl_1RB0LD_1LC1RA_0LC1LD_0RA0RB. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_1RB0LD_1LC1RA_0LC1LD_0RA0RB : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB0LD_1LC1RA_0LC1LD_0RA0RB p j q0 E) as (n & c' & Hn & Hrun & Hlift).
    exists n, c'. split; [exact Hrun | split; [exact Hlift | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_1RB0LD_1LC1RA_0LC1LD_0RA0RB B0_1RB0LD_1LC1RA_0LC1LD_0RA0RB B1_1RB0LD_1LC1RA_0LC1LD_0RA0RB 20 80 p j' [] []).
    + exact run_ovf_1RB0LD_1LC1RA_0LC1LD_0RA0RB.
    + reflexivity.
    + reflexivity.
    + exact (gso_1RB0LD_1LC1RA_0LC1LD_0RA0RB p j' E).
    + exact (geo_1RB0LD_1LC1RA_0LC1LD_0RA0RB p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_1RB0LD_1LC1RA_0LC1LD_0RA0RB : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 53.
  assert (H : match csteps tm 53 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 53 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma viso_1RB0LD_1LC1RA_0LC1LD_0RA0RB : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_1RB0LD_1LC1RA_0LC1LD_0RA0RB = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_1RB0LD_1LC1RA_0LC1LD_0RA0RB p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB0LD_1LC1RA_0LC1LD_0RA0RB p j E)].
Qed.

Lemma vis_1RB0LD_1LC1RA_0LC1LD_0RA0RB : forall p q, exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros p q.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n c', 0 < n /\ csteps tm n (Cc p0) = Some c'
                         /\ lift c' = lift (Cc (Pos.succ p0)))
    by exact lapi_1RB0LD_1LC1RA_0LC1LD_0RA0RB.
  destruct q.

  - (* StA *)
    apply (vis_via_ovf_lift tm Cc Hi StA).
    intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
    apply (viso_1RB0LD_1LC1RA_0LC1LD_0RA0RB [SWin 3; SWinR 2] StA ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* StB *)
    apply (vis_via_ovf_lift tm Cc Hi StB).
    intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
    apply (viso_1RB0LD_1LC1RA_0LC1LD_0RA0RB [SWin 3; SWinR 5] StB ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* StC: the anchor state *)
    exists 0. eexists. split; reflexivity.
  - (* StD *)
    apply (vis_via_ovf_lift tm Cc Hi StD).
    intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
    apply (viso_1RB0LD_1LC1RA_0LC1LD_0RA0RB [SWin 3; SWinR 1] StD ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
Qed.

(** The interior lap closes only up to [lift] (one trailing blank past the
    anchor's far side), so the closer is [LapCertGlueLift.glue_neverqh_lift]:
    [LapGlue.glue_neverqh] with the visit premise in [stepn] space, which is
    what its own proof consumes. *)
Theorem nqhm_1RB0LD_1LC1RA_0LC1LD_0RA0RB : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh_lift tm Cc 1). - exact boot_1RB0LD_1LC1RA_0LC1LD_0RA0RB. - intros p _. apply lap_1RB0LD_1LC1RA_0LC1LD_0RA0RB. - intros p q _. apply vis_1RB0LD_1LC1RA_0LC1LD_0RA0RB. Qed.

Theorem nqh_1RB0LD_1LC1RA_0LC1LD_0RA0RB : NeverQuasiHaltsSt tm_1RB0LD_1LC1RA_0LC1LD_0RA0RB.
Proof. apply (mirror_never_qh tm_1RB0LD_1LC1RA_0LC1LD_0RA0RB). rewrite mirror_ok_1RB0LD_1LC1RA_0LC1LD_0RA0RB. exact nqhm_1RB0LD_1LC1RA_0LC1LD_0RA0RB. Qed.

Theorem nonhalt_1RB0LD_1LC1RA_0LC1LD_0RA0RB : NonHalt tm_1RB0LD_1LC1RA_0LC1LD_0RA0RB.
Proof. apply never_qh_nonhalt, nqh_1RB0LD_1LC1RA_0LC1LD_0RA0RB. Qed.
