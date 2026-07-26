(** * LAPC_1RB1RC_1LA1LB_1LA0RD_0RC0LC: machine 1RB1RC_1LA1LB_1LA0RD_0RC0LC, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Jp digit alphabet (JpCounter.v), anchored at

      Cc p = (StA, (Jp p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  j=0: 14 ; j=S j': 6*j'+20 steps
      overflow  (cview p = (S j, None)):   6*j+18 steps

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 198 anchors.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH MonoCounter
                                  JpCounter JpCounter LapCertGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_1RB1RC_1LA1LB_1LA0RD_0RC0LC (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1RC_1LA1LB_1LA0RD_0RC0LC.

(** 1RB1RC_1LA1LB_1LA0RD_0RC0LC *)
(** 1RB1RC_1LA1LB_1LA0RD_0RC0LC -- the real machine (its counter grows RIGHT). *)
Definition tm_1RB1RC_1LA1LB_1LA0RD_0RC0LC : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DR StC
  | StB, S0 => mk S1 DL StA | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S1 DL StA | StC, S1 => mk S0 DR StD
  | StD, S0 => mk S0 DR StC | StD, S1 => mk S0 DL StC end.

(** Its mirror 1LB1LC_1RA1RB_1RA0LD_0LC0RC: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_1RB1RC_1LA1LB_1LA0RD_0RC0LC : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => mk S1 DL StC
  | StB, S0 => mk S1 DR StA | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S1 DR StA | StC, S1 => mk S0 DL StD
  | StD, S0 => mk S0 DL StC | StD, S1 => mk S0 DR StC end.
Local Notation tm := tmm_1RB1RC_1LA1LB_1LA0RD_0RC0LC.

Lemma mirror_ok_1RB1RC_1LA1LB_1LA0RD_0RC0LC : mirror_tm tm_1RB1RC_1LA1LB_1LA0RD_0RC0LC = tmm_1RB1RC_1LA1LB_1LA0RD_0RC0LC.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_1RB1RC_1LA1LB_1LA0RD_0RC0LC (p : positive) : cconf := (StA, (Jp p ++ [S0], S0, [S0;S1])).
Local Notation Cc := Cc_1RB1RC_1LA1LB_1LA0RD_0RC0LC.

(** ** The certificate *)

(** j = 0: the repeated block is absent, so the whole lap is concrete. *)
Definition Z0_1RB1RC_1LA1LB_1LA0RD_0RC0LC : sconf := mkC StA (mkS [S1;S1] [] 0 0 []) S0 (mkS [S0;S1] [] 0 0 []).
Definition Z1_1RB1RC_1LA1LB_1LA0RD_0RC0LC : sconf := mkC StA (mkS [S1;S0] [] 0 0 []) S0 (mkS [S0;S1] [] 0 0 []).
Definition chz_1RB1RC_1LA1LB_1LA0RD_0RC0LC : list lstep := [SWin 14].

Lemma run_z_1RB1RC_1LA1LB_1LA0RD_0RC0LC : srun tm false true chz_1RB1RC_1LA1LB_1LA0RD_0RC0LC Z0_1RB1RC_1LA1LB_1LA0RD_0RC0LC = Some (Z1_1RB1RC_1LA1LB_1LA0RD_0RC0LC, 0, 14).
Proof. vm_compute. reflexivity. Qed.

(** j = S j': one copy of the unit sits in the PREFIX, so the head always has
    a concrete cell to step onto. *)
Definition P0_1RB1RC_1LA1LB_1LA0RD_0RC0LC : sconf := mkC StA (mkS [S1;S0] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S0;S1] [] 0 0 []).
Definition P1_1RB1RC_1LA1LB_1LA0RD_0RC0LC : sconf := mkC StA (mkS [S1;S1] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S0;S1] [] 0 0 []).
Definition chp_1RB1RC_1LA1LB_1LA0RD_0RC0LC : list lstep := [SWin 12; SCycL 2 0; SWin 6; SCycR 4; SWin 2].

Lemma run_p_1RB1RC_1LA1LB_1LA0RD_0RC0LC : srun tm false true chp_1RB1RC_1LA1LB_1LA0RD_0RC0LC P0_1RB1RC_1LA1LB_1LA0RD_0RC0LC = Some (P1_1RB1RC_1LA1LB_1LA0RD_0RC0LC, 6, 20).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB1RC_1LA1LB_1LA0RD_0RC0LC : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S0]) S0 (mkS [S0;S1] [] 0 0 []).
Definition B1_1RB1RC_1LA1LB_1LA0RD_0RC0LC : sconf := mkC StA (mkS [] [S1;S1] 1 1 [S1]) S0 (mkS [S0;S1] [] 0 0 []).
Definition cho_1RB1RC_1LA1LB_1LA0RD_0RC0LC : list lstep := [SRotL 1; SWin 11; SCycL 2 0; SWin 1; SWinL 5; SCycR 4; SWin 1; SRotL 1; SFoldL 1].

Lemma run_ovf_1RB1RC_1LA1LB_1LA0RD_0RC0LC : srun tm true true cho_1RB1RC_1LA1LB_1LA0RD_0RC0LC B0_1RB1RC_1LA1LB_1LA0RD_0RC0LC = Some (B1_1RB1RC_1LA1LB_1LA0RD_0RC0LC, 6, 18).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gz_1RB1RC_1LA1LB_1LA0RD_0RC0LC : forall p q0, cview p = (0, Some q0) ->
  Cc p = cden (Jp q0 ++ [S0]) [] 0 Z0_1RB1RC_1LA1LB_1LA0RD_0RC0LC /\
  cden (Jp q0 ++ [S0]) [] 0 Z1_1RB1RC_1LA1LB_1LA0RD_0RC0LC = Cc (Pos.succ p).
Proof.
  intros p q0 E. destruct (JpCounter.cview_some_J p 0 q0 E) as (H1 & H2).
  unfold Cc_1RB1RC_1LA1LB_1LA0RD_0RC0LC, cden, Z0_1RB1RC_1LA1LB_1LA0RD_0RC0LC, Z1_1RB1RC_1LA1LB_1LA0RD_0RC0LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gp_1RB1RC_1LA1LB_1LA0RD_0RC0LC : forall p j q0, cview p = (S j, Some q0) ->
  Cc p = cden (Jp q0 ++ [S0]) [] j P0_1RB1RC_1LA1LB_1LA0RD_0RC0LC /\
  cden (Jp q0 ++ [S0]) [] j P1_1RB1RC_1LA1LB_1LA0RD_0RC0LC = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p (S j) q0 E) as (H1 & H2).
  unfold Cc_1RB1RC_1LA1LB_1LA0RD_0RC0LC, cden, P0_1RB1RC_1LA1LB_1LA0RD_0RC0LC, P1_1RB1RC_1LA1LB_1LA0RD_0RC0LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB1RC_1LA1LB_1LA0RD_0RC0LC : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct j as [|j'].
  - destruct (gz_1RB1RC_1LA1LB_1LA0RD_0RC0LC p q0 E) as (HA & HB).
    exists (0 * 0 + 14). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chz_1RB1RC_1LA1LB_1LA0RD_0RC0LC Z0_1RB1RC_1LA1LB_1LA0RD_0RC0LC Z1_1RB1RC_1LA1LB_1LA0RD_0RC0LC 0 14
               run_z_1RB1RC_1LA1LB_1LA0RD_0RC0LC (Jp q0 ++ [S0]) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gp_1RB1RC_1LA1LB_1LA0RD_0RC0LC p j' q0 E) as (HA & HB).
    exists (6 * j' + 20). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chp_1RB1RC_1LA1LB_1LA0RD_0RC0LC P0_1RB1RC_1LA1LB_1LA0RD_0RC0LC P1_1RB1RC_1LA1LB_1LA0RD_0RC0LC 6 20
               run_p_1RB1RC_1LA1LB_1LA0RD_0RC0LC (Jp q0 ++ [S0]) [] j'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
Qed.

Lemma gso_1RB1RC_1LA1LB_1LA0RD_0RC0LC : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_1RB1RC_1LA1LB_1LA0RD_0RC0LC.
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (H1 & _).
  unfold Cc_1RB1RC_1LA1LB_1LA0RD_0RC0LC, cden, B0_1RB1RC_1LA1LB_1LA0RD_0RC0LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB1RC_1LA1LB_1LA0RD_0RC0LC : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB1RC_1LA1LB_1LA0RD_0RC0LC : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB1RC_1LA1LB_1LA0RD_0RC0LC) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB1RC_1LA1LB_1LA0RD_0RC0LC
             = (StA, (rep [S1;S1] (S j) ++ [S1], S0, [S0;S1]))).
  { unfold cden, B1_1RB1RC_1LA1LB_1LA0RD_0RC0LC, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. reflexivity. }
  assert (HC : Cc (Pos.succ p) = (StA, ((rep [S1;S1] (S j) ++ [S1]) ++ [S0], S0, [S0;S1]))).
  { unfold Cc_1RB1RC_1LA1LB_1LA0RD_0RC0LC. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_1RB1RC_1LA1LB_1LA0RD_0RC0LC. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_1RB1RC_1LA1LB_1LA0RD_0RC0LC : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB1RC_1LA1LB_1LA0RD_0RC0LC p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_1RB1RC_1LA1LB_1LA0RD_0RC0LC B0_1RB1RC_1LA1LB_1LA0RD_0RC0LC B1_1RB1RC_1LA1LB_1LA0RD_0RC0LC 6 18 p j' [] []).
    + exact run_ovf_1RB1RC_1LA1LB_1LA0RD_0RC0LC.
    + reflexivity.
    + reflexivity.
    + exact (gso_1RB1RC_1LA1LB_1LA0RD_0RC0LC p j' E).
    + exact (geo_1RB1RC_1LA1LB_1LA0RD_0RC0LC p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_1RB1RC_1LA1LB_1LA0RD_0RC0LC : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 6.
  assert (H : match csteps tm 6 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 6 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma viso_1RB1RC_1LA1LB_1LA0RD_0RC0LC : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_1RB1RC_1LA1LB_1LA0RD_0RC0LC = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_1RB1RC_1LA1LB_1LA0RD_0RC0LC p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB1RC_1LA1LB_1LA0RD_0RC0LC p j E)].
Qed.

Lemma vis_1RB1RC_1LA1LB_1LA0RD_0RC0LC : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_1RB1RC_1LA1LB_1LA0RD_0RC0LC.
  destruct q.

  - (* StA: the anchor state *)
    exists 0. eexists. split; reflexivity.
  - (* StB *)
    apply (vis_via_ovf tm Cc Hi StB), viso_1RB1RC_1LA1LB_1LA0RD_0RC0LC
      with (l := [SRotL 1; SWin 1]).
    vm_compute; reflexivity.
  - (* StC *)
    apply (vis_via_ovf tm Cc Hi StC), viso_1RB1RC_1LA1LB_1LA0RD_0RC0LC
      with (l := [SRotL 1; SWin 5]).
    vm_compute; reflexivity.
  - (* StD *)
    apply (vis_via_ovf tm Cc Hi StD), viso_1RB1RC_1LA1LB_1LA0RD_0RC0LC
      with (l := [SRotL 1; SWin 6]).
    vm_compute; reflexivity.
Qed.

Theorem nqhm_1RB1RC_1LA1LB_1LA0RD_0RC0LC : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 1). - exact boot_1RB1RC_1LA1LB_1LA0RD_0RC0LC. - intros p _. apply lap_1RB1RC_1LA1LB_1LA0RD_0RC0LC. - intros p q _. apply vis_1RB1RC_1LA1LB_1LA0RD_0RC0LC. Qed.

Theorem nqh_1RB1RC_1LA1LB_1LA0RD_0RC0LC : NeverQuasiHaltsSt tm_1RB1RC_1LA1LB_1LA0RD_0RC0LC.
Proof. apply (mirror_never_qh tm_1RB1RC_1LA1LB_1LA0RD_0RC0LC). rewrite mirror_ok_1RB1RC_1LA1LB_1LA0RD_0RC0LC. exact nqhm_1RB1RC_1LA1LB_1LA0RD_0RC0LC. Qed.

Theorem nonhalt_1RB1RC_1LA1LB_1LA0RD_0RC0LC : NonHalt tm_1RB1RC_1LA1LB_1LA0RD_0RC0LC.
Proof. apply never_qh_nonhalt, nqh_1RB1RC_1LA1LB_1LA0RD_0RC0LC. Qed.
