(** * LAPC_0RB0RA_1RC0RC_1LD1RB_0LD0LA: machine 0RB0RA_1RC0RC_1LD1RB_0LD0LA, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Ap_Alph_000_010_01 digit alphabet (Alph_000_010_01.v), anchored at

      Cc p = (StA, (Ap_Alph_000_010_01 p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  j=0: 4 ; j=S j': 10*j'+14 steps
      overflow  (cview p = (S j, None)):   10*j+14 steps

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
                                  JpCounter Alph_000_010_01 LapCertGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_0RB0RA_1RC0RC_1LD1RB_0LD0LA (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB0RA_1RC0RC_1LD1RB_0LD0LA.

(** 0RB0RA_1RC0RC_1LD1RB_0LD0LA *)
(** 0RB0RA_1RC0RC_1LD1RB_0LD0LA -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB0RA_1RC0RC_1LD1RB_0LD0LA : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S0 DR StA
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S0 DR StC
  | StC, S0 => mk S1 DL StD | StC, S1 => mk S1 DR StB
  | StD, S0 => mk S0 DL StD | StD, S1 => mk S0 DL StA end.

(** Its mirror 0LB0LA_1LC0LC_1RD1LB_0RD0RA: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB0RA_1RC0RC_1LD1RB_0LD0LA : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S0 DL StA
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DL StC
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S1 DL StB
  | StD, S0 => mk S0 DR StD | StD, S1 => mk S0 DR StA end.
Local Notation tm := tmm_0RB0RA_1RC0RC_1LD1RB_0LD0LA.

Lemma mirror_ok_0RB0RA_1RC0RC_1LD1RB_0LD0LA : mirror_tm tm_0RB0RA_1RC0RC_1LD1RB_0LD0LA = tmm_0RB0RA_1RC0RC_1LD1RB_0LD0LA.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_0RB0RA_1RC0RC_1LD1RB_0LD0LA (p : positive) : cconf := (StA, (Ap_Alph_000_010_01 p ++ [S0], S0, [])).
Local Notation Cc := Cc_0RB0RA_1RC0RC_1LD1RB_0LD0LA.

(** ** The certificate *)

(** j = 0: the repeated block is absent, so the whole lap is concrete. *)
Definition Z0_0RB0RA_1RC0RC_1LD1RB_0LD0LA : sconf := mkC StA (mkS [S0;S0;S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition Z1_0RB0RA_1RC0RC_1LD1RB_0LD0LA : sconf := mkC StA (mkS [S0;S1;S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition chz_0RB0RA_1RC0RC_1LD1RB_0LD0LA : list lstep := [SWin 4].

Lemma run_z_0RB0RA_1RC0RC_1LD1RB_0LD0LA : srun tm false true chz_0RB0RA_1RC0RC_1LD1RB_0LD0LA Z0_0RB0RA_1RC0RC_1LD1RB_0LD0LA = Some (Z1_0RB0RA_1RC0RC_1LD1RB_0LD0LA, 0, 4).
Proof. vm_compute. reflexivity. Qed.

(** j = S j': one copy of the unit sits in the PREFIX, so the head always has
    a concrete cell to step onto. *)
Definition P0_0RB0RA_1RC0RC_1LD1RB_0LD0LA : sconf := mkC StA (mkS [S0;S1;S0] [S0;S1;S0] 1 0 [S0;S0;S0]) S0 (mkS [] [] 0 0 []).
Definition P1_0RB0RA_1RC0RC_1LD1RB_0LD0LA : sconf := mkC StA (mkS [S0;S0;S0] [S0;S0;S0] 1 0 [S0;S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chp_0RB0RA_1RC0RC_1LD1RB_0LD0LA : list lstep := [SWin 3; SCycL 7 1; SWin 9; SCycR 3; SWin 2; SRotL 1].

Lemma run_p_0RB0RA_1RC0RC_1LD1RB_0LD0LA : srun tm false true chp_0RB0RA_1RC0RC_1LD1RB_0LD0LA P0_0RB0RA_1RC0RC_1LD1RB_0LD0LA = Some (P1_0RB0RA_1RC0RC_1LD1RB_0LD0LA, 10, 14).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB0RA_1RC0RC_1LD1RB_0LD0LA : sconf := mkC StA (mkS [] [S0;S1;S0] 1 0 [S0;S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_0RB0RA_1RC0RC_1LD1RB_0LD0LA : sconf := mkC StA (mkS [] [S0;S0;S0] 1 1 [S0;S1]) S0 (mkS [] [] 0 0 []).
Definition cho_0RB0RA_1RC0RC_1LD1RB_0LD0LA : list lstep := [SRotL 1; SWin 1; SRotL 1; SWin 1; SCycL 7 0; SWin 1; SWinL 9; SCycR 3; SWin 2; SRotL 1; SFoldL 1].

Lemma run_ovf_0RB0RA_1RC0RC_1LD1RB_0LD0LA : srun tm true true cho_0RB0RA_1RC0RC_1LD1RB_0LD0LA B0_0RB0RA_1RC0RC_1LD1RB_0LD0LA = Some (B1_0RB0RA_1RC0RC_1LD1RB_0LD0LA, 10, 14).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gz_0RB0RA_1RC0RC_1LD1RB_0LD0LA : forall p q0, cview p = (0, Some q0) ->
  Cc p = cden (Ap_Alph_000_010_01 q0 ++ [S0]) [] 0 Z0_0RB0RA_1RC0RC_1LD1RB_0LD0LA /\
  cden (Ap_Alph_000_010_01 q0 ++ [S0]) [] 0 Z1_0RB0RA_1RC0RC_1LD1RB_0LD0LA = Cc (Pos.succ p).
Proof.
  intros p q0 E. destruct (Alph_000_010_01.cview_some_Alph_000_010_01 p 0 q0 E) as (H1 & H2).
  unfold Cc_0RB0RA_1RC0RC_1LD1RB_0LD0LA, cden, Z0_0RB0RA_1RC0RC_1LD1RB_0LD0LA, Z1_0RB0RA_1RC0RC_1LD1RB_0LD0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gp_0RB0RA_1RC0RC_1LD1RB_0LD0LA : forall p j q0, cview p = (S j, Some q0) ->
  Cc p = cden (Ap_Alph_000_010_01 q0 ++ [S0]) [] j P0_0RB0RA_1RC0RC_1LD1RB_0LD0LA /\
  cden (Ap_Alph_000_010_01 q0 ++ [S0]) [] j P1_0RB0RA_1RC0RC_1LD1RB_0LD0LA = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (Alph_000_010_01.cview_some_Alph_000_010_01 p (S j) q0 E) as (H1 & H2).
  unfold Cc_0RB0RA_1RC0RC_1LD1RB_0LD0LA, cden, P0_0RB0RA_1RC0RC_1LD1RB_0LD0LA, P1_0RB0RA_1RC0RC_1LD1RB_0LD0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_0RB0RA_1RC0RC_1LD1RB_0LD0LA : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct j as [|j'].
  - destruct (gz_0RB0RA_1RC0RC_1LD1RB_0LD0LA p q0 E) as (HA & HB).
    exists (0 * 0 + 4). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chz_0RB0RA_1RC0RC_1LD1RB_0LD0LA Z0_0RB0RA_1RC0RC_1LD1RB_0LD0LA Z1_0RB0RA_1RC0RC_1LD1RB_0LD0LA 0 4
               run_z_0RB0RA_1RC0RC_1LD1RB_0LD0LA (Ap_Alph_000_010_01 q0 ++ [S0]) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gp_0RB0RA_1RC0RC_1LD1RB_0LD0LA p j' q0 E) as (HA & HB).
    exists (10 * j' + 14). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chp_0RB0RA_1RC0RC_1LD1RB_0LD0LA P0_0RB0RA_1RC0RC_1LD1RB_0LD0LA P1_0RB0RA_1RC0RC_1LD1RB_0LD0LA 10 14
               run_p_0RB0RA_1RC0RC_1LD1RB_0LD0LA (Ap_Alph_000_010_01 q0 ++ [S0]) [] j'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
Qed.

Lemma gso_0RB0RA_1RC0RC_1LD1RB_0LD0LA : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_0RB0RA_1RC0RC_1LD1RB_0LD0LA.
Proof.
  intros p j E. destruct (Alph_000_010_01.cview_none_Alph_000_010_01 p j E) as (H1 & _).
  unfold Cc_0RB0RA_1RC0RC_1LD1RB_0LD0LA, cden, B0_0RB0RA_1RC0RC_1LD1RB_0LD0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_0RB0RA_1RC0RC_1LD1RB_0LD0LA : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_0RB0RA_1RC0RC_1LD1RB_0LD0LA : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB0RA_1RC0RC_1LD1RB_0LD0LA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (Alph_000_010_01.cview_none_Alph_000_010_01 p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_0RB0RA_1RC0RC_1LD1RB_0LD0LA
             = (StA, (rep [S0;S0;S0] (S j) ++ [S0;S1], S0, []))).
  { unfold cden, B1_0RB0RA_1RC0RC_1LD1RB_0LD0LA, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. reflexivity. }
  assert (HC : Cc (Pos.succ p) = (StA, ((rep [S0;S0;S0] (S j) ++ [S0;S1]) ++ [S0], S0, []))).
  { unfold Cc_0RB0RA_1RC0RC_1LD1RB_0LD0LA. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_0RB0RA_1RC0RC_1LD1RB_0LD0LA. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_0RB0RA_1RC0RC_1LD1RB_0LD0LA : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB0RA_1RC0RC_1LD1RB_0LD0LA p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_0RB0RA_1RC0RC_1LD1RB_0LD0LA B0_0RB0RA_1RC0RC_1LD1RB_0LD0LA B1_0RB0RA_1RC0RC_1LD1RB_0LD0LA 10 14 p j' [] []).
    + exact run_ovf_0RB0RA_1RC0RC_1LD1RB_0LD0LA.
    + reflexivity.
    + reflexivity.
    + exact (gso_0RB0RA_1RC0RC_1LD1RB_0LD0LA p j' E).
    + exact (geo_0RB0RA_1RC0RC_1LD1RB_0LD0LA p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_0RB0RA_1RC0RC_1LD1RB_0LD0LA : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
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

Lemma viso_0RB0RA_1RC0RC_1LD1RB_0LD0LA : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_0RB0RA_1RC0RC_1LD1RB_0LD0LA = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_0RB0RA_1RC0RC_1LD1RB_0LD0LA p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB0RA_1RC0RC_1LD1RB_0LD0LA p j E)].
Qed.

Lemma vis_0RB0RA_1RC0RC_1LD1RB_0LD0LA : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_0RB0RA_1RC0RC_1LD1RB_0LD0LA.
  destruct q.

  - (* StA: the anchor state *)
    exists 0. eexists. split; reflexivity.
  - (* StB *)
    apply (vis_via_ovf tm Cc Hi StB), viso_0RB0RA_1RC0RC_1LD1RB_0LD0LA
      with (l := [SRotL 1; SWin 1]).
    vm_compute; reflexivity.
  - (* StC *)
    apply (vis_via_ovf tm Cc Hi StC), viso_0RB0RA_1RC0RC_1LD1RB_0LD0LA
      with (l := [SRotL 1; SWin 1; SRotL 1; SWin 1]).
    vm_compute; reflexivity.
  - (* StD *)
    apply (vis_via_ovf tm Cc Hi StD), viso_0RB0RA_1RC0RC_1LD1RB_0LD0LA
      with (l := [SRotL 1; SWin 1; SRotL 1; SWin 1; SCycL 7 0; SWin 1; SWinL 2]).
    vm_compute; reflexivity.
Qed.

Theorem nqhm_0RB0RA_1RC0RC_1LD1RB_0LD0LA : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 1). - exact boot_0RB0RA_1RC0RC_1LD1RB_0LD0LA. - intros p _. apply lap_0RB0RA_1RC0RC_1LD1RB_0LD0LA. - intros p q _. apply vis_0RB0RA_1RC0RC_1LD1RB_0LD0LA. Qed.

Theorem nqh_0RB0RA_1RC0RC_1LD1RB_0LD0LA : NeverQuasiHaltsSt tm_0RB0RA_1RC0RC_1LD1RB_0LD0LA.
Proof. apply (mirror_never_qh tm_0RB0RA_1RC0RC_1LD1RB_0LD0LA). rewrite mirror_ok_0RB0RA_1RC0RC_1LD1RB_0LD0LA. exact nqhm_0RB0RA_1RC0RC_1LD1RB_0LD0LA. Qed.

Theorem nonhalt_0RB0RA_1RC0RC_1LD1RB_0LD0LA : NonHalt tm_0RB0RA_1RC0RC_1LD1RB_0LD0LA.
Proof. apply never_qh_nonhalt, nqh_0RB0RA_1RC0RC_1LD1RB_0LD0LA. Qed.
