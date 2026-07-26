(** * LAPG_0RB0LA_1RC0RC_1LD0LD_1RB1LA: machine 0RB0LA_1RC0RC_1LD0LD_1RB1LA, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_graycert.py (UNTRUSTED emitter; the
    Coq kernel re-runs the checker on every line below).  This is a GRAY-CODE
    counter: the tape word is the reflected-binary code of the count, not its
    binary expansion (WAVE13_FINDINGS.md section 9d), so it is anchored on
    [Counters/GpCounter.v] rather than on one of the five digit alphabets.

      Cc p = (StA, (Gp p ++ [], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound] -- unchanged, because
    [srun_sound] never sees the encoding, only the symbolic sides.

    FIVE branches.  The Gray increment flips ONE cell of the high part; the
    interior branch therefore splits on the value [x] of that cell, which
    makes the opaque tail [G] identical on both sides of the lap (the tail is
    universally quantified in [srun_sound], so it must be).

      interior j=0,   x=S0 : 4 steps      x=S1 : 4 steps
      interior j=S j', x=S0 : 4*j'+8           x=S1 : 4*j'+8
      overflow             : 4*j+8

    Differentially validated against the raw simulator on ALL FIVE branches --
    step counts AND exact configurations -- for 298 anchors.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH MonoCounter
                                  JpCounter GpCounter LapCertGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_0RB0LA_1RC0RC_1LD0LD_1RB1LA (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB0LA_1RC0RC_1LD0LD_1RB1LA.

(** 0RB0LA_1RC0RC_1LD0LD_1RB1LA *)
(** 0RB0LA_1RC0RC_1LD0LD_1RB1LA -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB0LA_1RC0RC_1LD0LD_1RB1LA : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S0 DL StA
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S0 DR StC
  | StC, S0 => mk S1 DL StD | StC, S1 => mk S0 DL StD
  | StD, S0 => mk S1 DR StB | StD, S1 => mk S1 DL StA end.

(** Its mirror 0LB0RA_1LC0LC_1RD0RD_1LB1RA: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB0LA_1RC0RC_1LD0LD_1RB1LA : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S0 DR StA
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DL StC
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S0 DR StD
  | StD, S0 => mk S1 DL StB | StD, S1 => mk S1 DR StA end.
Local Notation tm := tmm_0RB0LA_1RC0RC_1LD0LD_1RB1LA.

Lemma mirror_ok_0RB0LA_1RC0RC_1LD0LD_1RB1LA : mirror_tm tm_0RB0LA_1RC0RC_1LD0LD_1RB1LA = tmm_0RB0LA_1RC0RC_1LD0LD_1RB1LA.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_0RB0LA_1RC0RC_1LD0LD_1RB1LA (p : positive) : cconf := (StA, (Gp p ++ [], S0, [])).
Local Notation Cc := Cc_0RB0LA_1RC0RC_1LD0LD_1RB1LA.

(** ** The certificate *)

Definition Z0a_0RB0LA_1RC0RC_1LD0LD_1RB1LA : sconf := mkC StA (mkS [S0;S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition Z1a_0RB0LA_1RC0RC_1LD0LD_1RB1LA : sconf := mkC StA (mkS [S1;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition chza_0RB0LA_1RC0RC_1LD0LD_1RB1LA : list lstep := [SWin 4].
Lemma run_za_0RB0LA_1RC0RC_1LD0LD_1RB1LA : srun tm false true chza_0RB0LA_1RC0RC_1LD0LD_1RB1LA Z0a_0RB0LA_1RC0RC_1LD0LD_1RB1LA = Some (Z1a_0RB0LA_1RC0RC_1LD0LD_1RB1LA, 0, 4).
Proof. vm_compute. reflexivity. Qed.

Definition Z0b_0RB0LA_1RC0RC_1LD0LD_1RB1LA : sconf := mkC StA (mkS [S0;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition Z1b_0RB0LA_1RC0RC_1LD0LD_1RB1LA : sconf := mkC StA (mkS [S1;S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition chzb_0RB0LA_1RC0RC_1LD0LD_1RB1LA : list lstep := [SWin 4].
Lemma run_zb_0RB0LA_1RC0RC_1LD0LD_1RB1LA : srun tm false true chzb_0RB0LA_1RC0RC_1LD0LD_1RB1LA Z0b_0RB0LA_1RC0RC_1LD0LD_1RB1LA = Some (Z1b_0RB0LA_1RC0RC_1LD0LD_1RB1LA, 0, 4).
Proof. vm_compute. reflexivity. Qed.

Definition P0a_0RB0LA_1RC0RC_1LD0LD_1RB1LA : sconf := mkC StA (mkS [S1] [S0] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition P1a_0RB0LA_1RC0RC_1LD0LD_1RB1LA : sconf := mkC StA (mkS [S0] [S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chpa_0RB0LA_1RC0RC_1LD0LD_1RB1LA : list lstep := [SWin 1; SCycL 3 0; SWin 6; SCycR 1; SWin 1].
Lemma run_pa_0RB0LA_1RC0RC_1LD0LD_1RB1LA : srun tm false true chpa_0RB0LA_1RC0RC_1LD0LD_1RB1LA P0a_0RB0LA_1RC0RC_1LD0LD_1RB1LA = Some (P1a_0RB0LA_1RC0RC_1LD0LD_1RB1LA, 4, 8).
Proof. vm_compute. reflexivity. Qed.

Definition P0b_0RB0LA_1RC0RC_1LD0LD_1RB1LA : sconf := mkC StA (mkS [S1] [S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition P1b_0RB0LA_1RC0RC_1LD0LD_1RB1LA : sconf := mkC StA (mkS [S0] [S0] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chpb_0RB0LA_1RC0RC_1LD0LD_1RB1LA : list lstep := [SWin 1; SCycL 3 0; SWin 6; SCycR 1; SWin 1].
Lemma run_pb_0RB0LA_1RC0RC_1LD0LD_1RB1LA : srun tm false true chpb_0RB0LA_1RC0RC_1LD0LD_1RB1LA P0b_0RB0LA_1RC0RC_1LD0LD_1RB1LA = Some (P1b_0RB0LA_1RC0RC_1LD0LD_1RB1LA, 4, 8).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB0LA_1RC0RC_1LD0LD_1RB1LA : sconf := mkC StA (mkS [S1] [S0] 1 0 [S1]) S0 (mkS [] [] 0 0 []).
Definition B1_0RB0LA_1RC0RC_1LD0LD_1RB1LA : sconf := mkC StA (mkS [S0] [S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition cho_0RB0LA_1RC0RC_1LD0LD_1RB1LA : list lstep := [SWin 1; SCycL 3 0; SWin 3; SWinL 3; SCycR 1; SWin 1].
Lemma run_ovf_0RB0LA_1RC0RC_1LD0LD_1RB1LA : srun tm true true cho_0RB0LA_1RC0RC_1LD0LD_1RB1LA B0_0RB0LA_1RC0RC_1LD0LD_1RB1LA = Some (B1_0RB0LA_1RC0RC_1LD0LD_1RB1LA, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics

    Each is one [GpCounter] rewrite plus [app_assoc].  The [x] argument is
    the flipped high cell, made concrete by the split. *)

Lemma gza_0RB0LA_1RC0RC_1LD0LD_1RB1LA : forall p q0 G, cview p = (0, Some q0) -> Gp q0 = S0 :: G ->
  Cc p = cden (G ++ []) [] 0 Z0a_0RB0LA_1RC0RC_1LD0LD_1RB1LA /\
  cden (G ++ []) [] 0 Z1a_0RB0LA_1RC0RC_1LD0LD_1RB1LA = Cc (Pos.succ p).
Proof.
  intros p q0 G E HG. destruct (cview_some0_G p q0 S0 G E HG) as (H1 & H2).
  unfold Cc_0RB0LA_1RC0RC_1LD0LD_1RB1LA, cden, Z0a_0RB0LA_1RC0RC_1LD0LD_1RB1LA, Z1a_0RB0LA_1RC0RC_1LD0LD_1RB1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split; [rewrite H1 | rewrite H2]; cbn [rep app negs];
    rewrite <- ?app_assoc; cbn [app]; reflexivity.
Qed.

Lemma gzb_0RB0LA_1RC0RC_1LD0LD_1RB1LA : forall p q0 G, cview p = (0, Some q0) -> Gp q0 = S1 :: G ->
  Cc p = cden (G ++ []) [] 0 Z0b_0RB0LA_1RC0RC_1LD0LD_1RB1LA /\
  cden (G ++ []) [] 0 Z1b_0RB0LA_1RC0RC_1LD0LD_1RB1LA = Cc (Pos.succ p).
Proof.
  intros p q0 G E HG. destruct (cview_some0_G p q0 S1 G E HG) as (H1 & H2).
  unfold Cc_0RB0LA_1RC0RC_1LD0LD_1RB1LA, cden, Z0b_0RB0LA_1RC0RC_1LD0LD_1RB1LA, Z1b_0RB0LA_1RC0RC_1LD0LD_1RB1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split; [rewrite H1 | rewrite H2]; cbn [rep app negs];
    rewrite <- ?app_assoc; cbn [app]; reflexivity.
Qed.

Lemma gpa_0RB0LA_1RC0RC_1LD0LD_1RB1LA : forall p j q0 G, cview p = (S j, Some q0) -> Gp q0 = S0 :: G ->
  Cc p = cden (G ++ []) [] j P0a_0RB0LA_1RC0RC_1LD0LD_1RB1LA /\
  cden (G ++ []) [] j P1a_0RB0LA_1RC0RC_1LD0LD_1RB1LA = Cc (Pos.succ p).
Proof.
  intros p j q0 G E HG. destruct (cview_some_G p j q0 S0 G E HG) as (H1 & H2).
  unfold Cc_0RB0LA_1RC0RC_1LD0LD_1RB1LA, cden, P0a_0RB0LA_1RC0RC_1LD0LD_1RB1LA, P1a_0RB0LA_1RC0RC_1LD0LD_1RB1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split; [rewrite H1 | rewrite H2]; cbn [rep app negs];
    rewrite <- ?app_assoc; cbn [app]; reflexivity.
Qed.

Lemma gpb_0RB0LA_1RC0RC_1LD0LD_1RB1LA : forall p j q0 G, cview p = (S j, Some q0) -> Gp q0 = S1 :: G ->
  Cc p = cden (G ++ []) [] j P0b_0RB0LA_1RC0RC_1LD0LD_1RB1LA /\
  cden (G ++ []) [] j P1b_0RB0LA_1RC0RC_1LD0LD_1RB1LA = Cc (Pos.succ p).
Proof.
  intros p j q0 G E HG. destruct (cview_some_G p j q0 S1 G E HG) as (H1 & H2).
  unfold Cc_0RB0LA_1RC0RC_1LD0LD_1RB1LA, cden, P0b_0RB0LA_1RC0RC_1LD0LD_1RB1LA, P1b_0RB0LA_1RC0RC_1LD0LD_1RB1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split; [rewrite H1 | rewrite H2]; cbn [rep app negs];
    rewrite <- ?app_assoc; cbn [app]; reflexivity.
Qed.

(** ** The interior lap *)

Lemma lapi_0RB0LA_1RC0RC_1LD0LD_1RB1LA : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (Gp_shape q0) as (x & G & HG).
  destruct j as [|j']; destruct x.
  - destruct (gza_0RB0LA_1RC0RC_1LD0LD_1RB1LA p q0 G E HG) as (HA & HB).
    exists (0 * 0 + 4). split; [lia|]. rewrite HA.
    rewrite (srun_sound tm false true chza_0RB0LA_1RC0RC_1LD0LD_1RB1LA Z0a_0RB0LA_1RC0RC_1LD0LD_1RB1LA Z1a_0RB0LA_1RC0RC_1LD0LD_1RB1LA 0 4
               run_za_0RB0LA_1RC0RC_1LD0LD_1RB1LA (G ++ []) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gzb_0RB0LA_1RC0RC_1LD0LD_1RB1LA p q0 G E HG) as (HA & HB).
    exists (0 * 0 + 4). split; [lia|]. rewrite HA.
    rewrite (srun_sound tm false true chzb_0RB0LA_1RC0RC_1LD0LD_1RB1LA Z0b_0RB0LA_1RC0RC_1LD0LD_1RB1LA Z1b_0RB0LA_1RC0RC_1LD0LD_1RB1LA 0 4
               run_zb_0RB0LA_1RC0RC_1LD0LD_1RB1LA (G ++ []) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gpa_0RB0LA_1RC0RC_1LD0LD_1RB1LA p j' q0 G E HG) as (HA & HB).
    exists (4 * j' + 8). split; [lia|]. rewrite HA.
    rewrite (srun_sound tm false true chpa_0RB0LA_1RC0RC_1LD0LD_1RB1LA P0a_0RB0LA_1RC0RC_1LD0LD_1RB1LA P1a_0RB0LA_1RC0RC_1LD0LD_1RB1LA 4 8
               run_pa_0RB0LA_1RC0RC_1LD0LD_1RB1LA (G ++ []) [] j'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gpb_0RB0LA_1RC0RC_1LD0LD_1RB1LA p j' q0 G E HG) as (HA & HB).
    exists (4 * j' + 8). split; [lia|]. rewrite HA.
    rewrite (srun_sound tm false true chpb_0RB0LA_1RC0RC_1LD0LD_1RB1LA P0b_0RB0LA_1RC0RC_1LD0LD_1RB1LA P1b_0RB0LA_1RC0RC_1LD0LD_1RB1LA 4 8
               run_pb_0RB0LA_1RC0RC_1LD0LD_1RB1LA (G ++ []) [] j'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
Qed.

(** ** The overflow lap *)

Lemma gso_0RB0LA_1RC0RC_1LD0LD_1RB1LA : forall p j, cview p = (S j, None) -> Cc p = cden [] [] j B0_0RB0LA_1RC0RC_1LD0LD_1RB1LA.
Proof.
  intros p j E. destruct (cview_none_G p j E) as (H1 & _).
  unfold Cc_0RB0LA_1RC0RC_1LD0LD_1RB1LA, cden, B0_0RB0LA_1RC0RC_1LD0LD_1RB1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1; cbn [rep app]; rewrite <- ?app_assoc; cbn [app]; reflexivity.
Qed.

Lemma lbl_0RB0LA_1RC0RC_1LD0LD_1RB1LA : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_0RB0LA_1RC0RC_1LD0LD_1RB1LA : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB0LA_1RC0RC_1LD0LD_1RB1LA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (cview_none_G p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_0RB0LA_1RC0RC_1LD0LD_1RB1LA
             = (StA, (S0 :: rep [S0] j ++ [S1;S1], S0, []))).
  { unfold cden, B1_0RB0LA_1RC0RC_1LD0LD_1RB1LA, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. reflexivity. }
  assert (HC : Cc (Pos.succ p) = (StA, (S0 :: rep [S0] j ++ [S1;S1], S0, []))).
  { unfold Cc_0RB0LA_1RC0RC_1LD0LD_1RB1LA. rewrite H2. cbn [app]; rewrite <- ?app_assoc;
    cbn [app]; rewrite ?app_nil_r; reflexivity. }
  rewrite HD, HC. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_0RB0LA_1RC0RC_1LD0LD_1RB1LA : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB0LA_1RC0RC_1LD0LD_1RB1LA p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_0RB0LA_1RC0RC_1LD0LD_1RB1LA B0_0RB0LA_1RC0RC_1LD0LD_1RB1LA B1_0RB0LA_1RC0RC_1LD0LD_1RB1LA 4 8 p j' [] []).
    + exact run_ovf_0RB0LA_1RC0RC_1LD0LD_1RB1LA.
    + reflexivity.
    + reflexivity.
    + exact (gso_0RB0LA_1RC0RC_1LD0LD_1RB1LA p j' E).
    + exact (geo_0RB0LA_1RC0RC_1LD0LD_1RB1LA p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_0RB0LA_1RC0RC_1LD0LD_1RB1LA : exists t0, stepn tm t0 InitES = Some (lift (Cc 2)).
Proof.
  exists 12.
  assert (H : match csteps tm 12 c0 with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 12 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits *)

Lemma viso_0RB0LA_1RC0RC_1LD0LD_1RB1LA : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_0RB0LA_1RC0RC_1LD0LD_1RB1LA = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_0RB0LA_1RC0RC_1LD0LD_1RB1LA p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB0LA_1RC0RC_1LD0LD_1RB1LA p j E)].
Qed.

Lemma vis_0RB0LA_1RC0RC_1LD0LD_1RB1LA : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_0RB0LA_1RC0RC_1LD0LD_1RB1LA.
  destruct q.

  - (* StA: the anchor state *)
    exists 0. eexists. split; reflexivity.
  - (* StB *)
    apply (vis_via_ovf tm Cc Hi StB), viso_0RB0LA_1RC0RC_1LD0LD_1RB1LA
      with (l := [SWin 1]).
    vm_compute; reflexivity.
  - (* StC *)
    apply (vis_via_ovf tm Cc Hi StC), viso_0RB0LA_1RC0RC_1LD0LD_1RB1LA
      with (l := [SWin 1; SCycL 3 0; SWin 1]).
    vm_compute; reflexivity.
  - (* StD *)
    apply (vis_via_ovf tm Cc Hi StD), viso_0RB0LA_1RC0RC_1LD0LD_1RB1LA
      with (l := [SWin 1; SCycL 3 0; SWin 2]).
    vm_compute; reflexivity.
Qed.

Theorem nqhm_0RB0LA_1RC0RC_1LD0LD_1RB1LA : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 2). - exact boot_0RB0LA_1RC0RC_1LD0LD_1RB1LA. - intros p _. apply lap_0RB0LA_1RC0RC_1LD0LD_1RB1LA. - intros p q _. apply vis_0RB0LA_1RC0RC_1LD0LD_1RB1LA. Qed.

Theorem nqh_0RB0LA_1RC0RC_1LD0LD_1RB1LA : NeverQuasiHaltsSt tm_0RB0LA_1RC0RC_1LD0LD_1RB1LA.
Proof. apply (mirror_never_qh tm_0RB0LA_1RC0RC_1LD0LD_1RB1LA). rewrite mirror_ok_0RB0LA_1RC0RC_1LD0LD_1RB1LA. exact nqhm_0RB0LA_1RC0RC_1LD0LD_1RB1LA. Qed.

Theorem nonhalt_0RB0LA_1RC0RC_1LD0LD_1RB1LA : NonHalt tm_0RB0LA_1RC0RC_1LD0LD_1RB1LA.
Proof. apply never_qh_nonhalt, nqh_0RB0LA_1RC0RC_1LD0LD_1RB1LA. Qed.
