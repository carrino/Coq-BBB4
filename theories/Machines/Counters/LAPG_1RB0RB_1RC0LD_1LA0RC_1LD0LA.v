(** * LAPG_1RB0RB_1RC0LD_1LA0RC_1LD0LA: machine 1RB0RB_1RC0LD_1LA0RC_1LD0LA, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_graycert.py (UNTRUSTED emitter; the
    Coq kernel re-runs the checker on every line below).  This is a GRAY-CODE
    counter: the tape word is the reflected-binary code of the count, not its
    binary expansion (WAVE13_FINDINGS.md section 9d), so it is anchored on
    [Counters/GpCounter.v] rather than on one of the five digit alphabets.

      Cc p = (StC, (Gp p ++ [], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound] -- unchanged, because
    [srun_sound] never sees the encoding, only the symbolic sides.

    FIVE branches.  The Gray increment flips ONE cell of the high part; the
    interior branch therefore splits on the value [x] of that cell, which
    makes the opaque tail [G] identical on both sides of the lap (the tail is
    universally quantified in [srun_sound], so it must be).

      interior j=0,   x=S0 : 6 steps      x=S1 : 6 steps
      interior j=S j', x=S0 : 2*j'+8           x=S1 : 2*j'+8
      overflow             : 2*j+8

    Differentially validated against the raw simulator on ALL FIVE branches --
    step counts AND exact configurations -- for 298 anchors.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH MonoCounter
                                  JpCounter GpCounter LapCertGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_1RB0RB_1RC0LD_1LA0RC_1LD0LA (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB0RB_1RC0LD_1LA0RC_1LD0LA.

(** 1RB0RB_1RC0LD_1LA0RC_1LD0LA *)
Definition tm_1RB0RB_1RC0LD_1LA0RC_1LD0LA : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DR StB
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S0 DL StD
  | StC, S0 => mk S1 DL StA | StC, S1 => mk S0 DR StC
  | StD, S0 => mk S1 DL StD | StD, S1 => mk S0 DL StA end.
Local Notation tm := tm_1RB0RB_1RC0LD_1LA0RC_1LD0LA.

Definition Cc_1RB0RB_1RC0LD_1LA0RC_1LD0LA (p : positive) : cconf := (StC, (Gp p ++ [], S0, [])).
Local Notation Cc := Cc_1RB0RB_1RC0LD_1LA0RC_1LD0LA.

(** ** The certificate *)

Definition Z0a_1RB0RB_1RC0LD_1LA0RC_1LD0LA : sconf := mkC StC (mkS [S0;S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition Z1a_1RB0RB_1RC0LD_1LA0RC_1LD0LA : sconf := mkC StC (mkS [S1;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition chza_1RB0RB_1RC0LD_1LA0RC_1LD0LA : list lstep := [SWin 6].
Lemma run_za_1RB0RB_1RC0LD_1LA0RC_1LD0LA : srun tm false true chza_1RB0RB_1RC0LD_1LA0RC_1LD0LA Z0a_1RB0RB_1RC0LD_1LA0RC_1LD0LA = Some (Z1a_1RB0RB_1RC0LD_1LA0RC_1LD0LA, 0, 6).
Proof. vm_compute. reflexivity. Qed.

Definition Z0b_1RB0RB_1RC0LD_1LA0RC_1LD0LA : sconf := mkC StC (mkS [S0;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition Z1b_1RB0RB_1RC0LD_1LA0RC_1LD0LA : sconf := mkC StC (mkS [S1;S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition chzb_1RB0RB_1RC0LD_1LA0RC_1LD0LA : list lstep := [SWin 6].
Lemma run_zb_1RB0RB_1RC0LD_1LA0RC_1LD0LA : srun tm false true chzb_1RB0RB_1RC0LD_1LA0RC_1LD0LA Z0b_1RB0RB_1RC0LD_1LA0RC_1LD0LA = Some (Z1b_1RB0RB_1RC0LD_1LA0RC_1LD0LA, 0, 6).
Proof. vm_compute. reflexivity. Qed.

Definition P0a_1RB0RB_1RC0LD_1LA0RC_1LD0LA : sconf := mkC StC (mkS [S1] [S0] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition P1a_1RB0RB_1RC0LD_1LA0RC_1LD0LA : sconf := mkC StC (mkS [S0] [S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chpa_1RB0RB_1RC0LD_1LA0RC_1LD0LA : list lstep := [SWin 3; SCycL 1 0; SWin 4; SCycR 1; SWin 1].
Lemma run_pa_1RB0RB_1RC0LD_1LA0RC_1LD0LA : srun tm false true chpa_1RB0RB_1RC0LD_1LA0RC_1LD0LA P0a_1RB0RB_1RC0LD_1LA0RC_1LD0LA = Some (P1a_1RB0RB_1RC0LD_1LA0RC_1LD0LA, 2, 8).
Proof. vm_compute. reflexivity. Qed.

Definition P0b_1RB0RB_1RC0LD_1LA0RC_1LD0LA : sconf := mkC StC (mkS [S1] [S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition P1b_1RB0RB_1RC0LD_1LA0RC_1LD0LA : sconf := mkC StC (mkS [S0] [S0] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chpb_1RB0RB_1RC0LD_1LA0RC_1LD0LA : list lstep := [SWin 3; SCycL 1 0; SWin 4; SCycR 1; SWin 1].
Lemma run_pb_1RB0RB_1RC0LD_1LA0RC_1LD0LA : srun tm false true chpb_1RB0RB_1RC0LD_1LA0RC_1LD0LA P0b_1RB0RB_1RC0LD_1LA0RC_1LD0LA = Some (P1b_1RB0RB_1RC0LD_1LA0RC_1LD0LA, 2, 8).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB0RB_1RC0LD_1LA0RC_1LD0LA : sconf := mkC StC (mkS [S1] [S0] 1 0 [S1]) S0 (mkS [] [] 0 0 []).
Definition B1_1RB0RB_1RC0LD_1LA0RC_1LD0LA : sconf := mkC StC (mkS [S0] [S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition cho_1RB0RB_1RC0LD_1LA0RC_1LD0LA : list lstep := [SWin 3; SCycL 1 0; SWin 1; SWinL 3; SCycR 1; SWin 1].
Lemma run_ovf_1RB0RB_1RC0LD_1LA0RC_1LD0LA : srun tm true true cho_1RB0RB_1RC0LD_1LA0RC_1LD0LA B0_1RB0RB_1RC0LD_1LA0RC_1LD0LA = Some (B1_1RB0RB_1RC0LD_1LA0RC_1LD0LA, 2, 8).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics

    Each is one [GpCounter] rewrite plus [app_assoc].  The [x] argument is
    the flipped high cell, made concrete by the split. *)

Lemma gza_1RB0RB_1RC0LD_1LA0RC_1LD0LA : forall p q0 G, cview p = (0, Some q0) -> Gp q0 = S0 :: G ->
  Cc p = cden (G ++ []) [] 0 Z0a_1RB0RB_1RC0LD_1LA0RC_1LD0LA /\
  cden (G ++ []) [] 0 Z1a_1RB0RB_1RC0LD_1LA0RC_1LD0LA = Cc (Pos.succ p).
Proof.
  intros p q0 G E HG. destruct (cview_some0_G p q0 S0 G E HG) as (H1 & H2).
  unfold Cc_1RB0RB_1RC0LD_1LA0RC_1LD0LA, cden, Z0a_1RB0RB_1RC0LD_1LA0RC_1LD0LA, Z1a_1RB0RB_1RC0LD_1LA0RC_1LD0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split; [rewrite H1 | rewrite H2]; cbn [rep app negs];
    rewrite <- ?app_assoc; cbn [app]; reflexivity.
Qed.

Lemma gzb_1RB0RB_1RC0LD_1LA0RC_1LD0LA : forall p q0 G, cview p = (0, Some q0) -> Gp q0 = S1 :: G ->
  Cc p = cden (G ++ []) [] 0 Z0b_1RB0RB_1RC0LD_1LA0RC_1LD0LA /\
  cden (G ++ []) [] 0 Z1b_1RB0RB_1RC0LD_1LA0RC_1LD0LA = Cc (Pos.succ p).
Proof.
  intros p q0 G E HG. destruct (cview_some0_G p q0 S1 G E HG) as (H1 & H2).
  unfold Cc_1RB0RB_1RC0LD_1LA0RC_1LD0LA, cden, Z0b_1RB0RB_1RC0LD_1LA0RC_1LD0LA, Z1b_1RB0RB_1RC0LD_1LA0RC_1LD0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split; [rewrite H1 | rewrite H2]; cbn [rep app negs];
    rewrite <- ?app_assoc; cbn [app]; reflexivity.
Qed.

Lemma gpa_1RB0RB_1RC0LD_1LA0RC_1LD0LA : forall p j q0 G, cview p = (S j, Some q0) -> Gp q0 = S0 :: G ->
  Cc p = cden (G ++ []) [] j P0a_1RB0RB_1RC0LD_1LA0RC_1LD0LA /\
  cden (G ++ []) [] j P1a_1RB0RB_1RC0LD_1LA0RC_1LD0LA = Cc (Pos.succ p).
Proof.
  intros p j q0 G E HG. destruct (cview_some_G p j q0 S0 G E HG) as (H1 & H2).
  unfold Cc_1RB0RB_1RC0LD_1LA0RC_1LD0LA, cden, P0a_1RB0RB_1RC0LD_1LA0RC_1LD0LA, P1a_1RB0RB_1RC0LD_1LA0RC_1LD0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split; [rewrite H1 | rewrite H2]; cbn [rep app negs];
    rewrite <- ?app_assoc; cbn [app]; reflexivity.
Qed.

Lemma gpb_1RB0RB_1RC0LD_1LA0RC_1LD0LA : forall p j q0 G, cview p = (S j, Some q0) -> Gp q0 = S1 :: G ->
  Cc p = cden (G ++ []) [] j P0b_1RB0RB_1RC0LD_1LA0RC_1LD0LA /\
  cden (G ++ []) [] j P1b_1RB0RB_1RC0LD_1LA0RC_1LD0LA = Cc (Pos.succ p).
Proof.
  intros p j q0 G E HG. destruct (cview_some_G p j q0 S1 G E HG) as (H1 & H2).
  unfold Cc_1RB0RB_1RC0LD_1LA0RC_1LD0LA, cden, P0b_1RB0RB_1RC0LD_1LA0RC_1LD0LA, P1b_1RB0RB_1RC0LD_1LA0RC_1LD0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split; [rewrite H1 | rewrite H2]; cbn [rep app negs];
    rewrite <- ?app_assoc; cbn [app]; reflexivity.
Qed.

(** ** The interior lap *)

Lemma lapi_1RB0RB_1RC0LD_1LA0RC_1LD0LA : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (Gp_shape q0) as (x & G & HG).
  destruct j as [|j']; destruct x.
  - destruct (gza_1RB0RB_1RC0LD_1LA0RC_1LD0LA p q0 G E HG) as (HA & HB).
    exists (0 * 0 + 6). split; [lia|]. rewrite HA.
    rewrite (srun_sound tm false true chza_1RB0RB_1RC0LD_1LA0RC_1LD0LA Z0a_1RB0RB_1RC0LD_1LA0RC_1LD0LA Z1a_1RB0RB_1RC0LD_1LA0RC_1LD0LA 0 6
               run_za_1RB0RB_1RC0LD_1LA0RC_1LD0LA (G ++ []) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gzb_1RB0RB_1RC0LD_1LA0RC_1LD0LA p q0 G E HG) as (HA & HB).
    exists (0 * 0 + 6). split; [lia|]. rewrite HA.
    rewrite (srun_sound tm false true chzb_1RB0RB_1RC0LD_1LA0RC_1LD0LA Z0b_1RB0RB_1RC0LD_1LA0RC_1LD0LA Z1b_1RB0RB_1RC0LD_1LA0RC_1LD0LA 0 6
               run_zb_1RB0RB_1RC0LD_1LA0RC_1LD0LA (G ++ []) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gpa_1RB0RB_1RC0LD_1LA0RC_1LD0LA p j' q0 G E HG) as (HA & HB).
    exists (2 * j' + 8). split; [lia|]. rewrite HA.
    rewrite (srun_sound tm false true chpa_1RB0RB_1RC0LD_1LA0RC_1LD0LA P0a_1RB0RB_1RC0LD_1LA0RC_1LD0LA P1a_1RB0RB_1RC0LD_1LA0RC_1LD0LA 2 8
               run_pa_1RB0RB_1RC0LD_1LA0RC_1LD0LA (G ++ []) [] j'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gpb_1RB0RB_1RC0LD_1LA0RC_1LD0LA p j' q0 G E HG) as (HA & HB).
    exists (2 * j' + 8). split; [lia|]. rewrite HA.
    rewrite (srun_sound tm false true chpb_1RB0RB_1RC0LD_1LA0RC_1LD0LA P0b_1RB0RB_1RC0LD_1LA0RC_1LD0LA P1b_1RB0RB_1RC0LD_1LA0RC_1LD0LA 2 8
               run_pb_1RB0RB_1RC0LD_1LA0RC_1LD0LA (G ++ []) [] j'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
Qed.

(** ** The overflow lap *)

Lemma gso_1RB0RB_1RC0LD_1LA0RC_1LD0LA : forall p j, cview p = (S j, None) -> Cc p = cden [] [] j B0_1RB0RB_1RC0LD_1LA0RC_1LD0LA.
Proof.
  intros p j E. destruct (cview_none_G p j E) as (H1 & _).
  unfold Cc_1RB0RB_1RC0LD_1LA0RC_1LD0LA, cden, B0_1RB0RB_1RC0LD_1LA0RC_1LD0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1; cbn [rep app]; rewrite <- ?app_assoc; cbn [app]; reflexivity.
Qed.

Lemma lbl_1RB0RB_1RC0LD_1LA0RC_1LD0LA : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB0RB_1RC0LD_1LA0RC_1LD0LA : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB0RB_1RC0LD_1LA0RC_1LD0LA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (cview_none_G p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB0RB_1RC0LD_1LA0RC_1LD0LA
             = (StC, (S0 :: rep [S0] j ++ [S1;S1], S0, []))).
  { unfold cden, B1_1RB0RB_1RC0LD_1LA0RC_1LD0LA, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. reflexivity. }
  assert (HC : Cc (Pos.succ p) = (StC, (S0 :: rep [S0] j ++ [S1;S1], S0, []))).
  { unfold Cc_1RB0RB_1RC0LD_1LA0RC_1LD0LA. rewrite H2. cbn [app]; rewrite <- ?app_assoc;
    cbn [app]; rewrite ?app_nil_r; reflexivity. }
  rewrite HD, HC. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_1RB0RB_1RC0LD_1LA0RC_1LD0LA : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB0RB_1RC0LD_1LA0RC_1LD0LA p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_1RB0RB_1RC0LD_1LA0RC_1LD0LA B0_1RB0RB_1RC0LD_1LA0RC_1LD0LA B1_1RB0RB_1RC0LD_1LA0RC_1LD0LA 2 8 p j' [] []).
    + exact run_ovf_1RB0RB_1RC0LD_1LA0RC_1LD0LA.
    + reflexivity.
    + reflexivity.
    + exact (gso_1RB0RB_1RC0LD_1LA0RC_1LD0LA p j' E).
    + exact (geo_1RB0RB_1RC0LD_1LA0RC_1LD0LA p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_1RB0RB_1RC0LD_1LA0RC_1LD0LA : exists t0, stepn tm t0 InitES = Some (lift (Cc 2)).
Proof.
  exists 10.
  assert (H : match csteps tm 10 c0 with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 10 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits *)

Lemma viso_1RB0RB_1RC0LD_1LA0RC_1LD0LA : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_1RB0RB_1RC0LD_1LA0RC_1LD0LA = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_1RB0RB_1RC0LD_1LA0RC_1LD0LA p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB0RB_1RC0LD_1LA0RC_1LD0LA p j E)].
Qed.

Lemma vis_1RB0RB_1RC0LD_1LA0RC_1LD0LA : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_1RB0RB_1RC0LD_1LA0RC_1LD0LA.
  destruct q.

  - (* StA *)
    apply (vis_via_ovf tm Cc Hi StA), viso_1RB0RB_1RC0LD_1LA0RC_1LD0LA
      with (l := [SWin 1]).
    vm_compute; reflexivity.
  - (* StB *)
    apply (vis_via_ovf tm Cc Hi StB), viso_1RB0RB_1RC0LD_1LA0RC_1LD0LA
      with (l := [SWin 2]).
    vm_compute; reflexivity.
  - (* StC: the anchor state *)
    exists 0. eexists. split; reflexivity.
  - (* StD *)
    apply (vis_via_ovf tm Cc Hi StD), viso_1RB0RB_1RC0LD_1LA0RC_1LD0LA
      with (l := [SWin 3]).
    vm_compute; reflexivity.
Qed.

Theorem nqh_1RB0RB_1RC0LD_1LA0RC_1LD0LA : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 2). - exact boot_1RB0RB_1RC0LD_1LA0RC_1LD0LA. - intros p _. apply lap_1RB0RB_1RC0LD_1LA0RC_1LD0LA. - intros p q _. apply vis_1RB0RB_1RC0LD_1LA0RC_1LD0LA. Qed.

Theorem nonhalt_1RB0RB_1RC0LD_1LA0RC_1LD0LA : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_1RB0RB_1RC0LD_1LA0RC_1LD0LA. Qed.
