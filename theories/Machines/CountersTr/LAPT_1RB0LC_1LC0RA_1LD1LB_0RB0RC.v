(** * LAPT_1RB0LC_1LC0RA_1LD1LB_0RB0RC: TRANSITION-LEVEL board for machine 1RB0LC_1LC0RA_1LD1LB_0RB0RC, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Jp digit alphabet (JpCounter.v), anchored at

      Cc p = (StD, (Jp p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  6*j+4 steps
      overflow  (cview p = (S j, None)):   boot 4*j+5, then the inner counter's own laps to the
                                           all-ones fill, then exit 6*j+16

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 192 interior anchors (interior); 6 overflow phases, j = 2..7 (246 inner laps) (nested overflow).
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter JpCounter LapCertGlue LapCertGlueLift IXPGadgets NestedLap NestedLapLift.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
From BBB4 Require Import BBBT4_Statement.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr.
Import ListNotations.

Definition mk_1RB0LC_1LC0RA_1LD1LB_0RB0RC (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB0LC_1LC0RA_1LD1LB_0RB0RC.

(** 1RB0LC_1LC0RA_1LD1LB_0RB0RC *)
(** 1RB0LC_1LC0RA_1LD1LB_0RB0RC -- the real machine (its counter grows RIGHT). *)
Definition tm_1RB0LC_1LC0RA_1LD1LB_0RB0RC : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StC
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DR StA
  | StC, S0 => mk S1 DL StD | StC, S1 => mk S1 DL StB
  | StD, S0 => mk S0 DR StB | StD, S1 => mk S0 DR StC end.

(** Its mirror 1LB0RC_1RC0LA_1RD1RB_0LB0LC: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_1RB0LC_1LC0RA_1LD1LB_0RB0RC : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => mk S0 DR StC
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S0 DL StA
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S1 DR StB
  | StD, S0 => mk S0 DL StB | StD, S1 => mk S0 DL StC end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_1RB0LC_1LC0RA_1LD1LB_0RB0RC : list Instr := [].
Definition tmw_1RB0LC_1LC0RA_1LD1LB_0RB0RC : TM := tm_wrap_trs tmm_1RB0LC_1LC0RA_1LD1LB_0RB0RC pins_1RB0LC_1LC0RA_1LD1LB_0RB0RC.
Local Notation tm := tmw_1RB0LC_1LC0RA_1LD1LB_0RB0RC.

Lemma mirror_ok_1RB0LC_1LC0RA_1LD1LB_0RB0RC : mirror_tm tm_1RB0LC_1LC0RA_1LD1LB_0RB0RC = tmm_1RB0LC_1LC0RA_1LD1LB_0RB0RC.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_1RB0LC_1LC0RA_1LD1LB_0RB0RC (p : positive) : cconf := (StD, (Jp p ++ [S0], S0, [])).
Local Notation Cc := Cc_1RB0LC_1LC0RA_1LD1LB_0RB0RC.

(** ** The certificate *)

Definition A0_1RB0LC_1LC0RA_1LD1LB_0RB0RC : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition A1_1RB0LC_1LC0RA_1LD1LB_0RB0RC : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chi_1RB0LC_1LC0RA_1LD1LB_0RB0RC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 4; SWin 1; SUnrotL 1].

Lemma run_int_1RB0LC_1LC0RA_1LD1LB_0RB0RC : srun tm false true chi_1RB0LC_1LC0RA_1LD1LB_0RB0RC A0_1RB0LC_1LC0RA_1LD1LB_0RB0RC = Some (A1_1RB0LC_1LC0RA_1LD1LB_0RB0RC, 6, 4).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB0LC_1LC0RA_1LD1LB_0RB0RC : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_1RB0LC_1LC0RA_1LD1LB_0RB0RC : sconf := mkC StD (mkS [] [S1;S1] 1 1 [S1;S0]) S0 (mkS [] [] 0 0 []).
(** ** The INNER anchor family -- Jp at StB *)
Definition Cin_1RB0LC_1LC0RA_1LD1LB_0RB0RC (v : positive) : cconf := (StB, (Jp v ++ [S1], S0, [])).
Local Notation Cin := Cin_1RB0LC_1LC0RA_1LD1LB_0RB0RC.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow2_1RB0LC_1LC0RA_1LD1LB_0RB0RC : forall n, Jp (pow2 n) = rep [S1;S1] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap -- ordinary and affine.  Iterating it to the fill is
    where a [Theta(2^j)] lives, and [inner_to_fill_lift] keeps it inside an
    existential. *)
Definition AI0_1RB0LC_1LC0RA_1LD1LB_0RB0RC : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition AI1_1RB0LC_1LC0RA_1LD1LB_0RB0RC : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S0;S0] [] 0 0 []).
Definition chn_1RB0LC_1LC0RA_1LD1LB_0RB0RC : list lstep := [SWinR 8; SCycL 2 0; SWin 6; SCycR 4].

Lemma run_inner_1RB0LC_1LC0RA_1LD1LB_0RB0RC : srun tm false true chn_1RB0LC_1LC0RA_1LD1LB_0RB0RC AI0_1RB0LC_1LC0RA_1LD1LB_0RB0RC = Some (AI1_1RB0LC_1LC0RA_1LD1LB_0RB0RC, 6, 14).
Proof. vm_compute. reflexivity. Qed.

(** *** boot: the outer overflow anchor -> the first inner anchor at [pow2 j] *)
Definition BB1_1RB0LC_1LC0RA_1LD1LB_0RB0RC : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S1]) S0 (mkS [S0] [] 0 0 []).
Definition chb_1RB0LC_1LC0RA_1LD1LB_0RB0RC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 3; SCycR 2].

Lemma run_boot_1RB0LC_1LC0RA_1LD1LB_0RB0RC : srun tm true true chb_1RB0LC_1LC0RA_1LD1LB_0RB0RC B0_1RB0LC_1LC0RA_1LD1LB_0RB0RC = Some (BB1_1RB0LC_1LC0RA_1LD1LB_0RB0RC, 4, 5).
Proof. vm_compute. reflexivity. Qed.

(** *** exit: the last inner all-ones fill -> the outer successor *)
Definition BE0_1RB0LC_1LC0RA_1LD1LB_0RB0RC : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition che_1RB0LC_1LC0RA_1LD1LB_0RB0RC : list lstep := [SWinR 8; SCycL 2 0; SWin 6; SCycR 4; SWin 2; SFoldL 1].

Lemma run_exit_1RB0LC_1LC0RA_1LD1LB_0RB0RC : srun tm true true che_1RB0LC_1LC0RA_1LD1LB_0RB0RC BE0_1RB0LC_1LC0RA_1LD1LB_0RB0RC = Some (B1_1RB0LC_1LC0RA_1LD1LB_0RB0RC, 6, 16).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_1RB0LC_1LC0RA_1LD1LB_0RB0RC : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Jp q0 ++ [S0]) [] j A0_1RB0LC_1LC0RA_1LD1LB_0RB0RC.
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (H1 & _).
  unfold Cc_1RB0LC_1LC0RA_1LD1LB_0RB0RC, cden, A0_1RB0LC_1LC0RA_1LD1LB_0RB0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gei_1RB0LC_1LC0RA_1LD1LB_0RB0RC : forall p j q0, cview p = (j, Some q0) ->
  cden (Jp q0 ++ [S0]) [] j A1_1RB0LC_1LC0RA_1LD1LB_0RB0RC = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (_ & H2).
  unfold Cc_1RB0LC_1LC0RA_1LD1LB_0RB0RC, cden, A1_1RB0LC_1LC0RA_1LD1LB_0RB0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB0LC_1LC0RA_1LD1LB_0RB0RC : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (6 * j + 4). split; [lia|].
  rewrite (gsi_1RB0LC_1LC0RA_1LD1LB_0RB0RC p j q0 E).
  rewrite (srun_sound tm false true chi_1RB0LC_1LC0RA_1LD1LB_0RB0RC A0_1RB0LC_1LC0RA_1LD1LB_0RB0RC A1_1RB0LC_1LC0RA_1LD1LB_0RB0RC 6 4
             run_int_1RB0LC_1LC0RA_1LD1LB_0RB0RC (Jp q0 ++ [S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_1RB0LC_1LC0RA_1LD1LB_0RB0RC p j q0 E).
Qed.

Lemma gso_1RB0LC_1LC0RA_1LD1LB_0RB0RC : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_1RB0LC_1LC0RA_1LD1LB_0RB0RC.
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (H1 & _).
  unfold Cc_1RB0LC_1LC0RA_1LD1LB_0RB0RC, cden, B0_1RB0LC_1LC0RA_1LD1LB_0RB0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB0LC_1LC0RA_1LD1LB_0RB0RC : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB0LC_1LC0RA_1LD1LB_0RB0RC : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB0LC_1LC0RA_1LD1LB_0RB0RC) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB0LC_1LC0RA_1LD1LB_0RB0RC
             = (StD, (rep [S1;S1] (S j) ++ [S1;S0], S0, []))).
  { unfold cden, B1_1RB0LC_1LC0RA_1LD1LB_0RB0RC, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StD, (rep [S1;S1] (S j) ++ [S1;S0], S0, []))).
  { unfold Cc_1RB0LC_1LC0RA_1LD1LB_0RB0RC. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. reflexivity.
Qed.

Lemma gsn_1RB0LC_1LC0RA_1LD1LB_0RB0RC : forall v i q0, cview v = (i, Some q0) ->
  Cin v = cden (Jp q0 ++ [S1]) [] i AI0_1RB0LC_1LC0RA_1LD1LB_0RB0RC.
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (H1 & _).
  unfold Cin_1RB0LC_1LC0RA_1LD1LB_0RB0RC, cden, AI0_1RB0LC_1LC0RA_1LD1LB_0RB0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen_1RB0LC_1LC0RA_1LD1LB_0RB0RC : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Jp q0 ++ [S1]) [] i AI1_1RB0LC_1LC0RA_1LD1LB_0RB0RC) = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (_ & H2).
  unfold Cin_1RB0LC_1LC0RA_1LD1LB_0RB0RC, cden, AI1_1RB0LC_1LC0RA_1LD1LB_0RB0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S0;S0]) with ((([]) ++ [S0]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin_1RB0LC_1LC0RA_1LD1LB_0RB0RC : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (6 * i + 14), (cden (Jp q0 ++ [S1]) [] i AI1_1RB0LC_1LC0RA_1LD1LB_0RB0RC).
  split; [lia|]. split; [| exact (gen_1RB0LC_1LC0RA_1LD1LB_0RB0RC v i q0 E)].
  rewrite (gsn_1RB0LC_1LC0RA_1LD1LB_0RB0RC v i q0 E).
  exact (srun_sound tm false true chn_1RB0LC_1LC0RA_1LD1LB_0RB0RC AI0_1RB0LC_1LC0RA_1LD1LB_0RB0RC AI1_1RB0LC_1LC0RA_1LD1LB_0RB0RC 6 14
           run_inner_1RB0LC_1LC0RA_1LD1LB_0RB0RC (Jp q0 ++ [S1]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The chain into this family lands on its anchor up to 0/1
    trailing blanks. *)
Lemma gbo_1RB0LC_1LC0RA_1LD1LB_0RB0RC : forall j, lift (cden [] [] j BB1_1RB0LC_1LC0RA_1LD1LB_0RB0RC) = lift (Cin (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_1RB0LC_1LC0RA_1LD1LB_0RB0RC = (StB, (rep [S1;S1] j ++ [S1;S1], S0, ([]) ++ [S0]))).
  { unfold cden, BB1_1RB0LC_1LC0RA_1LD1LB_0RB0RC, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin (pow2 j) = (StB, (rep [S1;S1] j ++ [S1;S1], S0, []))).
  { unfold Cin_1RB0LC_1LC0RA_1LD1LB_0RB0RC. rewrite epow2_1RB0LC_1LC0RA_1LD1LB_0RB0RC.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_1RB0LC_1LC0RA_1LD1LB_0RB0RC. rewrite ?lift_app_blank. reflexivity.
Qed.

(** This family's all-ones fill IS the next chain's start.  [cview (fill
    (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    family's own overflow decomposition names the word. *)
Lemma gxi_1RB0LC_1LC0RA_1LD1LB_0RB0RC : forall j, Cin (fill (pow2 j)) = cden [] [] j BE0_1RB0LC_1LC0RA_1LD1LB_0RB0RC.
Proof.
  intro j.
  destruct (JpCounter.cview_none_J (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin_1RB0LC_1LC0RA_1LD1LB_0RB0RC, cden, BE0_1RB0LC_1LC0RA_1LD1LB_0RB0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

(** The interior lap, restated up to [lift] -- what [vis_via_ovf_lift] and
    [vis_via_fill] consume. *)
Lemma lapil_1RB0LC_1LC0RA_1LD1LB_0RB0RC : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof. intros p j q0 E. destruct (lapi_1RB0LC_1LC0RA_1LD1LB_0RB0RC p j q0 E) as (n & Hn & Hr).
  exists n, (Cc (Pos.succ p)).
  split; [exact Hn | split; [exact Hr | reflexivity]]. Qed.

(** The outer OVERFLOW branch, composed.  The exponential cost is the
    [exists n] inside [inner_to_fill_lift]; no formula for it is ever
    written. *)
Lemma lapo_1RB0LC_1LC0RA_1LD1LB_0RB0RC : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E.
  apply (nested_overflow_lift tm Cc Cin lapin_1RB0LC_1LC0RA_1LD1LB_0RB0RC p (pow2 j)).
  - exists (4 * j + 5), (cden [] [] j BB1_1RB0LC_1LC0RA_1LD1LB_0RB0RC).
    split; [lia|]. split; [| exact (gbo_1RB0LC_1LC0RA_1LD1LB_0RB0RC j)].
    rewrite (gso_1RB0LC_1LC0RA_1LD1LB_0RB0RC p j E).
    exact (srun_sound tm true true chb_1RB0LC_1LC0RA_1LD1LB_0RB0RC B0_1RB0LC_1LC0RA_1LD1LB_0RB0RC BB1_1RB0LC_1LC0RA_1LD1LB_0RB0RC 4 5
             run_boot_1RB0LC_1LC0RA_1LD1LB_0RB0RC [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  - exists (6 * j + 16), (cden [] [] j B1_1RB0LC_1LC0RA_1LD1LB_0RB0RC).
    split; [| exact (geo_1RB0LC_1LC0RA_1LD1LB_0RB0RC p j E)].
    rewrite (gxi_1RB0LC_1LC0RA_1LD1LB_0RB0RC j).
    exact (srun_sound tm true true che_1RB0LC_1LC0RA_1LD1LB_0RB0RC BE0_1RB0LC_1LC0RA_1LD1LB_0RB0RC B1_1RB0LC_1LC0RA_1LD1LB_0RB0RC 6 16
             run_exit_1RB0LC_1LC0RA_1LD1LB_0RB0RC [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.



(** ** The lap *)

Lemma lap_1RB0LC_1LC0RA_1LD1LB_0RB0RC : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB0LC_1LC0RA_1LD1LB_0RB0RC p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->). exact (lapo_1RB0LC_1LC0RA_1LD1LB_0RB0RC p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_1RB0LC_1LC0RA_1LD1LB_0RB0RC : exists t0, stepn tm t0 InitES = Some (lift (Cc 2)).
Proof.
  exists 19.
  assert (H : match csteps tm 19 c0 with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 19 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_1RB0LC_1LC0RA_1LD1LB_0RB0RC : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_1RB0LC_1LC0RA_1LD1LB_0RB0RC = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_1RB0LC_1LC0RA_1LD1LB_0RB0RC p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB0LC_1LC0RA_1LD1LB_0RB0RC p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_1RB0LC_1LC0RA_1LD1LB_0RB0RC : forall t, ~ In t pins_1RB0LC_1LC0RA_1LD1LB_0RB0RC ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_1RB0LC_1LC0RA_1LD1LB_0RB0RC.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_via_ovf tm Cc Hi (StA, S0)), fireo_1RB0LC_1LC0RA_1LD1LB_0RB0RC
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1]).
    vm_compute; reflexivity.
  - (* A1 *)
    apply (fire_via_ovf tm Cc Hi (StA, S1)), fireo_1RB0LC_1LC0RA_1LD1LB_0RB0RC
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 3; SCycR 2; SWinR 4]).
    vm_compute; reflexivity.
  - (* B0 *)
    apply (fire_via_ovf tm Cc Hi (StB, S0)), fireo_1RB0LC_1LC0RA_1LD1LB_0RB0RC
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 1]).
    vm_compute; reflexivity.
  - (* B1 *)
    apply (fire_via_ovf tm Cc Hi (StB, S1)), fireo_1RB0LC_1LC0RA_1LD1LB_0RB0RC
      with (l := [SRotL 1; SWin 1]).
    vm_compute; reflexivity.
  - (* C0 *)
    apply (fire_via_ovf tm Cc Hi (StC, S0)), fireo_1RB0LC_1LC0RA_1LD1LB_0RB0RC
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 3; SCycR 2; SWin 1]).
    vm_compute; reflexivity.
  - (* C1 *)
    apply (fire_via_ovf tm Cc Hi (StC, S1)), fireo_1RB0LC_1LC0RA_1LD1LB_0RB0RC
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 2]).
    vm_compute; reflexivity.
  - (* D0 *)
    apply (fire_via_ovf tm Cc Hi (StD, S0)), fireo_1RB0LC_1LC0RA_1LD1LB_0RB0RC
      with (l := []).
    vm_compute; reflexivity.
  - (* D1 *)
    apply (fire_via_ovf tm Cc Hi (StD, S1)), fireo_1RB0LC_1LC0RA_1LD1LB_0RB0RC
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 3; SCycR 2; SWin 1; SWinR 7; SRotL 1; SWin 1; SRotL 1; SWin 3]).
    vm_compute; reflexivity.
Qed.

Theorem nqhtrm_1RB0LC_1LC0RA_1LD1LB_0RB0RC : NeverQuasiHaltsTr tmm_1RB0LC_1LC0RA_1LD1LB_0RB0RC.
Proof.
  apply (glue_neverqhtr tmm_1RB0LC_1LC0RA_1LD1LB_0RB0RC pins_1RB0LC_1LC0RA_1LD1LB_0RB0RC Cc 2).
  - exact boot_1RB0LC_1LC0RA_1LD1LB_0RB0RC.
  - intros p _. apply lap_1RB0LC_1LC0RA_1LD1LB_0RB0RC.
  - intros t Ht p _. apply fire_1RB0LC_1LC0RA_1LD1LB_0RB0RC. exact Ht.
Qed.

Theorem nqhtr_1RB0LC_1LC0RA_1LD1LB_0RB0RC : NeverQuasiHaltsTr tm_1RB0LC_1LC0RA_1LD1LB_0RB0RC.
Proof. apply (neverqhtr_mirror tm_1RB0LC_1LC0RA_1LD1LB_0RB0RC). rewrite mirror_ok_1RB0LC_1LC0RA_1LD1LB_0RB0RC. exact nqhtrm_1RB0LC_1LC0RA_1LD1LB_0RB0RC. Qed.

Theorem nonhalt_1RB0LC_1LC0RA_1LD1LB_0RB0RC : NonHalt tm_1RB0LC_1LC0RA_1LD1LB_0RB0RC.
Proof. apply never_qh_tr_nonhalt, nqhtr_1RB0LC_1LC0RA_1LD1LB_0RB0RC. Qed.
