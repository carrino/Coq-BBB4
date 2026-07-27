(** * NLAP_1RB____1LB1RC_0RD0LB_0RB0RC: machine 1RB---_1LB1RC_0RD0LB_0RB0RC, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Jp digit alphabet (JpCounter.v), anchored at

      Cc p = (StB, (Jp p ++ [S1;S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  4*j+8 steps
      overflow  (cview p = (S j, None)):   boot 4*j+8, then the inner counter's own laps to the
                                           all-ones fill, then exit 4*j+12

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
Import ListNotations.

Definition mk_1RB____1LB1RC_0RD0LB_0RB0RC (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB____1LB1RC_0RD0LB_0RB0RC.

(** 1RB---_1LB1RC_0RD0LB_0RB0RC *)
(** 1RB---_1LB1RC_0RD0LB_0RB0RC -- the real machine (its counter grows RIGHT). *)
Definition tm_1RB____1LB1RC_0RD0LB_0RB0RC : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => None
  | StB, S0 => mk S1 DL StB | StB, S1 => mk S1 DR StC
  | StC, S0 => mk S0 DR StD | StC, S1 => mk S0 DL StB
  | StD, S0 => mk S0 DR StB | StD, S1 => mk S0 DR StC end.

(** Its mirror 1LB---_1RB1LC_0LD0RB_0LB0LC: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_1RB____1LB1RC_0RD0LB_0RB0RC : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => None
  | StB, S0 => mk S1 DR StB | StB, S1 => mk S1 DL StC
  | StC, S0 => mk S0 DL StD | StC, S1 => mk S0 DR StB
  | StD, S0 => mk S0 DL StB | StD, S1 => mk S0 DL StC end.
Local Notation tm := tmm_1RB____1LB1RC_0RD0LB_0RB0RC.

Lemma mirror_ok_1RB____1LB1RC_0RD0LB_0RB0RC : mirror_tm tm_1RB____1LB1RC_0RD0LB_0RB0RC = tmm_1RB____1LB1RC_0RD0LB_0RB0RC.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_1RB____1LB1RC_0RD0LB_0RB0RC (p : positive) : cconf := (StB, (Jp p ++ [S1;S0], S0, [S1])).
Local Notation Cc := Cc_1RB____1LB1RC_0RD0LB_0RB0RC.

(** ** The certificate *)

Definition A0_1RB____1LB1RC_0RD0LB_0RB0RC : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition A1_1RB____1LB1RC_0RD0LB_0RB0RC : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S1] [] 0 0 []).
Definition chi_1RB____1LB1RC_0RD0LB_0RB0RC : list lstep := [SWin 4; SCycL 2 0; SWin 4; SCycR 2].

Lemma run_int_1RB____1LB1RC_0RD0LB_0RB0RC : srun tm false true chi_1RB____1LB1RC_0RD0LB_0RB0RC A0_1RB____1LB1RC_0RD0LB_0RB0RC = Some (A1_1RB____1LB1RC_0RD0LB_0RB0RC, 4, 8).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB____1LB1RC_0RD0LB_0RB0RC : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S1;S0]) S0 (mkS [S1] [] 0 0 []).
Definition B1_1RB____1LB1RC_0RD0LB_0RB0RC : sconf := mkC StB (mkS [] [S1;S1] 1 1 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
(** ** The INNER anchor family

    The overflow phase runs a SECOND counter, in the Jp alphabet at
    state StB -- not necessarily the outer one (measured: inner /= outer on
    37% of this bucket, which is why an [Ip]-at-both-levels template derives
    none of it). *)
Definition Cin_1RB____1LB1RC_0RD0LB_0RB0RC (v : positive) : cconf := (StB, (Jp v ++ [], S0, [S1])).
Local Notation Cin := Cin_1RB____1LB1RC_0RD0LB_0RB0RC.

(** [E (2^n) = A^n C]: the boot's landing value, in the inner alphabet. *)
Lemma epow2_1RB____1LB1RC_0RD0LB_0RB0RC : forall n, Jp (pow2 n) = rep [S1;S1] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** *** boot: the outer overflow anchor -> the inner anchor at [pow2 j] *)
Definition BB1_1RB____1LB1RC_0RD0LB_0RB0RC : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S0;S0]) S0 (mkS [S1] [] 0 0 []).
Definition chb_1RB____1LB1RC_0RD0LB_0RB0RC : list lstep := [SWin 4; SCycL 2 0; SWin 4; SCycR 2].

Lemma run_boot_1RB____1LB1RC_0RD0LB_0RB0RC : srun tm true true chb_1RB____1LB1RC_0RD0LB_0RB0RC B0_1RB____1LB1RC_0RD0LB_0RB0RC = Some (BB1_1RB____1LB1RC_0RD0LB_0RB0RC, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** *** exit: the inner all-ones fill -> the outer successor *)
Definition BE0_1RB____1LB1RC_0RD0LB_0RB0RC : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1]) S0 (mkS [S1] [] 0 0 []).
Definition che_1RB____1LB1RC_0RD0LB_0RB0RC : list lstep := [SWin 4; SCycL 2 0; SWin 1; SWinL 7; SCycR 2; SRotL 2; SFoldL 1].

Lemma run_exit_1RB____1LB1RC_0RD0LB_0RB0RC : srun tm true true che_1RB____1LB1RC_0RD0LB_0RB0RC BE0_1RB____1LB1RC_0RD0LB_0RB0RC = Some (B1_1RB____1LB1RC_0RD0LB_0RB0RC, 4, 12).
Proof. vm_compute. reflexivity. Qed.

(** *** the inner family's own INTERIOR lap -- ordinary and affine.  Iterating
    it to the fill is where the [Theta(2^j)] cost lives, and
    [NestedLapLift.inner_to_fill_lift] keeps it inside an existential. *)
Definition AI0_1RB____1LB1RC_0RD0LB_0RB0RC : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition AI1_1RB____1LB1RC_0RD0LB_0RB0RC : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S1] [] 0 0 []).
Definition chn_1RB____1LB1RC_0RD0LB_0RB0RC : list lstep := [SWin 4; SCycL 2 0; SWin 4; SCycR 2].

Lemma run_inner_1RB____1LB1RC_0RD0LB_0RB0RC : srun tm false true chn_1RB____1LB1RC_0RD0LB_0RB0RC AI0_1RB____1LB1RC_0RD0LB_0RB0RC = Some (AI1_1RB____1LB1RC_0RD0LB_0RB0RC, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_1RB____1LB1RC_0RD0LB_0RB0RC : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Jp q0 ++ [S1;S0]) [] j A0_1RB____1LB1RC_0RD0LB_0RB0RC.
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (H1 & _).
  unfold Cc_1RB____1LB1RC_0RD0LB_0RB0RC, cden, A0_1RB____1LB1RC_0RD0LB_0RB0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gei_1RB____1LB1RC_0RD0LB_0RB0RC : forall p j q0, cview p = (j, Some q0) ->
  cden (Jp q0 ++ [S1;S0]) [] j A1_1RB____1LB1RC_0RD0LB_0RB0RC = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (_ & H2).
  unfold Cc_1RB____1LB1RC_0RD0LB_0RB0RC, cden, A1_1RB____1LB1RC_0RD0LB_0RB0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB____1LB1RC_0RD0LB_0RB0RC : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (4 * j + 8). split; [lia|].
  rewrite (gsi_1RB____1LB1RC_0RD0LB_0RB0RC p j q0 E).
  rewrite (srun_sound tm false true chi_1RB____1LB1RC_0RD0LB_0RB0RC A0_1RB____1LB1RC_0RD0LB_0RB0RC A1_1RB____1LB1RC_0RD0LB_0RB0RC 4 8
             run_int_1RB____1LB1RC_0RD0LB_0RB0RC (Jp q0 ++ [S1;S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_1RB____1LB1RC_0RD0LB_0RB0RC p j q0 E).
Qed.

Lemma gso_1RB____1LB1RC_0RD0LB_0RB0RC : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_1RB____1LB1RC_0RD0LB_0RB0RC.
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (H1 & _).
  unfold Cc_1RB____1LB1RC_0RD0LB_0RB0RC, cden, B0_1RB____1LB1RC_0RD0LB_0RB0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB____1LB1RC_0RD0LB_0RB0RC : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB____1LB1RC_0RD0LB_0RB0RC : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB____1LB1RC_0RD0LB_0RB0RC) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB____1LB1RC_0RD0LB_0RB0RC
             = (StB, (rep [S1;S1] (S j) ++ [S1;S1], S0, [S1]))).
  { unfold cden, B1_1RB____1LB1RC_0RD0LB_0RB0RC, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. reflexivity. }
  assert (HC : Cc (Pos.succ p) = (StB, ((rep [S1;S1] (S j) ++ [S1;S1]) ++ [S0], S0, [S1]))).
  { unfold Cc_1RB____1LB1RC_0RD0LB_0RB0RC. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_1RB____1LB1RC_0RD0LB_0RB0RC. reflexivity.
Qed.

(** ** Nested-overflow glue *)

Lemma gsn_1RB____1LB1RC_0RD0LB_0RB0RC : forall v i q0, cview v = (i, Some q0) ->
  Cin v = cden (Jp q0 ++ []) [] i AI0_1RB____1LB1RC_0RD0LB_0RB0RC.
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (H1 & _).
  unfold Cin_1RB____1LB1RC_0RD0LB_0RB0RC, cden, AI0_1RB____1LB1RC_0RD0LB_0RB0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen_1RB____1LB1RC_0RD0LB_0RB0RC : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Jp q0 ++ []) [] i AI1_1RB____1LB1RC_0RD0LB_0RB0RC) = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (_ & H2).
  unfold Cin_1RB____1LB1RC_0RD0LB_0RB0RC, cden, AI1_1RB____1LB1RC_0RD0LB_0RB0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin_1RB____1LB1RC_0RD0LB_0RB0RC : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 8), (cden (Jp q0 ++ []) [] i AI1_1RB____1LB1RC_0RD0LB_0RB0RC).
  split; [lia|]. split; [| exact (gen_1RB____1LB1RC_0RD0LB_0RB0RC v i q0 E)].
  rewrite (gsn_1RB____1LB1RC_0RD0LB_0RB0RC v i q0 E).
  exact (srun_sound tm false true chn_1RB____1LB1RC_0RD0LB_0RB0RC AI0_1RB____1LB1RC_0RD0LB_0RB0RC AI1_1RB____1LB1RC_0RD0LB_0RB0RC 4 8
           run_inner_1RB____1LB1RC_0RD0LB_0RB0RC (Jp q0 ++ []) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The boot lands on the inner anchor up to 2/0 trailing blanks. *)
Lemma gbo_1RB____1LB1RC_0RD0LB_0RB0RC : forall j, lift (cden [] [] j BB1_1RB____1LB1RC_0RD0LB_0RB0RC) = lift (Cin (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_1RB____1LB1RC_0RD0LB_0RB0RC = (StB, (((rep [S1;S1] j ++ [S1]) ++ [S0]) ++ [S0], S0, [S1]))).
  { unfold cden, BB1_1RB____1LB1RC_0RD0LB_0RB0RC, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin (pow2 j) = (StB, (rep [S1;S1] j ++ [S1], S0, [S1]))).
  { unfold Cin_1RB____1LB1RC_0RD0LB_0RB0RC. rewrite epow2_1RB____1LB1RC_0RD0LB_0RB0RC.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_1RB____1LB1RC_0RD0LB_0RB0RC. rewrite ?lift_app_blank. reflexivity.
Qed.

(** The inner counter's all-ones fill IS the exit chain's start.  [cview
    (fill (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    inner alphabet's own overflow decomposition names the word. *)
Lemma gxi_1RB____1LB1RC_0RD0LB_0RB0RC : forall j, Cin (fill (pow2 j)) = cden [] [] j BE0_1RB____1LB1RC_0RD0LB_0RB0RC.
Proof.
  intro j.
  destruct (JpCounter.cview_none_J (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin_1RB____1LB1RC_0RD0LB_0RB0RC, cden, BE0_1RB____1LB1RC_0RD0LB_0RB0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

(** The interior lap, restated up to [lift] -- what [vis_via_ovf_lift] and
    [vis_via_fill] consume. *)
Lemma lapil_1RB____1LB1RC_0RD0LB_0RB0RC : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof. intros p j q0 E. destruct (lapi_1RB____1LB1RC_0RD0LB_0RB0RC p j q0 E) as (n & Hn & Hr).
  exists n, (Cc (Pos.succ p)).
  split; [exact Hn | split; [exact Hr | reflexivity]]. Qed.

(** The outer OVERFLOW branch, composed.  The exponential cost is the [exists
    n] inside [inner_to_fill_lift]; no formula for it is ever written. *)
Lemma lapo_1RB____1LB1RC_0RD0LB_0RB0RC : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E.
  apply (nested_overflow_lift tm Cc Cin lapin_1RB____1LB1RC_0RD0LB_0RB0RC p (pow2 j)).
  - exists (4 * j + 8), (cden [] [] j BB1_1RB____1LB1RC_0RD0LB_0RB0RC).
    split; [lia|]. split; [| exact (gbo_1RB____1LB1RC_0RD0LB_0RB0RC j)].
    rewrite (gso_1RB____1LB1RC_0RD0LB_0RB0RC p j E).
    exact (srun_sound tm true true chb_1RB____1LB1RC_0RD0LB_0RB0RC B0_1RB____1LB1RC_0RD0LB_0RB0RC BB1_1RB____1LB1RC_0RD0LB_0RB0RC 4 8
             run_boot_1RB____1LB1RC_0RD0LB_0RB0RC [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  - exists (4 * j + 12), (cden [] [] j B1_1RB____1LB1RC_0RD0LB_0RB0RC).
    split; [| exact (geo_1RB____1LB1RC_0RD0LB_0RB0RC p j E)].
    rewrite (gxi_1RB____1LB1RC_0RD0LB_0RB0RC j).
    exact (srun_sound tm true true che_1RB____1LB1RC_0RD0LB_0RB0RC BE0_1RB____1LB1RC_0RD0LB_0RB0RC B1_1RB____1LB1RC_0RD0LB_0RB0RC 4 12
             run_exit_1RB____1LB1RC_0RD0LB_0RB0RC [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.



(** ** The lap *)

Lemma lap_1RB____1LB1RC_0RD0LB_0RB0RC : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB____1LB1RC_0RD0LB_0RB0RC p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->). exact (lapo_1RB____1LB1RC_0RD0LB_0RB0RC p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_1RB____1LB1RC_0RD0LB_0RB0RC : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 9.
  assert (H : match csteps tm 9 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 9 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma viso_1RB____1LB1RC_0RD0LB_0RB0RC : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_1RB____1LB1RC_0RD0LB_0RB0RC = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_1RB____1LB1RC_0RD0LB_0RB0RC p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB____1LB1RC_0RD0LB_0RB0RC p j E)].
Qed.

Lemma vis_1RB____1LB1RC_0RD0LB_0RB0RC : forall p q, q <> StA -> exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q Hq.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_1RB____1LB1RC_0RD0LB_0RB0RC.
  destruct q.

  - (* StA: quiet -- see the closing theorem *)
    exfalso; exact (Hq eq_refl).
  - (* StB: the anchor state *)
    exists 0. eexists. split; reflexivity.
  - (* StC *)
    apply (vis_via_ovf tm Cc Hi StC), viso_1RB____1LB1RC_0RD0LB_0RB0RC
      with (l := [SWin 2]).
    vm_compute; reflexivity.
  - (* StD *)
    apply (vis_via_ovf tm Cc Hi StD), viso_1RB____1LB1RC_0RD0LB_0RB0RC
      with (l := [SWin 4; SCycL 2 0; SWin 1]).
    vm_compute; reflexivity.
Qed.

(** StA is TARGETED BY NOTHING, so its only visit is at configuration index
    0 and the quiet bound is 1 -- weakened to the census tier's 2000. *)
Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.

Theorem iqhm_1RB____1LB1RC_0RD0LB_0RB0RC : iqh tmm_1RB____1LB1RC_0RD0LB_0RB0RC.
Proof.
  destruct (glue_qh tm Cc 1 boot_1RB____1LB1RC_0RD0LB_0RB0RC (fun p _ => lap_1RB____1LB1RC_0RD0LB_0RB0RC p)
                    (fun p q _ Hq => vis_1RB____1LB1RC_0RD0LB_0RB0RC p q Hq)
                    (ltac:(intros q b tr Ht; destruct q, b; cbn in Ht;
                           try discriminate; injection Ht as <-; discriminate)))
    as (Hn & Hb & Hq).
  split; [exact Hn | split; [| exact Hq]].
  apply (qhbound_mono 1 2000); [lia | exact Hb].
Qed.

(** Transfer to the REAL machine.  [mirror_nonhalt] and [mirror_qh]
    are Mirror.v; [qhbound_mirror] is Census/TNF_QH.v. *)
Theorem iqh_1RB____1LB1RC_0RD0LB_0RB0RC : iqh tm_1RB____1LB1RC_0RD0LB_0RB0RC.
Proof.
  destruct iqhm_1RB____1LB1RC_0RD0LB_0RB0RC as (Hn & Hb & Hq).
  rewrite <- mirror_ok_1RB____1LB1RC_0RD0LB_0RB0RC in Hn, Hb, Hq.
  split; [exact (mirror_nonhalt _ Hn)
         | split; [exact (qhbound_mirror _ _ Hb)
                  | exact (mirror_qh _ Hq)]].
Qed.

Theorem nonhalt_1RB____1LB1RC_0RD0LB_0RB0RC : NonHalt tm_1RB____1LB1RC_0RD0LB_0RB0RC.
Proof. apply (proj1 iqh_1RB____1LB1RC_0RD0LB_0RB0RC). Qed.
