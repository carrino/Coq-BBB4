(** * NLAP_1RB1RD_1LB1LC_0RD1LC_1RA0LC: machine 1RB1RD_1LB1LC_0RD1LC_1RA0LC, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Jp digit alphabet (JpCounter.v), anchored at

      Cc p = (StD, (Jp p ++ [S1;S0], S0, []))

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

Definition mk_1RB1RD_1LB1LC_0RD1LC_1RA0LC (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1RD_1LB1LC_0RD1LC_1RA0LC.

(** 1RB1RD_1LB1LC_0RD1LC_1RA0LC *)
(** 1RB1RD_1LB1LC_0RD1LC_1RA0LC -- the real machine (its counter grows RIGHT). *)
Definition tm_1RB1RD_1LB1LC_0RD1LC_1RA0LC : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DR StD
  | StB, S0 => mk S1 DL StB | StB, S1 => mk S1 DL StC
  | StC, S0 => mk S0 DR StD | StC, S1 => mk S1 DL StC
  | StD, S0 => mk S1 DR StA | StD, S1 => mk S0 DL StC end.

(** Its mirror 1LB1LD_1RB1RC_0LD1RC_1LA0RC: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_1RB1RD_1LB1LC_0RD1LC_1RA0LC : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => mk S1 DL StD
  | StB, S0 => mk S1 DR StB | StB, S1 => mk S1 DR StC
  | StC, S0 => mk S0 DL StD | StC, S1 => mk S1 DR StC
  | StD, S0 => mk S1 DL StA | StD, S1 => mk S0 DR StC end.
Local Notation tm := tmm_1RB1RD_1LB1LC_0RD1LC_1RA0LC.

Lemma mirror_ok_1RB1RD_1LB1LC_0RD1LC_1RA0LC : mirror_tm tm_1RB1RD_1LB1LC_0RD1LC_1RA0LC = tmm_1RB1RD_1LB1LC_0RD1LC_1RA0LC.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_1RB1RD_1LB1LC_0RD1LC_1RA0LC (p : positive) : cconf := (StD, (Jp p ++ [S1;S0], S0, [])).
Local Notation Cc := Cc_1RB1RD_1LB1LC_0RD1LC_1RA0LC.

(** ** The certificate *)

Definition A0_1RB1RD_1LB1LC_0RD1LC_1RA0LC : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition A1_1RB1RD_1LB1LC_0RD1LC_1RA0LC : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S0] [] 0 0 []).
Definition chi_1RB1RD_1LB1LC_0RD1LC_1RA0LC : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWinR 4].

Lemma run_int_1RB1RD_1LB1LC_0RD1LC_1RA0LC : srun tm false true chi_1RB1RD_1LB1LC_0RD1LC_1RA0LC A0_1RB1RD_1LB1LC_0RD1LC_1RA0LC = Some (A1_1RB1RD_1LB1LC_0RD1LC_1RA0LC, 4, 8).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB1RD_1LB1LC_0RD1LC_1RA0LC : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_1RB1RD_1LB1LC_0RD1LC_1RA0LC : sconf := mkC StD (mkS [] [S1;S1] 1 1 [S1;S1]) S0 (mkS [S0] [] 0 0 []).
(** ** The INNER anchor family

    The overflow phase runs a SECOND counter, in the Jp alphabet at
    state StD -- not necessarily the outer one (measured: inner /= outer on
    37% of this bucket, which is why an [Ip]-at-both-levels template derives
    none of it). *)
Definition Cin_1RB1RD_1LB1LC_0RD1LC_1RA0LC (v : positive) : cconf := (StD, (Jp v ++ [], S0, [])).
Local Notation Cin := Cin_1RB1RD_1LB1LC_0RD1LC_1RA0LC.

(** [E (2^n) = A^n C]: the boot's landing value, in the inner alphabet. *)
Lemma epow2_1RB1RD_1LB1LC_0RD1LC_1RA0LC : forall n, Jp (pow2 n) = rep [S1;S1] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** *** boot: the outer overflow anchor -> the inner anchor at [pow2 j] *)
Definition BB1_1RB1RD_1LB1LC_0RD1LC_1RA0LC : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0;S0]) S0 (mkS [S0] [] 0 0 []).
Definition chb_1RB1RD_1LB1LC_0RD1LC_1RA0LC : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWinR 4].

Lemma run_boot_1RB1RD_1LB1LC_0RD1LC_1RA0LC : srun tm true true chb_1RB1RD_1LB1LC_0RD1LC_1RA0LC B0_1RB1RD_1LB1LC_0RD1LC_1RA0LC = Some (BB1_1RB1RD_1LB1LC_0RD1LC_1RA0LC, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** *** exit: the inner all-ones fill -> the outer successor *)
Definition BE0_1RB1RD_1LB1LC_0RD1LC_1RA0LC : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1]) S0 (mkS [] [] 0 0 []).
Definition che_1RB1RD_1LB1LC_0RD1LC_1RA0LC : list lstep := [SCycL 2 0; SWin 1; SWinL 7; SCycR 2; SWinR 4; SRotL 2; SFoldL 1].

Lemma run_exit_1RB1RD_1LB1LC_0RD1LC_1RA0LC : srun tm true true che_1RB1RD_1LB1LC_0RD1LC_1RA0LC BE0_1RB1RD_1LB1LC_0RD1LC_1RA0LC = Some (B1_1RB1RD_1LB1LC_0RD1LC_1RA0LC, 4, 12).
Proof. vm_compute. reflexivity. Qed.

(** *** the inner family's own INTERIOR lap -- ordinary and affine.  Iterating
    it to the fill is where the [Theta(2^j)] cost lives, and
    [NestedLapLift.inner_to_fill_lift] keeps it inside an existential. *)
Definition AI0_1RB1RD_1LB1LC_0RD1LC_1RA0LC : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition AI1_1RB1RD_1LB1LC_0RD1LC_1RA0LC : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S0] [] 0 0 []).
Definition chn_1RB1RD_1LB1LC_0RD1LC_1RA0LC : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWinR 4].

Lemma run_inner_1RB1RD_1LB1LC_0RD1LC_1RA0LC : srun tm false true chn_1RB1RD_1LB1LC_0RD1LC_1RA0LC AI0_1RB1RD_1LB1LC_0RD1LC_1RA0LC = Some (AI1_1RB1RD_1LB1LC_0RD1LC_1RA0LC, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_1RB1RD_1LB1LC_0RD1LC_1RA0LC : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Jp q0 ++ [S1;S0]) [] j A0_1RB1RD_1LB1LC_0RD1LC_1RA0LC.
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (H1 & _).
  unfold Cc_1RB1RD_1LB1LC_0RD1LC_1RA0LC, cden, A0_1RB1RD_1LB1LC_0RD1LC_1RA0LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

(** The lap ends on [S0] where the anchor has [] -- one trailing blank,
    which [lift] cannot see. *)
Lemma gei_1RB1RD_1LB1LC_0RD1LC_1RA0LC : forall p j q0, cview p = (j, Some q0) ->
  lift (cden (Jp q0 ++ [S1;S0]) [] j A1_1RB1RD_1LB1LC_0RD1LC_1RA0LC) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (_ & H2).
  unfold Cc_1RB1RD_1LB1LC_0RD1LC_1RA0LC, cden, A1_1RB1RD_1LB1LC_0RD1LC_1RA0LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S0]) with (([]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB1RD_1LB1LC_0RD1LC_1RA0LC : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  exists (4 * j + 8), (cden (Jp q0 ++ [S1;S0]) [] j A1_1RB1RD_1LB1LC_0RD1LC_1RA0LC).
  split; [lia|]. split; [| exact (gei_1RB1RD_1LB1LC_0RD1LC_1RA0LC p j q0 E)].
  rewrite (gsi_1RB1RD_1LB1LC_0RD1LC_1RA0LC p j q0 E).
  exact (srun_sound tm false true chi_1RB1RD_1LB1LC_0RD1LC_1RA0LC A0_1RB1RD_1LB1LC_0RD1LC_1RA0LC A1_1RB1RD_1LB1LC_0RD1LC_1RA0LC 4 8
           run_int_1RB1RD_1LB1LC_0RD1LC_1RA0LC (Jp q0 ++ [S1;S0]) [] j
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma gso_1RB1RD_1LB1LC_0RD1LC_1RA0LC : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_1RB1RD_1LB1LC_0RD1LC_1RA0LC.
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (H1 & _).
  unfold Cc_1RB1RD_1LB1LC_0RD1LC_1RA0LC, cden, B0_1RB1RD_1LB1LC_0RD1LC_1RA0LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB1RD_1LB1LC_0RD1LC_1RA0LC : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB1RD_1LB1LC_0RD1LC_1RA0LC : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB1RD_1LB1LC_0RD1LC_1RA0LC) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB1RD_1LB1LC_0RD1LC_1RA0LC
             = (StD, (rep [S1;S1] (S j) ++ [S1;S1], S0, ([]) ++ [S0]))).
  { unfold cden, B1_1RB1RD_1LB1LC_0RD1LC_1RA0LC, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. reflexivity. }
  assert (HC : Cc (Pos.succ p) = (StD, ((rep [S1;S1] (S j) ++ [S1;S1]) ++ [S0], S0, []))).
  { unfold Cc_1RB1RD_1LB1LC_0RD1LC_1RA0LC. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lift_app_blank. rewrite !lbl_1RB1RD_1LB1LC_0RD1LC_1RA0LC. reflexivity.
Qed.

(** ** Nested-overflow glue *)

Lemma gsn_1RB1RD_1LB1LC_0RD1LC_1RA0LC : forall v i q0, cview v = (i, Some q0) ->
  Cin v = cden (Jp q0 ++ []) [] i AI0_1RB1RD_1LB1LC_0RD1LC_1RA0LC.
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (H1 & _).
  unfold Cin_1RB1RD_1LB1LC_0RD1LC_1RA0LC, cden, AI0_1RB1RD_1LB1LC_0RD1LC_1RA0LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen_1RB1RD_1LB1LC_0RD1LC_1RA0LC : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Jp q0 ++ []) [] i AI1_1RB1RD_1LB1LC_0RD1LC_1RA0LC) = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (_ & H2).
  unfold Cin_1RB1RD_1LB1LC_0RD1LC_1RA0LC, cden, AI1_1RB1RD_1LB1LC_0RD1LC_1RA0LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S0]) with (([]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin_1RB1RD_1LB1LC_0RD1LC_1RA0LC : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 8), (cden (Jp q0 ++ []) [] i AI1_1RB1RD_1LB1LC_0RD1LC_1RA0LC).
  split; [lia|]. split; [| exact (gen_1RB1RD_1LB1LC_0RD1LC_1RA0LC v i q0 E)].
  rewrite (gsn_1RB1RD_1LB1LC_0RD1LC_1RA0LC v i q0 E).
  exact (srun_sound tm false true chn_1RB1RD_1LB1LC_0RD1LC_1RA0LC AI0_1RB1RD_1LB1LC_0RD1LC_1RA0LC AI1_1RB1RD_1LB1LC_0RD1LC_1RA0LC 4 8
           run_inner_1RB1RD_1LB1LC_0RD1LC_1RA0LC (Jp q0 ++ []) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The boot lands on the inner anchor up to 2/1 trailing blanks. *)
Lemma gbo_1RB1RD_1LB1LC_0RD1LC_1RA0LC : forall j, lift (cden [] [] j BB1_1RB1RD_1LB1LC_0RD1LC_1RA0LC) = lift (Cin (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_1RB1RD_1LB1LC_0RD1LC_1RA0LC = (StD, (((rep [S1;S1] j ++ [S1]) ++ [S0]) ++ [S0], S0, ([]) ++ [S0]))).
  { unfold cden, BB1_1RB1RD_1LB1LC_0RD1LC_1RA0LC, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin (pow2 j) = (StD, (rep [S1;S1] j ++ [S1], S0, []))).
  { unfold Cin_1RB1RD_1LB1LC_0RD1LC_1RA0LC. rewrite epow2_1RB1RD_1LB1LC_0RD1LC_1RA0LC.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_1RB1RD_1LB1LC_0RD1LC_1RA0LC. rewrite ?lift_app_blank. reflexivity.
Qed.

(** The inner counter's all-ones fill IS the exit chain's start.  [cview
    (fill (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    inner alphabet's own overflow decomposition names the word. *)
Lemma gxi_1RB1RD_1LB1LC_0RD1LC_1RA0LC : forall j, Cin (fill (pow2 j)) = cden [] [] j BE0_1RB1RD_1LB1LC_0RD1LC_1RA0LC.
Proof.
  intro j.
  destruct (JpCounter.cview_none_J (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin_1RB1RD_1LB1LC_0RD1LC_1RA0LC, cden, BE0_1RB1RD_1LB1LC_0RD1LC_1RA0LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

(** The interior lap, restated up to [lift] -- what [vis_via_ovf_lift] and
    [vis_via_fill] consume. *)
Lemma lapil_1RB1RD_1LB1LC_0RD1LC_1RA0LC : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof. exact lapi_1RB1RD_1LB1LC_0RD1LC_1RA0LC. Qed.

(** The outer OVERFLOW branch, composed.  The exponential cost is the [exists
    n] inside [inner_to_fill_lift]; no formula for it is ever written. *)
Lemma lapo_1RB1RD_1LB1LC_0RD1LC_1RA0LC : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E.
  apply (nested_overflow_lift tm Cc Cin lapin_1RB1RD_1LB1LC_0RD1LC_1RA0LC p (pow2 j)).
  - exists (4 * j + 8), (cden [] [] j BB1_1RB1RD_1LB1LC_0RD1LC_1RA0LC).
    split; [lia|]. split; [| exact (gbo_1RB1RD_1LB1LC_0RD1LC_1RA0LC j)].
    rewrite (gso_1RB1RD_1LB1LC_0RD1LC_1RA0LC p j E).
    exact (srun_sound tm true true chb_1RB1RD_1LB1LC_0RD1LC_1RA0LC B0_1RB1RD_1LB1LC_0RD1LC_1RA0LC BB1_1RB1RD_1LB1LC_0RD1LC_1RA0LC 4 8
             run_boot_1RB1RD_1LB1LC_0RD1LC_1RA0LC [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  - exists (4 * j + 12), (cden [] [] j B1_1RB1RD_1LB1LC_0RD1LC_1RA0LC).
    split; [| exact (geo_1RB1RD_1LB1LC_0RD1LC_1RA0LC p j E)].
    rewrite (gxi_1RB1RD_1LB1LC_0RD1LC_1RA0LC j).
    exact (srun_sound tm true true che_1RB1RD_1LB1LC_0RD1LC_1RA0LC BE0_1RB1RD_1LB1LC_0RD1LC_1RA0LC B1_1RB1RD_1LB1LC_0RD1LC_1RA0LC 4 12
             run_exit_1RB1RD_1LB1LC_0RD1LC_1RA0LC [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** A state firing in the EXIT chain is reached from the outer overflow
    anchor by boot + the inner counter's own laps + that prefix. *)
Lemma visx_1RB1RD_1LB1LC_0RD1LC_1RA0LC : forall (l : list lstep) (q : St),
  srun_st tm true true l BE0_1RB1RD_1LB1LC_0RD1LC_1RA0LC = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros l q Hst p j E.
  apply (vis_via_fill tm Cc Cin lapin_1RB1RD_1LB1LC_0RD1LC_1RA0LC q p (pow2 j)).
  - exists (4 * j + 8), (cden [] [] j BB1_1RB1RD_1LB1LC_0RD1LC_1RA0LC). split;
      [| exact (gbo_1RB1RD_1LB1LC_0RD1LC_1RA0LC j)].
    rewrite (gso_1RB1RD_1LB1LC_0RD1LC_1RA0LC p j E).
    exact (srun_sound tm true true chb_1RB1RD_1LB1LC_0RD1LC_1RA0LC B0_1RB1RD_1LB1LC_0RD1LC_1RA0LC BB1_1RB1RD_1LB1LC_0RD1LC_1RA0LC 4 8
             run_boot_1RB1RD_1LB1LC_0RD1LC_1RA0LC [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  - apply (vis_lift_of_csteps tm (fun _ : positive => Cin (fill (pow2 j))) xH).
    apply (vis_of_run tm (fun _ : positive => Cin (fill (pow2 j)))
                      true true l BE0_1RB1RD_1LB1LC_0RD1LC_1RA0LC xH j [] []);
      [exact Hst | reflexivity | reflexivity | exact (gxi_1RB1RD_1LB1LC_0RD1LC_1RA0LC j)].
Qed.



(** ** The lap *)

Lemma lap_1RB1RD_1LB1LC_0RD1LC_1RA0LC : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB1RD_1LB1LC_0RD1LC_1RA0LC p j q0 E) as (n & c' & Hn & Hrun & Hlift).
    exists n, c'. split; [exact Hrun | split; [exact Hlift | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->). exact (lapo_1RB1RD_1LB1LC_0RD1LC_1RA0LC p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_1RB1RD_1LB1LC_0RD1LC_1RA0LC : exists t0, stepn tm t0 InitES = Some (lift (Cc 2)).
Proof.
  exists 18.
  assert (H : match csteps tm 18 c0 with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 18 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma viso_1RB1RD_1LB1LC_0RD1LC_1RA0LC : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_1RB1RD_1LB1LC_0RD1LC_1RA0LC = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_1RB1RD_1LB1LC_0RD1LC_1RA0LC p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB1RD_1LB1LC_0RD1LC_1RA0LC p j E)].
Qed.

Lemma vis_1RB1RD_1LB1LC_0RD1LC_1RA0LC : forall p q, exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros p q.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n c', 0 < n /\ csteps tm n (Cc p0) = Some c'
                         /\ lift c' = lift (Cc (Pos.succ p0)))
    by exact lapi_1RB1RD_1LB1LC_0RD1LC_1RA0LC.
  destruct q.

  - (* StA *)
    apply (vis_via_ovf_lift tm Cc Hi StA).
    intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
    apply (viso_1RB1RD_1LB1LC_0RD1LC_1RA0LC [SCycL 2 0; SWin 1] StA ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* StB: fires in the exit half of the overflow *)
    apply (vis_via_ovf_lift tm Cc lapil_1RB1RD_1LB1LC_0RD1LC_1RA0LC StB).
    intros p1 j1 E1.
    exact (visx_1RB1RD_1LB1LC_0RD1LC_1RA0LC [SCycL 2 0; SWin 1; SWinL 3] StB ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* StC *)
    apply (vis_via_ovf_lift tm Cc Hi StC).
    intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
    apply (viso_1RB1RD_1LB1LC_0RD1LC_1RA0LC [SCycL 2 0; SWin 3] StC ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* StD: the anchor state *)
    exists 0. eexists. split; reflexivity.
Qed.

(** The interior lap closes only up to [lift] (one trailing blank past the
    anchor's far side), so the closer is [LapCertGlueLift.glue_neverqh_lift]:
    [LapGlue.glue_neverqh] with the visit premise in [stepn] space, which is
    what its own proof consumes. *)
Theorem nqhm_1RB1RD_1LB1LC_0RD1LC_1RA0LC : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh_lift tm Cc 2). - exact boot_1RB1RD_1LB1LC_0RD1LC_1RA0LC. - intros p _. apply lap_1RB1RD_1LB1LC_0RD1LC_1RA0LC. - intros p q _. apply vis_1RB1RD_1LB1LC_0RD1LC_1RA0LC. Qed.

Theorem nqh_1RB1RD_1LB1LC_0RD1LC_1RA0LC : NeverQuasiHaltsSt tm_1RB1RD_1LB1LC_0RD1LC_1RA0LC.
Proof. apply (mirror_never_qh tm_1RB1RD_1LB1LC_0RD1LC_1RA0LC). rewrite mirror_ok_1RB1RD_1LB1LC_0RD1LC_1RA0LC. exact nqhm_1RB1RD_1LB1LC_0RD1LC_1RA0LC. Qed.

Theorem nonhalt_1RB1RD_1LB1LC_0RD1LC_1RA0LC : NonHalt tm_1RB1RD_1LB1LC_0RD1LC_1RA0LC.
Proof. apply never_qh_nonhalt, nqh_1RB1RD_1LB1LC_0RD1LC_1RA0LC. Qed.
