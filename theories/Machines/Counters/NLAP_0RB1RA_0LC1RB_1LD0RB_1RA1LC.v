(** * NLAP_0RB1RA_0LC1RB_1LD0RB_1RA1LC: machine 0RB1RA_0LC1RB_1LD0RB_1RA1LC, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Jp digit alphabet (JpCounter.v), anchored at

      Cc p = (StC, (Jp p ++ [S1;S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  4*j+8 steps
      overflow  (cview p = (S j, None)):   boot 4*j+8, then the inner counter's own laps to the
                                           all-ones fill, then exit 4*j+9

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 192 interior anchors (interior); 6 overflow phases, j = 2..7 (246 inner laps) (nested overflow).
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter JpCounter LapCertGlue LapCertGlueLift IXPGadgets NestedLap NestedLapLift.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_0RB1RA_0LC1RB_1LD0RB_1RA1LC (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB1RA_0LC1RB_1LD0RB_1RA1LC.

(** 0RB1RA_0LC1RB_1LD0RB_1RA1LC *)
Definition tm_0RB1RA_0LC1RB_1LD0RB_1RA1LC : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S1 DR StA
  | StB, S0 => mk S0 DL StC | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S1 DL StD | StC, S1 => mk S0 DR StB
  | StD, S0 => mk S1 DR StA | StD, S1 => mk S1 DL StC end.
Local Notation tm := tm_0RB1RA_0LC1RB_1LD0RB_1RA1LC.

Definition Cc_0RB1RA_0LC1RB_1LD0RB_1RA1LC (p : positive) : cconf := (StC, (Jp p ++ [S1;S0], S0, [])).
Local Notation Cc := Cc_0RB1RA_0LC1RB_1LD0RB_1RA1LC.

(** ** The certificate *)

Definition A0_0RB1RA_0LC1RB_1LD0RB_1RA1LC : sconf := mkC StC (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition A1_0RB1RA_0LC1RB_1LD0RB_1RA1LC : sconf := mkC StC (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S0] [] 0 0 []).
Definition chi_0RB1RA_0LC1RB_1LD0RB_1RA1LC : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWinR 4].

Lemma run_int_0RB1RA_0LC1RB_1LD0RB_1RA1LC : srun tm false true chi_0RB1RA_0LC1RB_1LD0RB_1RA1LC A0_0RB1RA_0LC1RB_1LD0RB_1RA1LC = Some (A1_0RB1RA_0LC1RB_1LD0RB_1RA1LC, 4, 8).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB1RA_0LC1RB_1LD0RB_1RA1LC : sconf := mkC StC (mkS [] [S1;S0] 1 0 [S1;S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_0RB1RA_0LC1RB_1LD0RB_1RA1LC : sconf := mkC StC (mkS [] [S1;S1] 1 1 [S1;S1]) S0 (mkS [S0] [] 0 0 []).
(** ** The INNER anchor family

    The overflow phase runs a SECOND counter, in the Jp alphabet at
    state StC -- not necessarily the outer one (measured: inner /= outer on
    37% of this bucket, which is why an [Ip]-at-both-levels template derives
    none of it). *)
Definition Cin_0RB1RA_0LC1RB_1LD0RB_1RA1LC (v : positive) : cconf := (StC, (Jp v ++ [], S0, [])).
Local Notation Cin := Cin_0RB1RA_0LC1RB_1LD0RB_1RA1LC.

(** [E (2^n) = A^n C]: the boot's landing value, in the inner alphabet. *)
Lemma epow2_0RB1RA_0LC1RB_1LD0RB_1RA1LC : forall n, Jp (pow2 n) = rep [S1;S1] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** *** boot: the outer overflow anchor -> the inner anchor at [pow2 j] *)
Definition BB1_0RB1RA_0LC1RB_1LD0RB_1RA1LC : sconf := mkC StC (mkS [] [S1;S1] 1 0 [S1;S0;S0]) S0 (mkS [S0] [] 0 0 []).
Definition chb_0RB1RA_0LC1RB_1LD0RB_1RA1LC : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWinR 4].

Lemma run_boot_0RB1RA_0LC1RB_1LD0RB_1RA1LC : srun tm true true chb_0RB1RA_0LC1RB_1LD0RB_1RA1LC B0_0RB1RA_0LC1RB_1LD0RB_1RA1LC = Some (BB1_0RB1RA_0LC1RB_1LD0RB_1RA1LC, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** *** exit: the inner all-ones fill -> the outer successor *)
Definition BE0_0RB1RA_0LC1RB_1LD0RB_1RA1LC : sconf := mkC StC (mkS [] [S1;S0] 1 0 [S1]) S0 (mkS [] [] 0 0 []).
Definition che_0RB1RA_0LC1RB_1LD0RB_1RA1LC : list lstep := [SCycL 2 0; SWin 1; SWinL 5; SCycR 2; SWinR 3; SRotL 1; SFoldL 1].

Lemma run_exit_0RB1RA_0LC1RB_1LD0RB_1RA1LC : srun tm true true che_0RB1RA_0LC1RB_1LD0RB_1RA1LC BE0_0RB1RA_0LC1RB_1LD0RB_1RA1LC = Some (B1_0RB1RA_0LC1RB_1LD0RB_1RA1LC, 4, 9).
Proof. vm_compute. reflexivity. Qed.

(** *** the inner family's own INTERIOR lap -- ordinary and affine.  Iterating
    it to the fill is where the [Theta(2^j)] cost lives, and
    [NestedLapLift.inner_to_fill_lift] keeps it inside an existential. *)
Definition AI0_0RB1RA_0LC1RB_1LD0RB_1RA1LC : sconf := mkC StC (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition AI1_0RB1RA_0LC1RB_1LD0RB_1RA1LC : sconf := mkC StC (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S0] [] 0 0 []).
Definition chn_0RB1RA_0LC1RB_1LD0RB_1RA1LC : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWinR 4].

Lemma run_inner_0RB1RA_0LC1RB_1LD0RB_1RA1LC : srun tm false true chn_0RB1RA_0LC1RB_1LD0RB_1RA1LC AI0_0RB1RA_0LC1RB_1LD0RB_1RA1LC = Some (AI1_0RB1RA_0LC1RB_1LD0RB_1RA1LC, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_0RB1RA_0LC1RB_1LD0RB_1RA1LC : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Jp q0 ++ [S1;S0]) [] j A0_0RB1RA_0LC1RB_1LD0RB_1RA1LC.
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (H1 & _).
  unfold Cc_0RB1RA_0LC1RB_1LD0RB_1RA1LC, cden, A0_0RB1RA_0LC1RB_1LD0RB_1RA1LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

(** The lap ends on [S0] where the anchor has [] -- one trailing blank,
    which [lift] cannot see. *)
Lemma gei_0RB1RA_0LC1RB_1LD0RB_1RA1LC : forall p j q0, cview p = (j, Some q0) ->
  lift (cden (Jp q0 ++ [S1;S0]) [] j A1_0RB1RA_0LC1RB_1LD0RB_1RA1LC) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (_ & H2).
  unfold Cc_0RB1RA_0LC1RB_1LD0RB_1RA1LC, cden, A1_0RB1RA_0LC1RB_1LD0RB_1RA1LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S0]) with (([]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_0RB1RA_0LC1RB_1LD0RB_1RA1LC : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  exists (4 * j + 8), (cden (Jp q0 ++ [S1;S0]) [] j A1_0RB1RA_0LC1RB_1LD0RB_1RA1LC).
  split; [lia|]. split; [| exact (gei_0RB1RA_0LC1RB_1LD0RB_1RA1LC p j q0 E)].
  rewrite (gsi_0RB1RA_0LC1RB_1LD0RB_1RA1LC p j q0 E).
  exact (srun_sound tm false true chi_0RB1RA_0LC1RB_1LD0RB_1RA1LC A0_0RB1RA_0LC1RB_1LD0RB_1RA1LC A1_0RB1RA_0LC1RB_1LD0RB_1RA1LC 4 8
           run_int_0RB1RA_0LC1RB_1LD0RB_1RA1LC (Jp q0 ++ [S1;S0]) [] j
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma gso_0RB1RA_0LC1RB_1LD0RB_1RA1LC : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_0RB1RA_0LC1RB_1LD0RB_1RA1LC.
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (H1 & _).
  unfold Cc_0RB1RA_0LC1RB_1LD0RB_1RA1LC, cden, B0_0RB1RA_0LC1RB_1LD0RB_1RA1LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_0RB1RA_0LC1RB_1LD0RB_1RA1LC : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_0RB1RA_0LC1RB_1LD0RB_1RA1LC : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB1RA_0LC1RB_1LD0RB_1RA1LC) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_0RB1RA_0LC1RB_1LD0RB_1RA1LC
             = (StC, (rep [S1;S1] (S j) ++ [S1;S1], S0, ([]) ++ [S0]))).
  { unfold cden, B1_0RB1RA_0LC1RB_1LD0RB_1RA1LC, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. reflexivity. }
  assert (HC : Cc (Pos.succ p) = (StC, ((rep [S1;S1] (S j) ++ [S1;S1]) ++ [S0], S0, []))).
  { unfold Cc_0RB1RA_0LC1RB_1LD0RB_1RA1LC. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lift_app_blank. rewrite !lbl_0RB1RA_0LC1RB_1LD0RB_1RA1LC. reflexivity.
Qed.

(** ** Nested-overflow glue *)

Lemma gsn_0RB1RA_0LC1RB_1LD0RB_1RA1LC : forall v i q0, cview v = (i, Some q0) ->
  Cin v = cden (Jp q0 ++ []) [] i AI0_0RB1RA_0LC1RB_1LD0RB_1RA1LC.
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (H1 & _).
  unfold Cin_0RB1RA_0LC1RB_1LD0RB_1RA1LC, cden, AI0_0RB1RA_0LC1RB_1LD0RB_1RA1LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen_0RB1RA_0LC1RB_1LD0RB_1RA1LC : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Jp q0 ++ []) [] i AI1_0RB1RA_0LC1RB_1LD0RB_1RA1LC) = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (_ & H2).
  unfold Cin_0RB1RA_0LC1RB_1LD0RB_1RA1LC, cden, AI1_0RB1RA_0LC1RB_1LD0RB_1RA1LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S0]) with (([]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin_0RB1RA_0LC1RB_1LD0RB_1RA1LC : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 8), (cden (Jp q0 ++ []) [] i AI1_0RB1RA_0LC1RB_1LD0RB_1RA1LC).
  split; [lia|]. split; [| exact (gen_0RB1RA_0LC1RB_1LD0RB_1RA1LC v i q0 E)].
  rewrite (gsn_0RB1RA_0LC1RB_1LD0RB_1RA1LC v i q0 E).
  exact (srun_sound tm false true chn_0RB1RA_0LC1RB_1LD0RB_1RA1LC AI0_0RB1RA_0LC1RB_1LD0RB_1RA1LC AI1_0RB1RA_0LC1RB_1LD0RB_1RA1LC 4 8
           run_inner_0RB1RA_0LC1RB_1LD0RB_1RA1LC (Jp q0 ++ []) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The boot lands on the inner anchor up to 2/1 trailing blanks. *)
Lemma gbo_0RB1RA_0LC1RB_1LD0RB_1RA1LC : forall j, lift (cden [] [] j BB1_0RB1RA_0LC1RB_1LD0RB_1RA1LC) = lift (Cin (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_0RB1RA_0LC1RB_1LD0RB_1RA1LC = (StC, (((rep [S1;S1] j ++ [S1]) ++ [S0]) ++ [S0], S0, ([]) ++ [S0]))).
  { unfold cden, BB1_0RB1RA_0LC1RB_1LD0RB_1RA1LC, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin (pow2 j) = (StC, (rep [S1;S1] j ++ [S1], S0, []))).
  { unfold Cin_0RB1RA_0LC1RB_1LD0RB_1RA1LC. rewrite epow2_0RB1RA_0LC1RB_1LD0RB_1RA1LC.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_0RB1RA_0LC1RB_1LD0RB_1RA1LC. rewrite ?lift_app_blank. reflexivity.
Qed.

(** The inner counter's all-ones fill IS the exit chain's start.  [cview
    (fill (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    inner alphabet's own overflow decomposition names the word. *)
Lemma gxi_0RB1RA_0LC1RB_1LD0RB_1RA1LC : forall j, Cin (fill (pow2 j)) = cden [] [] j BE0_0RB1RA_0LC1RB_1LD0RB_1RA1LC.
Proof.
  intro j.
  destruct (JpCounter.cview_none_J (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin_0RB1RA_0LC1RB_1LD0RB_1RA1LC, cden, BE0_0RB1RA_0LC1RB_1LD0RB_1RA1LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

(** The interior lap, restated up to [lift] -- what [vis_via_ovf_lift] and
    [vis_via_fill] consume. *)
Lemma lapil_0RB1RA_0LC1RB_1LD0RB_1RA1LC : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof. exact lapi_0RB1RA_0LC1RB_1LD0RB_1RA1LC. Qed.

(** The outer OVERFLOW branch, composed.  The exponential cost is the [exists
    n] inside [inner_to_fill_lift]; no formula for it is ever written. *)
Lemma lapo_0RB1RA_0LC1RB_1LD0RB_1RA1LC : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E.
  apply (nested_overflow_lift tm Cc Cin lapin_0RB1RA_0LC1RB_1LD0RB_1RA1LC p (pow2 j)).
  - exists (4 * j + 8), (cden [] [] j BB1_0RB1RA_0LC1RB_1LD0RB_1RA1LC).
    split; [lia|]. split; [| exact (gbo_0RB1RA_0LC1RB_1LD0RB_1RA1LC j)].
    rewrite (gso_0RB1RA_0LC1RB_1LD0RB_1RA1LC p j E).
    exact (srun_sound tm true true chb_0RB1RA_0LC1RB_1LD0RB_1RA1LC B0_0RB1RA_0LC1RB_1LD0RB_1RA1LC BB1_0RB1RA_0LC1RB_1LD0RB_1RA1LC 4 8
             run_boot_0RB1RA_0LC1RB_1LD0RB_1RA1LC [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  - exists (4 * j + 9), (cden [] [] j B1_0RB1RA_0LC1RB_1LD0RB_1RA1LC).
    split; [| exact (geo_0RB1RA_0LC1RB_1LD0RB_1RA1LC p j E)].
    rewrite (gxi_0RB1RA_0LC1RB_1LD0RB_1RA1LC j).
    exact (srun_sound tm true true che_0RB1RA_0LC1RB_1LD0RB_1RA1LC BE0_0RB1RA_0LC1RB_1LD0RB_1RA1LC B1_0RB1RA_0LC1RB_1LD0RB_1RA1LC 4 9
             run_exit_0RB1RA_0LC1RB_1LD0RB_1RA1LC [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** A state firing in the EXIT chain is reached from the outer overflow
    anchor by boot + the inner counter's own laps + that prefix. *)
Lemma visx_0RB1RA_0LC1RB_1LD0RB_1RA1LC : forall (l : list lstep) (q : St),
  srun_st tm true true l BE0_0RB1RA_0LC1RB_1LD0RB_1RA1LC = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros l q Hst p j E.
  apply (vis_via_fill tm Cc Cin lapin_0RB1RA_0LC1RB_1LD0RB_1RA1LC q p (pow2 j)).
  - exists (4 * j + 8), (cden [] [] j BB1_0RB1RA_0LC1RB_1LD0RB_1RA1LC). split;
      [| exact (gbo_0RB1RA_0LC1RB_1LD0RB_1RA1LC j)].
    rewrite (gso_0RB1RA_0LC1RB_1LD0RB_1RA1LC p j E).
    exact (srun_sound tm true true chb_0RB1RA_0LC1RB_1LD0RB_1RA1LC B0_0RB1RA_0LC1RB_1LD0RB_1RA1LC BB1_0RB1RA_0LC1RB_1LD0RB_1RA1LC 4 8
             run_boot_0RB1RA_0LC1RB_1LD0RB_1RA1LC [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  - apply (vis_lift_of_csteps tm (fun _ : positive => Cin (fill (pow2 j))) xH).
    apply (vis_of_run tm (fun _ : positive => Cin (fill (pow2 j)))
                      true true l BE0_0RB1RA_0LC1RB_1LD0RB_1RA1LC xH j [] []);
      [exact Hst | reflexivity | reflexivity | exact (gxi_0RB1RA_0LC1RB_1LD0RB_1RA1LC j)].
Qed.



(** ** The lap *)

Lemma lap_0RB1RA_0LC1RB_1LD0RB_1RA1LC : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB1RA_0LC1RB_1LD0RB_1RA1LC p j q0 E) as (n & c' & Hn & Hrun & Hlift).
    exists n, c'. split; [exact Hrun | split; [exact Hlift | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->). exact (lapo_0RB1RA_0LC1RB_1LD0RB_1RA1LC p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_0RB1RA_0LC1RB_1LD0RB_1RA1LC : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 7.
  assert (H : match csteps tm 7 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 7 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma viso_0RB1RA_0LC1RB_1LD0RB_1RA1LC : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_0RB1RA_0LC1RB_1LD0RB_1RA1LC = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_0RB1RA_0LC1RB_1LD0RB_1RA1LC p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB1RA_0LC1RB_1LD0RB_1RA1LC p j E)].
Qed.

Lemma vis_0RB1RA_0LC1RB_1LD0RB_1RA1LC : forall p q, exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros p q.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n c', 0 < n /\ csteps tm n (Cc p0) = Some c'
                         /\ lift c' = lift (Cc (Pos.succ p0)))
    by exact lapi_0RB1RA_0LC1RB_1LD0RB_1RA1LC.
  destruct q.

  - (* StA: fires in the exit half of the overflow *)
    apply (vis_via_ovf_lift tm Cc lapil_0RB1RA_0LC1RB_1LD0RB_1RA1LC StA).
    intros p1 j1 E1.
    exact (visx_0RB1RA_0LC1RB_1LD0RB_1RA1LC [SCycL 2 0; SWin 1; SWinL 3] StA ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* StB *)
    apply (vis_via_ovf_lift tm Cc Hi StB).
    intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
    apply (viso_0RB1RA_0LC1RB_1LD0RB_1RA1LC [SCycL 2 0; SWin 3] StB ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* StC: the anchor state *)
    exists 0. eexists. split; reflexivity.
  - (* StD *)
    apply (vis_via_ovf_lift tm Cc Hi StD).
    intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
    apply (viso_0RB1RA_0LC1RB_1LD0RB_1RA1LC [SCycL 2 0; SWin 1] StD ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
Qed.

(** The interior lap closes only up to [lift] (one trailing blank past the
    anchor's far side), so the closer is [LapCertGlueLift.glue_neverqh_lift]:
    [LapGlue.glue_neverqh] with the visit premise in [stepn] space, which is
    what its own proof consumes. *)
Theorem nqh_0RB1RA_0LC1RB_1LD0RB_1RA1LC : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh_lift tm Cc 1). - exact boot_0RB1RA_0LC1RB_1LD0RB_1RA1LC. - intros p _. apply lap_0RB1RA_0LC1RB_1LD0RB_1RA1LC. - intros p q _. apply vis_0RB1RA_0LC1RB_1LD0RB_1RA1LC. Qed.

Theorem nonhalt_0RB1RA_0LC1RB_1LD0RB_1RA1LC : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_0RB1RA_0LC1RB_1LD0RB_1RA1LC. Qed.
