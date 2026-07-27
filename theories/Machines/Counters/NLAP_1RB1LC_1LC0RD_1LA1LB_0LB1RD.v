(** * NLAP_1RB1LC_1LC0RD_1LA1LB_0LB1RD: machine 1RB1LC_1LC0RD_1LA1LB_0LB1RD, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Jp digit alphabet (JpCounter.v), anchored at

      Cc p = (StB, (Jp p ++ [S1;S0;S1;S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  4*j+8 steps
      overflow  (cview p = (S j, None)):   boot 4*j+8, then the inner counter's own laps to the
                                           all-ones fill, then exit 4*j+16

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

Definition mk_1RB1LC_1LC0RD_1LA1LB_0LB1RD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1LC_1LC0RD_1LA1LB_0LB1RD.

(** 1RB1LC_1LC0RD_1LA1LB_0LB1RD *)
Definition tm_1RB1LC_1LC0RD_1LA1LB_0LB1RD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StC
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DR StD
  | StC, S0 => mk S1 DL StA | StC, S1 => mk S1 DL StB
  | StD, S0 => mk S0 DL StB | StD, S1 => mk S1 DR StD end.
Local Notation tm := tm_1RB1LC_1LC0RD_1LA1LB_0LB1RD.

Definition Cc_1RB1LC_1LC0RD_1LA1LB_0LB1RD (p : positive) : cconf := (StB, (Jp p ++ [S1;S0;S1;S0], S0, [])).
Local Notation Cc := Cc_1RB1LC_1LC0RD_1LA1LB_0LB1RD.

(** ** The certificate *)

Definition A0_1RB1LC_1LC0RD_1LA1LB_0LB1RD : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition A1_1RB1LC_1LC0RD_1LA1LB_0LB1RD : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S0] [] 0 0 []).
Definition chi_1RB1LC_1LC0RD_1LA1LB_0LB1RD : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWinR 4].

Lemma run_int_1RB1LC_1LC0RD_1LA1LB_0LB1RD : srun tm false true chi_1RB1LC_1LC0RD_1LA1LB_0LB1RD A0_1RB1LC_1LC0RD_1LA1LB_0LB1RD = Some (A1_1RB1LC_1LC0RD_1LA1LB_0LB1RD, 4, 8).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB1LC_1LC0RD_1LA1LB_0LB1RD : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S1;S0;S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_1RB1LC_1LC0RD_1LA1LB_0LB1RD : sconf := mkC StB (mkS [] [S1;S1] 1 1 [S1;S1;S0;S1]) S0 (mkS [S0] [] 0 0 []).
(** ** The INNER anchor family

    The overflow phase runs a SECOND counter, in the Jp alphabet at
    state StB -- not necessarily the outer one (measured: inner /= outer on
    37% of this bucket, which is why an [Ip]-at-both-levels template derives
    none of it). *)
Definition Cin_1RB1LC_1LC0RD_1LA1LB_0LB1RD (v : positive) : cconf := (StB, (Jp v ++ [S0;S0;S1], S0, [])).
Local Notation Cin := Cin_1RB1LC_1LC0RD_1LA1LB_0LB1RD.

(** [E (2^n) = A^n C]: the boot's landing value, in the inner alphabet. *)
Lemma epow2_1RB1LC_1LC0RD_1LA1LB_0LB1RD : forall n, Jp (pow2 n) = rep [S1;S1] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** *** boot: the outer overflow anchor -> the inner anchor at [pow2 j] *)
Definition BB1_1RB1LC_1LC0RD_1LA1LB_0LB1RD : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S0;S0;S1;S0]) S0 (mkS [S0] [] 0 0 []).
Definition chb_1RB1LC_1LC0RD_1LA1LB_0LB1RD : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWinR 4].

Lemma run_boot_1RB1LC_1LC0RD_1LA1LB_0LB1RD : srun tm true true chb_1RB1LC_1LC0RD_1LA1LB_0LB1RD B0_1RB1LC_1LC0RD_1LA1LB_0LB1RD = Some (BB1_1RB1LC_1LC0RD_1LA1LB_0LB1RD, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** *** exit: the inner all-ones fill -> the outer successor *)
Definition BE0_1RB1LC_1LC0RD_1LA1LB_0LB1RD : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S0;S0;S1]) S0 (mkS [] [] 0 0 []).
Definition che_1RB1LC_1LC0RD_1LA1LB_0LB1RD : list lstep := [SCycL 2 0; SWin 4; SWinL 8; SCycR 2; SWinR 4; SRotL 2; SFoldL 1].

Lemma run_exit_1RB1LC_1LC0RD_1LA1LB_0LB1RD : srun tm true true che_1RB1LC_1LC0RD_1LA1LB_0LB1RD BE0_1RB1LC_1LC0RD_1LA1LB_0LB1RD = Some (B1_1RB1LC_1LC0RD_1LA1LB_0LB1RD, 4, 16).
Proof. vm_compute. reflexivity. Qed.

(** *** the inner family's own INTERIOR lap -- ordinary and affine.  Iterating
    it to the fill is where the [Theta(2^j)] cost lives, and
    [NestedLapLift.inner_to_fill_lift] keeps it inside an existential. *)
Definition AI0_1RB1LC_1LC0RD_1LA1LB_0LB1RD : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition AI1_1RB1LC_1LC0RD_1LA1LB_0LB1RD : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S0] [] 0 0 []).
Definition chn_1RB1LC_1LC0RD_1LA1LB_0LB1RD : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWinR 4].

Lemma run_inner_1RB1LC_1LC0RD_1LA1LB_0LB1RD : srun tm false true chn_1RB1LC_1LC0RD_1LA1LB_0LB1RD AI0_1RB1LC_1LC0RD_1LA1LB_0LB1RD = Some (AI1_1RB1LC_1LC0RD_1LA1LB_0LB1RD, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_1RB1LC_1LC0RD_1LA1LB_0LB1RD : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Jp q0 ++ [S1;S0;S1;S0]) [] j A0_1RB1LC_1LC0RD_1LA1LB_0LB1RD.
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (H1 & _).
  unfold Cc_1RB1LC_1LC0RD_1LA1LB_0LB1RD, cden, A0_1RB1LC_1LC0RD_1LA1LB_0LB1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

(** The lap ends on [S0] where the anchor has [] -- one trailing blank,
    which [lift] cannot see. *)
Lemma gei_1RB1LC_1LC0RD_1LA1LB_0LB1RD : forall p j q0, cview p = (j, Some q0) ->
  lift (cden (Jp q0 ++ [S1;S0;S1;S0]) [] j A1_1RB1LC_1LC0RD_1LA1LB_0LB1RD) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (_ & H2).
  unfold Cc_1RB1LC_1LC0RD_1LA1LB_0LB1RD, cden, A1_1RB1LC_1LC0RD_1LA1LB_0LB1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S0]) with (([]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB1LC_1LC0RD_1LA1LB_0LB1RD : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  exists (4 * j + 8), (cden (Jp q0 ++ [S1;S0;S1;S0]) [] j A1_1RB1LC_1LC0RD_1LA1LB_0LB1RD).
  split; [lia|]. split; [| exact (gei_1RB1LC_1LC0RD_1LA1LB_0LB1RD p j q0 E)].
  rewrite (gsi_1RB1LC_1LC0RD_1LA1LB_0LB1RD p j q0 E).
  exact (srun_sound tm false true chi_1RB1LC_1LC0RD_1LA1LB_0LB1RD A0_1RB1LC_1LC0RD_1LA1LB_0LB1RD A1_1RB1LC_1LC0RD_1LA1LB_0LB1RD 4 8
           run_int_1RB1LC_1LC0RD_1LA1LB_0LB1RD (Jp q0 ++ [S1;S0;S1;S0]) [] j
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma gso_1RB1LC_1LC0RD_1LA1LB_0LB1RD : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_1RB1LC_1LC0RD_1LA1LB_0LB1RD.
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (H1 & _).
  unfold Cc_1RB1LC_1LC0RD_1LA1LB_0LB1RD, cden, B0_1RB1LC_1LC0RD_1LA1LB_0LB1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB1LC_1LC0RD_1LA1LB_0LB1RD : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB1LC_1LC0RD_1LA1LB_0LB1RD : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB1LC_1LC0RD_1LA1LB_0LB1RD) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB1LC_1LC0RD_1LA1LB_0LB1RD
             = (StB, (rep [S1;S1] (S j) ++ [S1;S1;S0;S1], S0, ([]) ++ [S0]))).
  { unfold cden, B1_1RB1LC_1LC0RD_1LA1LB_0LB1RD, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. reflexivity. }
  assert (HC : Cc (Pos.succ p) = (StB, ((rep [S1;S1] (S j) ++ [S1;S1;S0;S1]) ++ [S0], S0, []))).
  { unfold Cc_1RB1LC_1LC0RD_1LA1LB_0LB1RD. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lift_app_blank. rewrite !lbl_1RB1LC_1LC0RD_1LA1LB_0LB1RD. reflexivity.
Qed.

(** ** Nested-overflow glue *)

Lemma gsn_1RB1LC_1LC0RD_1LA1LB_0LB1RD : forall v i q0, cview v = (i, Some q0) ->
  Cin v = cden (Jp q0 ++ [S0;S0;S1]) [] i AI0_1RB1LC_1LC0RD_1LA1LB_0LB1RD.
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (H1 & _).
  unfold Cin_1RB1LC_1LC0RD_1LA1LB_0LB1RD, cden, AI0_1RB1LC_1LC0RD_1LA1LB_0LB1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen_1RB1LC_1LC0RD_1LA1LB_0LB1RD : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Jp q0 ++ [S0;S0;S1]) [] i AI1_1RB1LC_1LC0RD_1LA1LB_0LB1RD) = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (_ & H2).
  unfold Cin_1RB1LC_1LC0RD_1LA1LB_0LB1RD, cden, AI1_1RB1LC_1LC0RD_1LA1LB_0LB1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S0]) with (([]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin_1RB1LC_1LC0RD_1LA1LB_0LB1RD : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 8), (cden (Jp q0 ++ [S0;S0;S1]) [] i AI1_1RB1LC_1LC0RD_1LA1LB_0LB1RD).
  split; [lia|]. split; [| exact (gen_1RB1LC_1LC0RD_1LA1LB_0LB1RD v i q0 E)].
  rewrite (gsn_1RB1LC_1LC0RD_1LA1LB_0LB1RD v i q0 E).
  exact (srun_sound tm false true chn_1RB1LC_1LC0RD_1LA1LB_0LB1RD AI0_1RB1LC_1LC0RD_1LA1LB_0LB1RD AI1_1RB1LC_1LC0RD_1LA1LB_0LB1RD 4 8
           run_inner_1RB1LC_1LC0RD_1LA1LB_0LB1RD (Jp q0 ++ [S0;S0;S1]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The boot lands on the inner anchor up to 1/1 trailing blanks. *)
Lemma gbo_1RB1LC_1LC0RD_1LA1LB_0LB1RD : forall j, lift (cden [] [] j BB1_1RB1LC_1LC0RD_1LA1LB_0LB1RD) = lift (Cin (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_1RB1LC_1LC0RD_1LA1LB_0LB1RD = (StB, ((rep [S1;S1] j ++ [S1;S0;S0;S1]) ++ [S0], S0, ([]) ++ [S0]))).
  { unfold cden, BB1_1RB1LC_1LC0RD_1LA1LB_0LB1RD, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin (pow2 j) = (StB, (rep [S1;S1] j ++ [S1;S0;S0;S1], S0, []))).
  { unfold Cin_1RB1LC_1LC0RD_1LA1LB_0LB1RD. rewrite epow2_1RB1LC_1LC0RD_1LA1LB_0LB1RD.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_1RB1LC_1LC0RD_1LA1LB_0LB1RD. rewrite ?lift_app_blank. reflexivity.
Qed.

(** The inner counter's all-ones fill IS the exit chain's start.  [cview
    (fill (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    inner alphabet's own overflow decomposition names the word. *)
Lemma gxi_1RB1LC_1LC0RD_1LA1LB_0LB1RD : forall j, Cin (fill (pow2 j)) = cden [] [] j BE0_1RB1LC_1LC0RD_1LA1LB_0LB1RD.
Proof.
  intro j.
  destruct (JpCounter.cview_none_J (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin_1RB1LC_1LC0RD_1LA1LB_0LB1RD, cden, BE0_1RB1LC_1LC0RD_1LA1LB_0LB1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

(** The interior lap, restated up to [lift] -- what [vis_via_ovf_lift] and
    [vis_via_fill] consume. *)
Lemma lapil_1RB1LC_1LC0RD_1LA1LB_0LB1RD : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof. exact lapi_1RB1LC_1LC0RD_1LA1LB_0LB1RD. Qed.

(** The outer OVERFLOW branch, composed.  The exponential cost is the [exists
    n] inside [inner_to_fill_lift]; no formula for it is ever written. *)
Lemma lapo_1RB1LC_1LC0RD_1LA1LB_0LB1RD : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E.
  apply (nested_overflow_lift tm Cc Cin lapin_1RB1LC_1LC0RD_1LA1LB_0LB1RD p (pow2 j)).
  - exists (4 * j + 8), (cden [] [] j BB1_1RB1LC_1LC0RD_1LA1LB_0LB1RD).
    split; [lia|]. split; [| exact (gbo_1RB1LC_1LC0RD_1LA1LB_0LB1RD j)].
    rewrite (gso_1RB1LC_1LC0RD_1LA1LB_0LB1RD p j E).
    exact (srun_sound tm true true chb_1RB1LC_1LC0RD_1LA1LB_0LB1RD B0_1RB1LC_1LC0RD_1LA1LB_0LB1RD BB1_1RB1LC_1LC0RD_1LA1LB_0LB1RD 4 8
             run_boot_1RB1LC_1LC0RD_1LA1LB_0LB1RD [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  - exists (4 * j + 16), (cden [] [] j B1_1RB1LC_1LC0RD_1LA1LB_0LB1RD).
    split; [| exact (geo_1RB1LC_1LC0RD_1LA1LB_0LB1RD p j E)].
    rewrite (gxi_1RB1LC_1LC0RD_1LA1LB_0LB1RD j).
    exact (srun_sound tm true true che_1RB1LC_1LC0RD_1LA1LB_0LB1RD BE0_1RB1LC_1LC0RD_1LA1LB_0LB1RD B1_1RB1LC_1LC0RD_1LA1LB_0LB1RD 4 16
             run_exit_1RB1LC_1LC0RD_1LA1LB_0LB1RD [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** A state firing in the EXIT chain is reached from the outer overflow
    anchor by boot + the inner counter's own laps + that prefix. *)
Lemma visx_1RB1LC_1LC0RD_1LA1LB_0LB1RD : forall (l : list lstep) (q : St),
  srun_st tm true true l BE0_1RB1LC_1LC0RD_1LA1LB_0LB1RD = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros l q Hst p j E.
  apply (vis_via_fill tm Cc Cin lapin_1RB1LC_1LC0RD_1LA1LB_0LB1RD q p (pow2 j)).
  - exists (4 * j + 8), (cden [] [] j BB1_1RB1LC_1LC0RD_1LA1LB_0LB1RD). split;
      [| exact (gbo_1RB1LC_1LC0RD_1LA1LB_0LB1RD j)].
    rewrite (gso_1RB1LC_1LC0RD_1LA1LB_0LB1RD p j E).
    exact (srun_sound tm true true chb_1RB1LC_1LC0RD_1LA1LB_0LB1RD B0_1RB1LC_1LC0RD_1LA1LB_0LB1RD BB1_1RB1LC_1LC0RD_1LA1LB_0LB1RD 4 8
             run_boot_1RB1LC_1LC0RD_1LA1LB_0LB1RD [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  - apply (vis_lift_of_csteps tm (fun _ : positive => Cin (fill (pow2 j))) xH).
    apply (vis_of_run tm (fun _ : positive => Cin (fill (pow2 j)))
                      true true l BE0_1RB1LC_1LC0RD_1LA1LB_0LB1RD xH j [] []);
      [exact Hst | reflexivity | reflexivity | exact (gxi_1RB1LC_1LC0RD_1LA1LB_0LB1RD j)].
Qed.



(** ** The lap *)

Lemma lap_1RB1LC_1LC0RD_1LA1LB_0LB1RD : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB1LC_1LC0RD_1LA1LB_0LB1RD p j q0 E) as (n & c' & Hn & Hrun & Hlift).
    exists n, c'. split; [exact Hrun | split; [exact Hlift | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->). exact (lapo_1RB1LC_1LC0RD_1LA1LB_0LB1RD p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_1RB1LC_1LC0RD_1LA1LB_0LB1RD : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 13.
  assert (H : match csteps tm 13 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 13 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma viso_1RB1LC_1LC0RD_1LA1LB_0LB1RD : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_1RB1LC_1LC0RD_1LA1LB_0LB1RD = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_1RB1LC_1LC0RD_1LA1LB_0LB1RD p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB1LC_1LC0RD_1LA1LB_0LB1RD p j E)].
Qed.

Lemma vis_1RB1LC_1LC0RD_1LA1LB_0LB1RD : forall p q, exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros p q.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n c', 0 < n /\ csteps tm n (Cc p0) = Some c'
                         /\ lift c' = lift (Cc (Pos.succ p0)))
    by exact lapi_1RB1LC_1LC0RD_1LA1LB_0LB1RD.
  destruct q.

  - (* StA: fires in the exit half of the overflow *)
    apply (vis_via_ovf_lift tm Cc lapil_1RB1LC_1LC0RD_1LA1LB_0LB1RD StA).
    intros p1 j1 E1.
    exact (visx_1RB1LC_1LC0RD_1LA1LB_0LB1RD [SCycL 2 0; SWin 4] StA ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* StB: the anchor state *)
    exists 0. eexists. split; reflexivity.
  - (* StC *)
    apply (vis_via_ovf_lift tm Cc Hi StC).
    intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
    apply (viso_1RB1LC_1LC0RD_1LA1LB_0LB1RD [SCycL 2 0; SWin 1] StC ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* StD *)
    apply (vis_via_ovf_lift tm Cc Hi StD).
    intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
    apply (viso_1RB1LC_1LC0RD_1LA1LB_0LB1RD [SCycL 2 0; SWin 3] StD ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
Qed.

(** The interior lap closes only up to [lift] (one trailing blank past the
    anchor's far side), so the closer is [LapCertGlueLift.glue_neverqh_lift]:
    [LapGlue.glue_neverqh] with the visit premise in [stepn] space, which is
    what its own proof consumes. *)
Theorem nqh_1RB1LC_1LC0RD_1LA1LB_0LB1RD : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh_lift tm Cc 1). - exact boot_1RB1LC_1LC0RD_1LA1LB_0LB1RD. - intros p _. apply lap_1RB1LC_1LC0RD_1LA1LB_0LB1RD. - intros p q _. apply vis_1RB1LC_1LC0RD_1LA1LB_0LB1RD. Qed.

Theorem nonhalt_1RB1LC_1LC0RD_1LA1LB_0LB1RD : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_1RB1LC_1LC0RD_1LA1LB_0LB1RD. Qed.
