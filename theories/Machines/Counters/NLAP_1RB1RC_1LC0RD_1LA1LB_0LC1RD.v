(** * NLAP_1RB1RC_1LC0RD_1LA1LB_0LC1RD: machine 1RB1RC_1LC0RD_1LA1LB_0LC1RD, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Jp digit alphabet (JpCounter.v), anchored at

      Cc p = (StD, (Jp p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  4*j+4 steps
      overflow  (cview p = (S j, None)):   boot 4*j+8, then the inner counter's own laps to the
                                           all-ones fill, then exit 4*j+10

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 192 interior anchors (interior); 6 overflow phases, j = 2..7 (492 inner laps, two counts each) (nested overflow).
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter JpCounter LapCertGlue LapCertGlueLift IXPGadgets NestedLap NestedLapLift NestedLap2.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_1RB1RC_1LC0RD_1LA1LB_0LC1RD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1RC_1LC0RD_1LA1LB_0LC1RD.

(** 1RB1RC_1LC0RD_1LA1LB_0LC1RD *)
Definition tm_1RB1RC_1LC0RD_1LA1LB_0LC1RD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DR StC
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DR StD
  | StC, S0 => mk S1 DL StA | StC, S1 => mk S1 DL StB
  | StD, S0 => mk S0 DL StC | StD, S1 => mk S1 DR StD end.
Local Notation tm := tm_1RB1RC_1LC0RD_1LA1LB_0LC1RD.

Definition Cc_1RB1RC_1LC0RD_1LA1LB_0LC1RD (p : positive) : cconf := (StD, (Jp p ++ [S0], S0, [])).
Local Notation Cc := Cc_1RB1RC_1LC0RD_1LA1LB_0LC1RD.

(** ** The certificate *)

Definition A0_1RB1RC_1LC0RD_1LA1LB_0LC1RD : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition A1_1RB1RC_1LC0RD_1LA1LB_0LC1RD : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chi_1RB1RC_1LC0RD_1LA1LB_0LC1RD : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_int_1RB1RC_1LC0RD_1LA1LB_0LC1RD : srun tm false true chi_1RB1RC_1LC0RD_1LA1LB_0LC1RD A0_1RB1RC_1LC0RD_1LA1LB_0LC1RD = Some (A1_1RB1RC_1LC0RD_1LA1LB_0LC1RD, 4, 4).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB1RC_1LC0RD_1LA1LB_0LC1RD : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_1RB1RC_1LC0RD_1LA1LB_0LC1RD : sconf := mkC StD (mkS [] [S1;S1] 1 1 [S1;S0]) S0 (mkS [] [] 0 0 []).
(** ** The FIRST INNER anchor family -- Jp at StD *)
Definition Cin_1RB1RC_1LC0RD_1LA1LB_0LC1RD (v : positive) : cconf := (StD, (Jp v ++ [S1;S0;S1], S0, [])).
Local Notation Cin := Cin_1RB1RC_1LC0RD_1LA1LB_0LC1RD.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow2_1RB1RC_1LC0RD_1LA1LB_0LC1RD : forall n, Jp (pow2 n) = rep [S1;S1] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap -- ordinary and affine.  Iterating it to the fill is
    where a [Theta(2^j)] lives, and [inner_to_fill_lift] keeps it inside an
    existential. *)
Definition AI0_1RB1RC_1LC0RD_1LA1LB_0LC1RD : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition AI1_1RB1RC_1LC0RD_1LA1LB_0LC1RD : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chn_1RB1RC_1LC0RD_1LA1LB_0LC1RD : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_inner_1RB1RC_1LC0RD_1LA1LB_0LC1RD : srun tm false true chn_1RB1RC_1LC0RD_1LA1LB_0LC1RD AI0_1RB1RC_1LC0RD_1LA1LB_0LC1RD = Some (AI1_1RB1RC_1LC0RD_1LA1LB_0LC1RD, 4, 4).
Proof. vm_compute. reflexivity. Qed.

(** ** The SECOND INNER anchor family -- Jp at StD *)
Definition Cin2_1RB1RC_1LC0RD_1LA1LB_0LC1RD (v : positive) : cconf := (StD, (Jp v ++ [S0;S0;S1], S0, [])).
Local Notation Cin2 := Cin2_1RB1RC_1LC0RD_1LA1LB_0LC1RD.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow22_1RB1RC_1LC0RD_1LA1LB_0LC1RD : forall n, Jp (pow2 n) = rep [S1;S1] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap -- ordinary and affine.  Iterating it to the fill is
    where a [Theta(2^j)] lives, and [inner_to_fill_lift] keeps it inside an
    existential. *)
Definition AI20_1RB1RC_1LC0RD_1LA1LB_0LC1RD : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition AI21_1RB1RC_1LC0RD_1LA1LB_0LC1RD : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chn2_1RB1RC_1LC0RD_1LA1LB_0LC1RD : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_inner2_1RB1RC_1LC0RD_1LA1LB_0LC1RD : srun tm false true chn2_1RB1RC_1LC0RD_1LA1LB_0LC1RD AI20_1RB1RC_1LC0RD_1LA1LB_0LC1RD = Some (AI21_1RB1RC_1LC0RD_1LA1LB_0LC1RD, 4, 4).
Proof. vm_compute. reflexivity. Qed.

(** *** boot: the outer overflow anchor -> the first inner anchor at [pow2 j] *)
Definition BB1_1RB1RC_1LC0RD_1LA1LB_0LC1RD : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S1;S0;S1]) S0 (mkS [] [] 0 0 []).
Definition chb_1RB1RC_1LC0RD_1LA1LB_0LC1RD : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 5; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_boot_1RB1RC_1LC0RD_1LA1LB_0LC1RD : srun tm true true chb_1RB1RC_1LC0RD_1LA1LB_0LC1RD B0_1RB1RC_1LC0RD_1LA1LB_0LC1RD = Some (BB1_1RB1RC_1LC0RD_1LA1LB_0LC1RD, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** *** shift: the FIRST count's all-ones fill -> the SECOND count's anchor.
    WAVE18 section 4c -- "count 8->15, shift, count 8->15 again". *)
Definition BM0_1RB1RC_1LC0RD_1LA1LB_0LC1RD : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1;S0;S1]) S0 (mkS [] [] 0 0 []).
Definition BM1_1RB1RC_1LC0RD_1LA1LB_0LC1RD : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0;S0;S1]) S0 (mkS [] [] 0 0 []).
Definition chm_1RB1RC_1LC0RD_1LA1LB_0LC1RD : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_shift_1RB1RC_1LC0RD_1LA1LB_0LC1RD : srun tm true true chm_1RB1RC_1LC0RD_1LA1LB_0LC1RD BM0_1RB1RC_1LC0RD_1LA1LB_0LC1RD = Some (BM1_1RB1RC_1LC0RD_1LA1LB_0LC1RD, 4, 4).
Proof. vm_compute. reflexivity. Qed.

(** *** exit: the last inner all-ones fill -> the outer successor *)
Definition BE0_1RB1RC_1LC0RD_1LA1LB_0LC1RD : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S0;S0;S1]) S0 (mkS [] [] 0 0 []).
Definition che_1RB1RC_1LC0RD_1LA1LB_0LC1RD : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 8; SCycR 2; SWin 1; SRotL 1; SFoldL 1].

Lemma run_exit_1RB1RC_1LC0RD_1LA1LB_0LC1RD : srun tm true true che_1RB1RC_1LC0RD_1LA1LB_0LC1RD BE0_1RB1RC_1LC0RD_1LA1LB_0LC1RD = Some (B1_1RB1RC_1LC0RD_1LA1LB_0LC1RD, 4, 10).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_1RB1RC_1LC0RD_1LA1LB_0LC1RD : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Jp q0 ++ [S0]) [] j A0_1RB1RC_1LC0RD_1LA1LB_0LC1RD.
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (H1 & _).
  unfold Cc_1RB1RC_1LC0RD_1LA1LB_0LC1RD, cden, A0_1RB1RC_1LC0RD_1LA1LB_0LC1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gei_1RB1RC_1LC0RD_1LA1LB_0LC1RD : forall p j q0, cview p = (j, Some q0) ->
  cden (Jp q0 ++ [S0]) [] j A1_1RB1RC_1LC0RD_1LA1LB_0LC1RD = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (_ & H2).
  unfold Cc_1RB1RC_1LC0RD_1LA1LB_0LC1RD, cden, A1_1RB1RC_1LC0RD_1LA1LB_0LC1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB1RC_1LC0RD_1LA1LB_0LC1RD : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (4 * j + 4). split; [lia|].
  rewrite (gsi_1RB1RC_1LC0RD_1LA1LB_0LC1RD p j q0 E).
  rewrite (srun_sound tm false true chi_1RB1RC_1LC0RD_1LA1LB_0LC1RD A0_1RB1RC_1LC0RD_1LA1LB_0LC1RD A1_1RB1RC_1LC0RD_1LA1LB_0LC1RD 4 4
             run_int_1RB1RC_1LC0RD_1LA1LB_0LC1RD (Jp q0 ++ [S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_1RB1RC_1LC0RD_1LA1LB_0LC1RD p j q0 E).
Qed.

Lemma gso_1RB1RC_1LC0RD_1LA1LB_0LC1RD : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_1RB1RC_1LC0RD_1LA1LB_0LC1RD.
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (H1 & _).
  unfold Cc_1RB1RC_1LC0RD_1LA1LB_0LC1RD, cden, B0_1RB1RC_1LC0RD_1LA1LB_0LC1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB1RC_1LC0RD_1LA1LB_0LC1RD : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB1RC_1LC0RD_1LA1LB_0LC1RD : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB1RC_1LC0RD_1LA1LB_0LC1RD) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB1RC_1LC0RD_1LA1LB_0LC1RD
             = (StD, (rep [S1;S1] (S j) ++ [S1;S0], S0, []))).
  { unfold cden, B1_1RB1RC_1LC0RD_1LA1LB_0LC1RD, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StD, (rep [S1;S1] (S j) ++ [S1;S0], S0, []))).
  { unfold Cc_1RB1RC_1LC0RD_1LA1LB_0LC1RD. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. reflexivity.
Qed.

Lemma gsn_1RB1RC_1LC0RD_1LA1LB_0LC1RD : forall v i q0, cview v = (i, Some q0) ->
  Cin v = cden (Jp q0 ++ [S1;S0;S1]) [] i AI0_1RB1RC_1LC0RD_1LA1LB_0LC1RD.
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (H1 & _).
  unfold Cin_1RB1RC_1LC0RD_1LA1LB_0LC1RD, cden, AI0_1RB1RC_1LC0RD_1LA1LB_0LC1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen_1RB1RC_1LC0RD_1LA1LB_0LC1RD : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Jp q0 ++ [S1;S0;S1]) [] i AI1_1RB1RC_1LC0RD_1LA1LB_0LC1RD) = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (_ & H2).
  unfold Cin_1RB1RC_1LC0RD_1LA1LB_0LC1RD, cden, AI1_1RB1RC_1LC0RD_1LA1LB_0LC1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin_1RB1RC_1LC0RD_1LA1LB_0LC1RD : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 4), (cden (Jp q0 ++ [S1;S0;S1]) [] i AI1_1RB1RC_1LC0RD_1LA1LB_0LC1RD).
  split; [lia|]. split; [| exact (gen_1RB1RC_1LC0RD_1LA1LB_0LC1RD v i q0 E)].
  rewrite (gsn_1RB1RC_1LC0RD_1LA1LB_0LC1RD v i q0 E).
  exact (srun_sound tm false true chn_1RB1RC_1LC0RD_1LA1LB_0LC1RD AI0_1RB1RC_1LC0RD_1LA1LB_0LC1RD AI1_1RB1RC_1LC0RD_1LA1LB_0LC1RD 4 4
           run_inner_1RB1RC_1LC0RD_1LA1LB_0LC1RD (Jp q0 ++ [S1;S0;S1]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The chain into this family lands on its anchor up to 0/0
    trailing blanks. *)
Lemma gbo_1RB1RC_1LC0RD_1LA1LB_0LC1RD : forall j, lift (cden [] [] j BB1_1RB1RC_1LC0RD_1LA1LB_0LC1RD) = lift (Cin (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_1RB1RC_1LC0RD_1LA1LB_0LC1RD = (StD, (rep [S1;S1] j ++ [S1;S1;S0;S1], S0, []))).
  { unfold cden, BB1_1RB1RC_1LC0RD_1LA1LB_0LC1RD, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin (pow2 j) = (StD, (rep [S1;S1] j ++ [S1;S1;S0;S1], S0, []))).
  { unfold Cin_1RB1RC_1LC0RD_1LA1LB_0LC1RD. rewrite epow2_1RB1RC_1LC0RD_1LA1LB_0LC1RD.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_1RB1RC_1LC0RD_1LA1LB_0LC1RD. rewrite ?lift_app_blank. reflexivity.
Qed.

(** This family's all-ones fill IS the next chain's start.  [cview (fill
    (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    family's own overflow decomposition names the word. *)
Lemma gxi_1RB1RC_1LC0RD_1LA1LB_0LC1RD : forall j, Cin (fill (pow2 j)) = cden [] [] j BM0_1RB1RC_1LC0RD_1LA1LB_0LC1RD.
Proof.
  intro j.
  destruct (JpCounter.cview_none_J (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin_1RB1RC_1LC0RD_1LA1LB_0LC1RD, cden, BM0_1RB1RC_1LC0RD_1LA1LB_0LC1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

Lemma gsn2_1RB1RC_1LC0RD_1LA1LB_0LC1RD : forall v i q0, cview v = (i, Some q0) ->
  Cin2 v = cden (Jp q0 ++ [S0;S0;S1]) [] i AI20_1RB1RC_1LC0RD_1LA1LB_0LC1RD.
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (H1 & _).
  unfold Cin2_1RB1RC_1LC0RD_1LA1LB_0LC1RD, cden, AI20_1RB1RC_1LC0RD_1LA1LB_0LC1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen2_1RB1RC_1LC0RD_1LA1LB_0LC1RD : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Jp q0 ++ [S0;S0;S1]) [] i AI21_1RB1RC_1LC0RD_1LA1LB_0LC1RD) = lift (Cin2 (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (_ & H2).
  unfold Cin2_1RB1RC_1LC0RD_1LA1LB_0LC1RD, cden, AI21_1RB1RC_1LC0RD_1LA1LB_0LC1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin2_1RB1RC_1LC0RD_1LA1LB_0LC1RD : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin2 v) = Some c'
               /\ lift c' = lift (Cin2 (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 4), (cden (Jp q0 ++ [S0;S0;S1]) [] i AI21_1RB1RC_1LC0RD_1LA1LB_0LC1RD).
  split; [lia|]. split; [| exact (gen2_1RB1RC_1LC0RD_1LA1LB_0LC1RD v i q0 E)].
  rewrite (gsn2_1RB1RC_1LC0RD_1LA1LB_0LC1RD v i q0 E).
  exact (srun_sound tm false true chn2_1RB1RC_1LC0RD_1LA1LB_0LC1RD AI20_1RB1RC_1LC0RD_1LA1LB_0LC1RD AI21_1RB1RC_1LC0RD_1LA1LB_0LC1RD 4 4
           run_inner2_1RB1RC_1LC0RD_1LA1LB_0LC1RD (Jp q0 ++ [S0;S0;S1]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The chain into this family lands on its anchor up to 0/0
    trailing blanks. *)
Lemma gbo2_1RB1RC_1LC0RD_1LA1LB_0LC1RD : forall j, lift (cden [] [] j BM1_1RB1RC_1LC0RD_1LA1LB_0LC1RD) = lift (Cin2 (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BM1_1RB1RC_1LC0RD_1LA1LB_0LC1RD = (StD, (rep [S1;S1] j ++ [S1;S0;S0;S1], S0, []))).
  { unfold cden, BM1_1RB1RC_1LC0RD_1LA1LB_0LC1RD, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin2 (pow2 j) = (StD, (rep [S1;S1] j ++ [S1;S0;S0;S1], S0, []))).
  { unfold Cin2_1RB1RC_1LC0RD_1LA1LB_0LC1RD. rewrite epow22_1RB1RC_1LC0RD_1LA1LB_0LC1RD.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_1RB1RC_1LC0RD_1LA1LB_0LC1RD. rewrite ?lift_app_blank. reflexivity.
Qed.

(** This family's all-ones fill IS the next chain's start.  [cview (fill
    (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    family's own overflow decomposition names the word. *)
Lemma gxi2_1RB1RC_1LC0RD_1LA1LB_0LC1RD : forall j, Cin2 (fill (pow2 j)) = cden [] [] j BE0_1RB1RC_1LC0RD_1LA1LB_0LC1RD.
Proof.
  intro j.
  destruct (JpCounter.cview_none_J (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin2_1RB1RC_1LC0RD_1LA1LB_0LC1RD, cden, BE0_1RB1RC_1LC0RD_1LA1LB_0LC1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

(** The interior lap, restated up to [lift] -- what [vis_via_ovf_lift] and
    [vis_via_fill] consume. *)
Lemma lapil_1RB1RC_1LC0RD_1LA1LB_0LC1RD : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof. intros p j q0 E. destruct (lapi_1RB1RC_1LC0RD_1LA1LB_0LC1RD p j q0 E) as (n & Hn & Hr).
  exists n, (Cc (Pos.succ p)).
  split; [exact Hn | split; [exact Hr | reflexivity]]. Qed.

(** The outer OVERFLOW branch, composed.  The exponential cost is the
    [exists n] inside [inner_to_fill_lift]; no formula for it is ever
    written. *)
Lemma lapo_1RB1RC_1LC0RD_1LA1LB_0LC1RD : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E.
  apply (nested_overflow_lift tm Cc Cin2 lapin2_1RB1RC_1LC0RD_1LA1LB_0LC1RD p (pow2 j)).
  - apply (boot_via_fill tm Cc Cin Cin2 lapin_1RB1RC_1LC0RD_1LA1LB_0LC1RD p (pow2 j) (pow2 j)).
    + exists (4 * j + 8), (cden [] [] j BB1_1RB1RC_1LC0RD_1LA1LB_0LC1RD).
      split; [lia|]. split; [| exact (gbo_1RB1RC_1LC0RD_1LA1LB_0LC1RD j)].
      rewrite (gso_1RB1RC_1LC0RD_1LA1LB_0LC1RD p j E).
      exact (srun_sound tm true true chb_1RB1RC_1LC0RD_1LA1LB_0LC1RD B0_1RB1RC_1LC0RD_1LA1LB_0LC1RD BB1_1RB1RC_1LC0RD_1LA1LB_0LC1RD 4 8
               run_boot_1RB1RC_1LC0RD_1LA1LB_0LC1RD [] [] j ltac:(reflexivity) ltac:(reflexivity)).
    + exists (4 * j + 4), (cden [] [] j BM1_1RB1RC_1LC0RD_1LA1LB_0LC1RD).
      split; [| exact (gbo2_1RB1RC_1LC0RD_1LA1LB_0LC1RD j)].
      rewrite (gxi_1RB1RC_1LC0RD_1LA1LB_0LC1RD j).
      exact (srun_sound tm true true chm_1RB1RC_1LC0RD_1LA1LB_0LC1RD BM0_1RB1RC_1LC0RD_1LA1LB_0LC1RD BM1_1RB1RC_1LC0RD_1LA1LB_0LC1RD 4 4
               run_shift_1RB1RC_1LC0RD_1LA1LB_0LC1RD [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  - exists (4 * j + 10), (cden [] [] j B1_1RB1RC_1LC0RD_1LA1LB_0LC1RD).
    split; [| exact (geo_1RB1RC_1LC0RD_1LA1LB_0LC1RD p j E)].
    rewrite (gxi2_1RB1RC_1LC0RD_1LA1LB_0LC1RD j).
    exact (srun_sound tm true true che_1RB1RC_1LC0RD_1LA1LB_0LC1RD BE0_1RB1RC_1LC0RD_1LA1LB_0LC1RD B1_1RB1RC_1LC0RD_1LA1LB_0LC1RD 4 10
             run_exit_1RB1RC_1LC0RD_1LA1LB_0LC1RD [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.



(** ** The lap *)

Lemma lap_1RB1RC_1LC0RD_1LA1LB_0LC1RD : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB1RC_1LC0RD_1LA1LB_0LC1RD p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->). exact (lapo_1RB1RC_1LC0RD_1LA1LB_0LC1RD p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_1RB1RC_1LC0RD_1LA1LB_0LC1RD : exists t0, stepn tm t0 InitES = Some (lift (Cc 6)).
Proof.
  exists 10.
  assert (H : match csteps tm 10 c0 with
              | Some c => ceqb c (Cc 6) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 10 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma viso_1RB1RC_1LC0RD_1LA1LB_0LC1RD : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_1RB1RC_1LC0RD_1LA1LB_0LC1RD = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_1RB1RC_1LC0RD_1LA1LB_0LC1RD p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB1RC_1LC0RD_1LA1LB_0LC1RD p j E)].
Qed.

Lemma vis_1RB1RC_1LC0RD_1LA1LB_0LC1RD : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_1RB1RC_1LC0RD_1LA1LB_0LC1RD.
  destruct q.

  - (* StA *)
    apply (vis_via_ovf tm Cc Hi StA), viso_1RB1RC_1LC0RD_1LA1LB_0LC1RD
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 2]).
    vm_compute; reflexivity.
  - (* StB *)
    apply (vis_via_ovf tm Cc Hi StB), viso_1RB1RC_1LC0RD_1LA1LB_0LC1RD
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1]).
    vm_compute; reflexivity.
  - (* StC *)
    apply (vis_via_ovf tm Cc Hi StC), viso_1RB1RC_1LC0RD_1LA1LB_0LC1RD
      with (l := [SRotL 1; SWin 1]).
    vm_compute; reflexivity.
  - (* StD: the anchor state *)
    exists 0. eexists. split; reflexivity.
Qed.

Theorem nqh_1RB1RC_1LC0RD_1LA1LB_0LC1RD : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 6). - exact boot_1RB1RC_1LC0RD_1LA1LB_0LC1RD. - intros p _. apply lap_1RB1RC_1LC0RD_1LA1LB_0LC1RD. - intros p q _. apply vis_1RB1RC_1LC0RD_1LA1LB_0LC1RD. Qed.

Theorem nonhalt_1RB1RC_1LC0RD_1LA1LB_0LC1RD : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_1RB1RC_1LC0RD_1LA1LB_0LC1RD. Qed.
