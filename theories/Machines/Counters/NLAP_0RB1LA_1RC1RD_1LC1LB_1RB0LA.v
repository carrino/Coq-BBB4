(** * NLAP_0RB1LA_1RC1RD_1LC1LB_1RB0LA: machine 0RB1LA_1RC1RD_1LC1LB_1RB0LA, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Jp digit alphabet (JpCounter.v), anchored at

      Cc p = (StA, (Jp p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  4*j+4 steps
      overflow  (cview p = (S j, None)):   boot 4*j+10, then the inner counter's own laps to the
                                           all-ones fill, then exit 4*j+10

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 192 interior anchors (interior); 6 overflow phases, j = 2..7 (492 inner laps, two counts each) (nested overflow).
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter JpCounter LapCertGlue LapCertGlueLift IXPGadgets NestedLap NestedLapLift NestedLap2.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_0RB1LA_1RC1RD_1LC1LB_1RB0LA (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB1LA_1RC1RD_1LC1LB_1RB0LA.

(** 0RB1LA_1RC1RD_1LC1LB_1RB0LA *)
(** 0RB1LA_1RC1RD_1LC1LB_1RB0LA -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB1LA_1RC1RD_1LC1LB_1RB0LA : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S1 DL StA
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S1 DL StC | StC, S1 => mk S1 DL StB
  | StD, S0 => mk S1 DR StB | StD, S1 => mk S0 DL StA end.

(** Its mirror 0LB1RA_1LC1LD_1RC1RB_1LB0RA: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB1LA_1RC1RD_1LC1LB_1RB0LA : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S1 DR StA
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DL StD
  | StC, S0 => mk S1 DR StC | StC, S1 => mk S1 DR StB
  | StD, S0 => mk S1 DL StB | StD, S1 => mk S0 DR StA end.
Local Notation tm := tmm_0RB1LA_1RC1RD_1LC1LB_1RB0LA.

Lemma mirror_ok_0RB1LA_1RC1RD_1LC1LB_1RB0LA : mirror_tm tm_0RB1LA_1RC1RD_1LC1LB_1RB0LA = tmm_0RB1LA_1RC1RD_1LC1LB_1RB0LA.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_0RB1LA_1RC1RD_1LC1LB_1RB0LA (p : positive) : cconf := (StA, (Jp p ++ [S0], S0, [])).
Local Notation Cc := Cc_0RB1LA_1RC1RD_1LC1LB_1RB0LA.

(** ** The certificate *)

Definition A0_0RB1LA_1RC1RD_1LC1LB_1RB0LA : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition A1_0RB1LA_1RC1RD_1LC1LB_1RB0LA : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chi_0RB1LA_1RC1RD_1LC1LB_1RB0LA : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_int_0RB1LA_1RC1RD_1LC1LB_1RB0LA : srun tm false true chi_0RB1LA_1RC1RD_1LC1LB_1RB0LA A0_0RB1LA_1RC1RD_1LC1LB_1RB0LA = Some (A1_0RB1LA_1RC1RD_1LC1LB_1RB0LA, 4, 4).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB1LA_1RC1RD_1LC1LB_1RB0LA : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_0RB1LA_1RC1RD_1LC1LB_1RB0LA : sconf := mkC StA (mkS [] [S1;S1] 1 1 [S1;S0]) S0 (mkS [] [] 0 0 []).
(** ** The FIRST INNER anchor family -- Jp at StA *)
Definition Cin_0RB1LA_1RC1RD_1LC1LB_1RB0LA (v : positive) : cconf := (StA, (Jp v ++ [S1;S0;S1], S0, [])).
Local Notation Cin := Cin_0RB1LA_1RC1RD_1LC1LB_1RB0LA.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow2_0RB1LA_1RC1RD_1LC1LB_1RB0LA : forall n, Jp (pow2 n) = rep [S1;S1] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap -- ordinary and affine.  Iterating it to the fill is
    where a [Theta(2^j)] lives, and [inner_to_fill_lift] keeps it inside an
    existential. *)
Definition AI0_0RB1LA_1RC1RD_1LC1LB_1RB0LA : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition AI1_0RB1LA_1RC1RD_1LC1LB_1RB0LA : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chn_0RB1LA_1RC1RD_1LC1LB_1RB0LA : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_inner_0RB1LA_1RC1RD_1LC1LB_1RB0LA : srun tm false true chn_0RB1LA_1RC1RD_1LC1LB_1RB0LA AI0_0RB1LA_1RC1RD_1LC1LB_1RB0LA = Some (AI1_0RB1LA_1RC1RD_1LC1LB_1RB0LA, 4, 4).
Proof. vm_compute. reflexivity. Qed.

(** ** The SECOND INNER anchor family -- Jp at StA *)
Definition Cin2_0RB1LA_1RC1RD_1LC1LB_1RB0LA (v : positive) : cconf := (StA, (Jp v ++ [S0;S0;S1], S0, [])).
Local Notation Cin2 := Cin2_0RB1LA_1RC1RD_1LC1LB_1RB0LA.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow22_0RB1LA_1RC1RD_1LC1LB_1RB0LA : forall n, Jp (pow2 n) = rep [S1;S1] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap -- ordinary and affine.  Iterating it to the fill is
    where a [Theta(2^j)] lives, and [inner_to_fill_lift] keeps it inside an
    existential. *)
Definition AI20_0RB1LA_1RC1RD_1LC1LB_1RB0LA : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition AI21_0RB1LA_1RC1RD_1LC1LB_1RB0LA : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chn2_0RB1LA_1RC1RD_1LC1LB_1RB0LA : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_inner2_0RB1LA_1RC1RD_1LC1LB_1RB0LA : srun tm false true chn2_0RB1LA_1RC1RD_1LC1LB_1RB0LA AI20_0RB1LA_1RC1RD_1LC1LB_1RB0LA = Some (AI21_0RB1LA_1RC1RD_1LC1LB_1RB0LA, 4, 4).
Proof. vm_compute. reflexivity. Qed.

(** *** boot: the outer overflow anchor -> the first inner anchor at [pow2 j] *)
Definition BB1_0RB1LA_1RC1RD_1LC1LB_1RB0LA : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S1;S0;S1]) S0 (mkS [] [] 0 0 []).
Definition chb_0RB1LA_1RC1RD_1LC1LB_1RB0LA : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 7; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_boot_0RB1LA_1RC1RD_1LC1LB_1RB0LA : srun tm true true chb_0RB1LA_1RC1RD_1LC1LB_1RB0LA B0_0RB1LA_1RC1RD_1LC1LB_1RB0LA = Some (BB1_0RB1LA_1RC1RD_1LC1LB_1RB0LA, 4, 10).
Proof. vm_compute. reflexivity. Qed.

(** *** shift: the FIRST count's all-ones fill -> the SECOND count's anchor.
    WAVE18 section 4c -- "count 8->15, shift, count 8->15 again". *)
Definition BM0_0RB1LA_1RC1RD_1LC1LB_1RB0LA : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1;S0;S1]) S0 (mkS [] [] 0 0 []).
Definition BM1_0RB1LA_1RC1RD_1LC1LB_1RB0LA : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0;S0;S1]) S0 (mkS [] [] 0 0 []).
Definition chm_0RB1LA_1RC1RD_1LC1LB_1RB0LA : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_shift_0RB1LA_1RC1RD_1LC1LB_1RB0LA : srun tm true true chm_0RB1LA_1RC1RD_1LC1LB_1RB0LA BM0_0RB1LA_1RC1RD_1LC1LB_1RB0LA = Some (BM1_0RB1LA_1RC1RD_1LC1LB_1RB0LA, 4, 4).
Proof. vm_compute. reflexivity. Qed.

(** *** exit: the last inner all-ones fill -> the outer successor *)
Definition BE0_0RB1LA_1RC1RD_1LC1LB_1RB0LA : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S0;S0;S1]) S0 (mkS [] [] 0 0 []).
Definition che_0RB1LA_1RC1RD_1LC1LB_1RB0LA : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 8; SCycR 2; SWin 1; SRotL 1; SFoldL 1].

Lemma run_exit_0RB1LA_1RC1RD_1LC1LB_1RB0LA : srun tm true true che_0RB1LA_1RC1RD_1LC1LB_1RB0LA BE0_0RB1LA_1RC1RD_1LC1LB_1RB0LA = Some (B1_0RB1LA_1RC1RD_1LC1LB_1RB0LA, 4, 10).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_0RB1LA_1RC1RD_1LC1LB_1RB0LA : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Jp q0 ++ [S0]) [] j A0_0RB1LA_1RC1RD_1LC1LB_1RB0LA.
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (H1 & _).
  unfold Cc_0RB1LA_1RC1RD_1LC1LB_1RB0LA, cden, A0_0RB1LA_1RC1RD_1LC1LB_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gei_0RB1LA_1RC1RD_1LC1LB_1RB0LA : forall p j q0, cview p = (j, Some q0) ->
  cden (Jp q0 ++ [S0]) [] j A1_0RB1LA_1RC1RD_1LC1LB_1RB0LA = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (_ & H2).
  unfold Cc_0RB1LA_1RC1RD_1LC1LB_1RB0LA, cden, A1_0RB1LA_1RC1RD_1LC1LB_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_0RB1LA_1RC1RD_1LC1LB_1RB0LA : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (4 * j + 4). split; [lia|].
  rewrite (gsi_0RB1LA_1RC1RD_1LC1LB_1RB0LA p j q0 E).
  rewrite (srun_sound tm false true chi_0RB1LA_1RC1RD_1LC1LB_1RB0LA A0_0RB1LA_1RC1RD_1LC1LB_1RB0LA A1_0RB1LA_1RC1RD_1LC1LB_1RB0LA 4 4
             run_int_0RB1LA_1RC1RD_1LC1LB_1RB0LA (Jp q0 ++ [S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_0RB1LA_1RC1RD_1LC1LB_1RB0LA p j q0 E).
Qed.

Lemma gso_0RB1LA_1RC1RD_1LC1LB_1RB0LA : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_0RB1LA_1RC1RD_1LC1LB_1RB0LA.
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (H1 & _).
  unfold Cc_0RB1LA_1RC1RD_1LC1LB_1RB0LA, cden, B0_0RB1LA_1RC1RD_1LC1LB_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_0RB1LA_1RC1RD_1LC1LB_1RB0LA : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_0RB1LA_1RC1RD_1LC1LB_1RB0LA : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB1LA_1RC1RD_1LC1LB_1RB0LA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_0RB1LA_1RC1RD_1LC1LB_1RB0LA
             = (StA, (rep [S1;S1] (S j) ++ [S1;S0], S0, []))).
  { unfold cden, B1_0RB1LA_1RC1RD_1LC1LB_1RB0LA, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StA, (rep [S1;S1] (S j) ++ [S1;S0], S0, []))).
  { unfold Cc_0RB1LA_1RC1RD_1LC1LB_1RB0LA. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. reflexivity.
Qed.

Lemma gsn_0RB1LA_1RC1RD_1LC1LB_1RB0LA : forall v i q0, cview v = (i, Some q0) ->
  Cin v = cden (Jp q0 ++ [S1;S0;S1]) [] i AI0_0RB1LA_1RC1RD_1LC1LB_1RB0LA.
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (H1 & _).
  unfold Cin_0RB1LA_1RC1RD_1LC1LB_1RB0LA, cden, AI0_0RB1LA_1RC1RD_1LC1LB_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen_0RB1LA_1RC1RD_1LC1LB_1RB0LA : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Jp q0 ++ [S1;S0;S1]) [] i AI1_0RB1LA_1RC1RD_1LC1LB_1RB0LA) = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (_ & H2).
  unfold Cin_0RB1LA_1RC1RD_1LC1LB_1RB0LA, cden, AI1_0RB1LA_1RC1RD_1LC1LB_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin_0RB1LA_1RC1RD_1LC1LB_1RB0LA : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 4), (cden (Jp q0 ++ [S1;S0;S1]) [] i AI1_0RB1LA_1RC1RD_1LC1LB_1RB0LA).
  split; [lia|]. split; [| exact (gen_0RB1LA_1RC1RD_1LC1LB_1RB0LA v i q0 E)].
  rewrite (gsn_0RB1LA_1RC1RD_1LC1LB_1RB0LA v i q0 E).
  exact (srun_sound tm false true chn_0RB1LA_1RC1RD_1LC1LB_1RB0LA AI0_0RB1LA_1RC1RD_1LC1LB_1RB0LA AI1_0RB1LA_1RC1RD_1LC1LB_1RB0LA 4 4
           run_inner_0RB1LA_1RC1RD_1LC1LB_1RB0LA (Jp q0 ++ [S1;S0;S1]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The chain into this family lands on its anchor up to 0/0
    trailing blanks. *)
Lemma gbo_0RB1LA_1RC1RD_1LC1LB_1RB0LA : forall j, lift (cden [] [] j BB1_0RB1LA_1RC1RD_1LC1LB_1RB0LA) = lift (Cin (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_0RB1LA_1RC1RD_1LC1LB_1RB0LA = (StA, (rep [S1;S1] j ++ [S1;S1;S0;S1], S0, []))).
  { unfold cden, BB1_0RB1LA_1RC1RD_1LC1LB_1RB0LA, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin (pow2 j) = (StA, (rep [S1;S1] j ++ [S1;S1;S0;S1], S0, []))).
  { unfold Cin_0RB1LA_1RC1RD_1LC1LB_1RB0LA. rewrite epow2_0RB1LA_1RC1RD_1LC1LB_1RB0LA.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_0RB1LA_1RC1RD_1LC1LB_1RB0LA. rewrite ?lift_app_blank. reflexivity.
Qed.

(** This family's all-ones fill IS the next chain's start.  [cview (fill
    (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    family's own overflow decomposition names the word. *)
Lemma gxi_0RB1LA_1RC1RD_1LC1LB_1RB0LA : forall j, Cin (fill (pow2 j)) = cden [] [] j BM0_0RB1LA_1RC1RD_1LC1LB_1RB0LA.
Proof.
  intro j.
  destruct (JpCounter.cview_none_J (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin_0RB1LA_1RC1RD_1LC1LB_1RB0LA, cden, BM0_0RB1LA_1RC1RD_1LC1LB_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

Lemma gsn2_0RB1LA_1RC1RD_1LC1LB_1RB0LA : forall v i q0, cview v = (i, Some q0) ->
  Cin2 v = cden (Jp q0 ++ [S0;S0;S1]) [] i AI20_0RB1LA_1RC1RD_1LC1LB_1RB0LA.
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (H1 & _).
  unfold Cin2_0RB1LA_1RC1RD_1LC1LB_1RB0LA, cden, AI20_0RB1LA_1RC1RD_1LC1LB_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen2_0RB1LA_1RC1RD_1LC1LB_1RB0LA : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Jp q0 ++ [S0;S0;S1]) [] i AI21_0RB1LA_1RC1RD_1LC1LB_1RB0LA) = lift (Cin2 (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (_ & H2).
  unfold Cin2_0RB1LA_1RC1RD_1LC1LB_1RB0LA, cden, AI21_0RB1LA_1RC1RD_1LC1LB_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin2_0RB1LA_1RC1RD_1LC1LB_1RB0LA : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin2 v) = Some c'
               /\ lift c' = lift (Cin2 (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 4), (cden (Jp q0 ++ [S0;S0;S1]) [] i AI21_0RB1LA_1RC1RD_1LC1LB_1RB0LA).
  split; [lia|]. split; [| exact (gen2_0RB1LA_1RC1RD_1LC1LB_1RB0LA v i q0 E)].
  rewrite (gsn2_0RB1LA_1RC1RD_1LC1LB_1RB0LA v i q0 E).
  exact (srun_sound tm false true chn2_0RB1LA_1RC1RD_1LC1LB_1RB0LA AI20_0RB1LA_1RC1RD_1LC1LB_1RB0LA AI21_0RB1LA_1RC1RD_1LC1LB_1RB0LA 4 4
           run_inner2_0RB1LA_1RC1RD_1LC1LB_1RB0LA (Jp q0 ++ [S0;S0;S1]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The chain into this family lands on its anchor up to 0/0
    trailing blanks. *)
Lemma gbo2_0RB1LA_1RC1RD_1LC1LB_1RB0LA : forall j, lift (cden [] [] j BM1_0RB1LA_1RC1RD_1LC1LB_1RB0LA) = lift (Cin2 (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BM1_0RB1LA_1RC1RD_1LC1LB_1RB0LA = (StA, (rep [S1;S1] j ++ [S1;S0;S0;S1], S0, []))).
  { unfold cden, BM1_0RB1LA_1RC1RD_1LC1LB_1RB0LA, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin2 (pow2 j) = (StA, (rep [S1;S1] j ++ [S1;S0;S0;S1], S0, []))).
  { unfold Cin2_0RB1LA_1RC1RD_1LC1LB_1RB0LA. rewrite epow22_0RB1LA_1RC1RD_1LC1LB_1RB0LA.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_0RB1LA_1RC1RD_1LC1LB_1RB0LA. rewrite ?lift_app_blank. reflexivity.
Qed.

(** This family's all-ones fill IS the next chain's start.  [cview (fill
    (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    family's own overflow decomposition names the word. *)
Lemma gxi2_0RB1LA_1RC1RD_1LC1LB_1RB0LA : forall j, Cin2 (fill (pow2 j)) = cden [] [] j BE0_0RB1LA_1RC1RD_1LC1LB_1RB0LA.
Proof.
  intro j.
  destruct (JpCounter.cview_none_J (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin2_0RB1LA_1RC1RD_1LC1LB_1RB0LA, cden, BE0_0RB1LA_1RC1RD_1LC1LB_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

(** The interior lap, restated up to [lift] -- what [vis_via_ovf_lift] and
    [vis_via_fill] consume. *)
Lemma lapil_0RB1LA_1RC1RD_1LC1LB_1RB0LA : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof. intros p j q0 E. destruct (lapi_0RB1LA_1RC1RD_1LC1LB_1RB0LA p j q0 E) as (n & Hn & Hr).
  exists n, (Cc (Pos.succ p)).
  split; [exact Hn | split; [exact Hr | reflexivity]]. Qed.

(** The outer OVERFLOW branch, composed.  The exponential cost is the
    [exists n] inside [inner_to_fill_lift]; no formula for it is ever
    written. *)
Lemma lapo_0RB1LA_1RC1RD_1LC1LB_1RB0LA : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E.
  apply (nested_overflow_lift tm Cc Cin2 lapin2_0RB1LA_1RC1RD_1LC1LB_1RB0LA p (pow2 j)).
  - apply (boot_via_fill tm Cc Cin Cin2 lapin_0RB1LA_1RC1RD_1LC1LB_1RB0LA p (pow2 j) (pow2 j)).
    + exists (4 * j + 10), (cden [] [] j BB1_0RB1LA_1RC1RD_1LC1LB_1RB0LA).
      split; [lia|]. split; [| exact (gbo_0RB1LA_1RC1RD_1LC1LB_1RB0LA j)].
      rewrite (gso_0RB1LA_1RC1RD_1LC1LB_1RB0LA p j E).
      exact (srun_sound tm true true chb_0RB1LA_1RC1RD_1LC1LB_1RB0LA B0_0RB1LA_1RC1RD_1LC1LB_1RB0LA BB1_0RB1LA_1RC1RD_1LC1LB_1RB0LA 4 10
               run_boot_0RB1LA_1RC1RD_1LC1LB_1RB0LA [] [] j ltac:(reflexivity) ltac:(reflexivity)).
    + exists (4 * j + 4), (cden [] [] j BM1_0RB1LA_1RC1RD_1LC1LB_1RB0LA).
      split; [| exact (gbo2_0RB1LA_1RC1RD_1LC1LB_1RB0LA j)].
      rewrite (gxi_0RB1LA_1RC1RD_1LC1LB_1RB0LA j).
      exact (srun_sound tm true true chm_0RB1LA_1RC1RD_1LC1LB_1RB0LA BM0_0RB1LA_1RC1RD_1LC1LB_1RB0LA BM1_0RB1LA_1RC1RD_1LC1LB_1RB0LA 4 4
               run_shift_0RB1LA_1RC1RD_1LC1LB_1RB0LA [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  - exists (4 * j + 10), (cden [] [] j B1_0RB1LA_1RC1RD_1LC1LB_1RB0LA).
    split; [| exact (geo_0RB1LA_1RC1RD_1LC1LB_1RB0LA p j E)].
    rewrite (gxi2_0RB1LA_1RC1RD_1LC1LB_1RB0LA j).
    exact (srun_sound tm true true che_0RB1LA_1RC1RD_1LC1LB_1RB0LA BE0_0RB1LA_1RC1RD_1LC1LB_1RB0LA B1_0RB1LA_1RC1RD_1LC1LB_1RB0LA 4 10
             run_exit_0RB1LA_1RC1RD_1LC1LB_1RB0LA [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.



(** ** The lap *)

Lemma lap_0RB1LA_1RC1RD_1LC1LB_1RB0LA : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB1LA_1RC1RD_1LC1LB_1RB0LA p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->). exact (lapo_0RB1LA_1RC1RD_1LC1LB_1RB0LA p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_0RB1LA_1RC1RD_1LC1LB_1RB0LA : exists t0, stepn tm t0 InitES = Some (lift (Cc 3)).
Proof.
  exists 9.
  assert (H : match csteps tm 9 c0 with
              | Some c => ceqb c (Cc 3) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 9 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma viso_0RB1LA_1RC1RD_1LC1LB_1RB0LA : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_0RB1LA_1RC1RD_1LC1LB_1RB0LA = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_0RB1LA_1RC1RD_1LC1LB_1RB0LA p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB1LA_1RC1RD_1LC1LB_1RB0LA p j E)].
Qed.

Lemma vis_0RB1LA_1RC1RD_1LC1LB_1RB0LA : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_0RB1LA_1RC1RD_1LC1LB_1RB0LA.
  destruct q.

  - (* StA: the anchor state *)
    exists 0. eexists. split; reflexivity.
  - (* StB *)
    apply (vis_via_ovf tm Cc Hi StB), viso_0RB1LA_1RC1RD_1LC1LB_1RB0LA
      with (l := [SRotL 1; SWin 1]).
    vm_compute; reflexivity.
  - (* StC *)
    apply (vis_via_ovf tm Cc Hi StC), viso_0RB1LA_1RC1RD_1LC1LB_1RB0LA
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 2]).
    vm_compute; reflexivity.
  - (* StD *)
    apply (vis_via_ovf tm Cc Hi StD), viso_0RB1LA_1RC1RD_1LC1LB_1RB0LA
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1]).
    vm_compute; reflexivity.
Qed.

Theorem nqhm_0RB1LA_1RC1RD_1LC1LB_1RB0LA : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 3). - exact boot_0RB1LA_1RC1RD_1LC1LB_1RB0LA. - intros p _. apply lap_0RB1LA_1RC1RD_1LC1LB_1RB0LA. - intros p q _. apply vis_0RB1LA_1RC1RD_1LC1LB_1RB0LA. Qed.

Theorem nqh_0RB1LA_1RC1RD_1LC1LB_1RB0LA : NeverQuasiHaltsSt tm_0RB1LA_1RC1RD_1LC1LB_1RB0LA.
Proof. apply (mirror_never_qh tm_0RB1LA_1RC1RD_1LC1LB_1RB0LA). rewrite mirror_ok_0RB1LA_1RC1RD_1LC1LB_1RB0LA. exact nqhm_0RB1LA_1RC1RD_1LC1LB_1RB0LA. Qed.

Theorem nonhalt_0RB1LA_1RC1RD_1LC1LB_1RB0LA : NonHalt tm_0RB1LA_1RC1RD_1LC1LB_1RB0LA.
Proof. apply never_qh_nonhalt, nqh_0RB1LA_1RC1RD_1LC1LB_1RB0LA. Qed.
