(** * LAPT_0RB1RD_1LC0RA_1RC1LB_0LC1RA: TRANSITION-LEVEL board for machine 0RB1RD_1LC0RA_1RC1LB_0LC1RA, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Jp digit alphabet (JpCounter.v), anchored at

      Cc p = (StD, (Jp p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  4*j+4 steps
      overflow  (cview p = (S j, None)):   boot 4*j+16, then the inner counter's own laps to the
                                           all-ones fill, then exit 4*j+6

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
From BBB4 Require Import BBBT4_Statement.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
Import ListNotations.

Definition mk_0RB1RD_1LC0RA_1RC1LB_0LC1RA (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB1RD_1LC0RA_1RC1LB_0LC1RA.

(** 0RB1RD_1LC0RA_1RC1LB_0LC1RA *)
Definition tm_0RB1RD_1LC0RA_1RC1LB_0LC1RA : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S1 DR StD
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DR StA
  | StC, S0 => mk S1 DR StC | StC, S1 => mk S1 DL StB
  | StD, S0 => mk S0 DL StC | StD, S1 => mk S1 DR StA end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_0RB1RD_1LC0RA_1RC1LB_0LC1RA : list Instr := [].
Definition tmw_0RB1RD_1LC0RA_1RC1LB_0LC1RA : TM := tm_wrap_trs tm_0RB1RD_1LC0RA_1RC1LB_0LC1RA pins_0RB1RD_1LC0RA_1RC1LB_0LC1RA.
Local Notation tm := tmw_0RB1RD_1LC0RA_1RC1LB_0LC1RA.

Definition Cc_0RB1RD_1LC0RA_1RC1LB_0LC1RA (p : positive) : cconf := (StD, (Jp p ++ [S0], S0, [])).
Local Notation Cc := Cc_0RB1RD_1LC0RA_1RC1LB_0LC1RA.

(** ** The certificate *)

Definition A0_0RB1RD_1LC0RA_1RC1LB_0LC1RA : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition A1_0RB1RD_1LC0RA_1RC1LB_0LC1RA : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chi_0RB1RD_1LC0RA_1RC1LB_0LC1RA : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_int_0RB1RD_1LC0RA_1RC1LB_0LC1RA : srun tm false true chi_0RB1RD_1LC0RA_1RC1LB_0LC1RA A0_0RB1RD_1LC0RA_1RC1LB_0LC1RA = Some (A1_0RB1RD_1LC0RA_1RC1LB_0LC1RA, 4, 4).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB1RD_1LC0RA_1RC1LB_0LC1RA : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_0RB1RD_1LC0RA_1RC1LB_0LC1RA : sconf := mkC StD (mkS [] [S1;S1] 1 1 [S1;S0]) S0 (mkS [] [] 0 0 []).
(** ** The INNER anchor family -- Jp at StB *)
Definition Cin_0RB1RD_1LC0RA_1RC1LB_0LC1RA (v : positive) : cconf := (StB, (Jp v ++ [S1], S0, [S1])).
Local Notation Cin := Cin_0RB1RD_1LC0RA_1RC1LB_0LC1RA.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow2_0RB1RD_1LC0RA_1RC1LB_0LC1RA : forall n, Jp (pow2 n) = rep [S1;S1] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap -- ordinary and affine.  Iterating it to the fill is
    where a [Theta(2^j)] lives, and [inner_to_fill_lift] keeps it inside an
    existential. *)
Definition AI0_0RB1RD_1LC0RA_1RC1LB_0LC1RA : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition AI1_0RB1RD_1LC0RA_1RC1LB_0LC1RA : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S1;S0] [] 0 0 []).
Definition chn_0RB1RD_1LC0RA_1RC1LB_0LC1RA : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWin 1; SWinR 7].

Lemma run_inner_0RB1RD_1LC0RA_1RC1LB_0LC1RA : srun tm false true chn_0RB1RD_1LC0RA_1RC1LB_0LC1RA AI0_0RB1RD_1LC0RA_1RC1LB_0LC1RA = Some (AI1_0RB1RD_1LC0RA_1RC1LB_0LC1RA, 4, 12).
Proof. vm_compute. reflexivity. Qed.

(** *** boot: the outer overflow anchor -> the first inner anchor at [pow2 j] *)
Definition BB1_0RB1RD_1LC0RA_1RC1LB_0LC1RA : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S1;S0]) S0 (mkS [S1;S0] [] 0 0 []).
Definition chb_0RB1RD_1LC0RA_1RC1LB_0LC1RA : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 5; SCycR 2; SWin 1; SWinR 8; SUnrotL 1].

Lemma run_boot_0RB1RD_1LC0RA_1RC1LB_0LC1RA : srun tm true true chb_0RB1RD_1LC0RA_1RC1LB_0LC1RA B0_0RB1RD_1LC0RA_1RC1LB_0LC1RA = Some (BB1_0RB1RD_1LC0RA_1RC1LB_0LC1RA, 4, 16).
Proof. vm_compute. reflexivity. Qed.

(** *** exit: the last inner all-ones fill -> the outer successor *)
Definition BE0_0RB1RD_1LC0RA_1RC1LB_0LC1RA : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition che_0RB1RD_1LC0RA_1RC1LB_0LC1RA : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWin 1; SWinR 1; SFoldL 1].

Lemma run_exit_0RB1RD_1LC0RA_1RC1LB_0LC1RA : srun tm true true che_0RB1RD_1LC0RA_1RC1LB_0LC1RA BE0_0RB1RD_1LC0RA_1RC1LB_0LC1RA = Some (B1_0RB1RD_1LC0RA_1RC1LB_0LC1RA, 4, 6).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_0RB1RD_1LC0RA_1RC1LB_0LC1RA : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Jp q0 ++ [S0]) [] j A0_0RB1RD_1LC0RA_1RC1LB_0LC1RA.
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (H1 & _).
  unfold Cc_0RB1RD_1LC0RA_1RC1LB_0LC1RA, cden, A0_0RB1RD_1LC0RA_1RC1LB_0LC1RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gei_0RB1RD_1LC0RA_1RC1LB_0LC1RA : forall p j q0, cview p = (j, Some q0) ->
  cden (Jp q0 ++ [S0]) [] j A1_0RB1RD_1LC0RA_1RC1LB_0LC1RA = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (_ & H2).
  unfold Cc_0RB1RD_1LC0RA_1RC1LB_0LC1RA, cden, A1_0RB1RD_1LC0RA_1RC1LB_0LC1RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_0RB1RD_1LC0RA_1RC1LB_0LC1RA : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (4 * j + 4). split; [lia|].
  rewrite (gsi_0RB1RD_1LC0RA_1RC1LB_0LC1RA p j q0 E).
  rewrite (srun_sound tm false true chi_0RB1RD_1LC0RA_1RC1LB_0LC1RA A0_0RB1RD_1LC0RA_1RC1LB_0LC1RA A1_0RB1RD_1LC0RA_1RC1LB_0LC1RA 4 4
             run_int_0RB1RD_1LC0RA_1RC1LB_0LC1RA (Jp q0 ++ [S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_0RB1RD_1LC0RA_1RC1LB_0LC1RA p j q0 E).
Qed.

Lemma gso_0RB1RD_1LC0RA_1RC1LB_0LC1RA : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_0RB1RD_1LC0RA_1RC1LB_0LC1RA.
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (H1 & _).
  unfold Cc_0RB1RD_1LC0RA_1RC1LB_0LC1RA, cden, B0_0RB1RD_1LC0RA_1RC1LB_0LC1RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_0RB1RD_1LC0RA_1RC1LB_0LC1RA : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_0RB1RD_1LC0RA_1RC1LB_0LC1RA : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB1RD_1LC0RA_1RC1LB_0LC1RA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_0RB1RD_1LC0RA_1RC1LB_0LC1RA
             = (StD, (rep [S1;S1] (S j) ++ [S1;S0], S0, []))).
  { unfold cden, B1_0RB1RD_1LC0RA_1RC1LB_0LC1RA, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StD, (rep [S1;S1] (S j) ++ [S1;S0], S0, []))).
  { unfold Cc_0RB1RD_1LC0RA_1RC1LB_0LC1RA. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. reflexivity.
Qed.

Lemma gsn_0RB1RD_1LC0RA_1RC1LB_0LC1RA : forall v i q0, cview v = (i, Some q0) ->
  Cin v = cden (Jp q0 ++ [S1]) [] i AI0_0RB1RD_1LC0RA_1RC1LB_0LC1RA.
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (H1 & _).
  unfold Cin_0RB1RD_1LC0RA_1RC1LB_0LC1RA, cden, AI0_0RB1RD_1LC0RA_1RC1LB_0LC1RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen_0RB1RD_1LC0RA_1RC1LB_0LC1RA : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Jp q0 ++ [S1]) [] i AI1_0RB1RD_1LC0RA_1RC1LB_0LC1RA) = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (_ & H2).
  unfold Cin_0RB1RD_1LC0RA_1RC1LB_0LC1RA, cden, AI1_0RB1RD_1LC0RA_1RC1LB_0LC1RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S1;S0]) with (([S1]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin_0RB1RD_1LC0RA_1RC1LB_0LC1RA : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 12), (cden (Jp q0 ++ [S1]) [] i AI1_0RB1RD_1LC0RA_1RC1LB_0LC1RA).
  split; [lia|]. split; [| exact (gen_0RB1RD_1LC0RA_1RC1LB_0LC1RA v i q0 E)].
  rewrite (gsn_0RB1RD_1LC0RA_1RC1LB_0LC1RA v i q0 E).
  exact (srun_sound tm false true chn_0RB1RD_1LC0RA_1RC1LB_0LC1RA AI0_0RB1RD_1LC0RA_1RC1LB_0LC1RA AI1_0RB1RD_1LC0RA_1RC1LB_0LC1RA 4 12
           run_inner_0RB1RD_1LC0RA_1RC1LB_0LC1RA (Jp q0 ++ [S1]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The chain into this family lands on its anchor up to 1/1
    trailing blanks. *)
Lemma gbo_0RB1RD_1LC0RA_1RC1LB_0LC1RA : forall j, lift (cden [] [] j BB1_0RB1RD_1LC0RA_1RC1LB_0LC1RA) = lift (Cin (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_0RB1RD_1LC0RA_1RC1LB_0LC1RA = (StB, ((rep [S1;S1] j ++ [S1;S1]) ++ [S0], S0, ([S1]) ++ [S0]))).
  { unfold cden, BB1_0RB1RD_1LC0RA_1RC1LB_0LC1RA, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin (pow2 j) = (StB, (rep [S1;S1] j ++ [S1;S1], S0, [S1]))).
  { unfold Cin_0RB1RD_1LC0RA_1RC1LB_0LC1RA. rewrite epow2_0RB1RD_1LC0RA_1RC1LB_0LC1RA.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_0RB1RD_1LC0RA_1RC1LB_0LC1RA. rewrite ?lift_app_blank. reflexivity.
Qed.

(** This family's all-ones fill IS the next chain's start.  [cview (fill
    (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    family's own overflow decomposition names the word. *)
Lemma gxi_0RB1RD_1LC0RA_1RC1LB_0LC1RA : forall j, Cin (fill (pow2 j)) = cden [] [] j BE0_0RB1RD_1LC0RA_1RC1LB_0LC1RA.
Proof.
  intro j.
  destruct (JpCounter.cview_none_J (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin_0RB1RD_1LC0RA_1RC1LB_0LC1RA, cden, BE0_0RB1RD_1LC0RA_1RC1LB_0LC1RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

(** The interior lap, restated up to [lift] -- what [vis_via_ovf_lift] and
    [vis_via_fill] consume. *)
Lemma lapil_0RB1RD_1LC0RA_1RC1LB_0LC1RA : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof. intros p j q0 E. destruct (lapi_0RB1RD_1LC0RA_1RC1LB_0LC1RA p j q0 E) as (n & Hn & Hr).
  exists n, (Cc (Pos.succ p)).
  split; [exact Hn | split; [exact Hr | reflexivity]]. Qed.

(** The outer OVERFLOW branch, composed.  The exponential cost is the
    [exists n] inside [inner_to_fill_lift]; no formula for it is ever
    written. *)
Lemma lapo_0RB1RD_1LC0RA_1RC1LB_0LC1RA : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E.
  apply (nested_overflow_lift tm Cc Cin lapin_0RB1RD_1LC0RA_1RC1LB_0LC1RA p (pow2 j)).
  - exists (4 * j + 16), (cden [] [] j BB1_0RB1RD_1LC0RA_1RC1LB_0LC1RA).
    split; [lia|]. split; [| exact (gbo_0RB1RD_1LC0RA_1RC1LB_0LC1RA j)].
    rewrite (gso_0RB1RD_1LC0RA_1RC1LB_0LC1RA p j E).
    exact (srun_sound tm true true chb_0RB1RD_1LC0RA_1RC1LB_0LC1RA B0_0RB1RD_1LC0RA_1RC1LB_0LC1RA BB1_0RB1RD_1LC0RA_1RC1LB_0LC1RA 4 16
             run_boot_0RB1RD_1LC0RA_1RC1LB_0LC1RA [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  - exists (4 * j + 6), (cden [] [] j B1_0RB1RD_1LC0RA_1RC1LB_0LC1RA).
    split; [| exact (geo_0RB1RD_1LC0RA_1RC1LB_0LC1RA p j E)].
    rewrite (gxi_0RB1RD_1LC0RA_1RC1LB_0LC1RA j).
    exact (srun_sound tm true true che_0RB1RD_1LC0RA_1RC1LB_0LC1RA BE0_0RB1RD_1LC0RA_1RC1LB_0LC1RA B1_0RB1RD_1LC0RA_1RC1LB_0LC1RA 4 6
             run_exit_0RB1RD_1LC0RA_1RC1LB_0LC1RA [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.



(** ** The lap *)

Lemma lap_0RB1RD_1LC0RA_1RC1LB_0LC1RA : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB1RD_1LC0RA_1RC1LB_0LC1RA p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->). exact (lapo_0RB1RD_1LC0RA_1RC1LB_0LC1RA p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_0RB1RD_1LC0RA_1RC1LB_0LC1RA : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 6.
  assert (H : match csteps tm 6 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 6 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_0RB1RD_1LC0RA_1RC1LB_0LC1RA : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_0RB1RD_1LC0RA_1RC1LB_0LC1RA = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_0RB1RD_1LC0RA_1RC1LB_0LC1RA p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB1RD_1LC0RA_1RC1LB_0LC1RA p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_0RB1RD_1LC0RA_1RC1LB_0LC1RA : forall t, ~ In t pins_0RB1RD_1LC0RA_1RC1LB_0LC1RA ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_0RB1RD_1LC0RA_1RC1LB_0LC1RA.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_via_ovf tm Cc Hi (StA, S0)), fireo_0RB1RD_1LC0RA_1RC1LB_0LC1RA
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 5; SCycR 2; SWin 1]).
    vm_compute; reflexivity.
  - (* A1 *)
    apply (fire_via_ovf tm Cc Hi (StA, S1)), fireo_0RB1RD_1LC0RA_1RC1LB_0LC1RA
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 4]).
    vm_compute; reflexivity.
  - (* B0 *)
    apply (fire_via_ovf tm Cc Hi (StB, S0)), fireo_0RB1RD_1LC0RA_1RC1LB_0LC1RA
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1]).
    vm_compute; reflexivity.
  - (* B1 *)
    apply (fire_via_ovf tm Cc Hi (StB, S1)), fireo_0RB1RD_1LC0RA_1RC1LB_0LC1RA
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 3]).
    vm_compute; reflexivity.
  - (* C0 *)
    apply (fire_via_ovf tm Cc Hi (StC, S0)), fireo_0RB1RD_1LC0RA_1RC1LB_0LC1RA
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 1]).
    vm_compute; reflexivity.
  - (* C1 *)
    apply (fire_via_ovf tm Cc Hi (StC, S1)), fireo_0RB1RD_1LC0RA_1RC1LB_0LC1RA
      with (l := [SRotL 1; SWin 1]).
    vm_compute; reflexivity.
  - (* D0 *)
    apply (fire_via_ovf tm Cc Hi (StD, S0)), fireo_0RB1RD_1LC0RA_1RC1LB_0LC1RA
      with (l := []).
    vm_compute; reflexivity.
  - (* D1 *)
    apply (fire_via_ovf tm Cc Hi (StD, S1)), fireo_0RB1RD_1LC0RA_1RC1LB_0LC1RA
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 5]).
    vm_compute; reflexivity.
Qed.

Theorem nqhtr_0RB1RD_1LC0RA_1RC1LB_0LC1RA : NeverQuasiHaltsTr tm_0RB1RD_1LC0RA_1RC1LB_0LC1RA.
Proof.
  apply (glue_neverqhtr tm_0RB1RD_1LC0RA_1RC1LB_0LC1RA pins_0RB1RD_1LC0RA_1RC1LB_0LC1RA Cc 1).
  - exact boot_0RB1RD_1LC0RA_1RC1LB_0LC1RA.
  - intros p _. apply lap_0RB1RD_1LC0RA_1RC1LB_0LC1RA.
  - intros t Ht p _. apply fire_0RB1RD_1LC0RA_1RC1LB_0LC1RA. exact Ht.
Qed.

Theorem nonhalt_0RB1RD_1LC0RA_1RC1LB_0LC1RA : NonHalt tm_0RB1RD_1LC0RA_1RC1LB_0LC1RA.
Proof. apply never_qh_tr_nonhalt, nqhtr_0RB1RD_1LC0RA_1RC1LB_0LC1RA. Qed.
