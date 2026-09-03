(** * LAPT_1RB0LC_1RC1RA_1LD1LD_0RB1LD: TRANSITION-LEVEL board for machine 1RB0LC_1RC1RA_1LD1LD_0RB1LD, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Jp digit alphabet (JpCounter.v), anchored at

      Cc p = (StD, (Jp p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  j=0: 4 ; j=S j': 4*j'+8 steps
      overflow  (cview p = (S j, None)):   boot 4*j+14, then the inner counter's own laps to the
                                           all-ones fill, then exit 4*j+6

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

Definition mk_1RB0LC_1RC1RA_1LD1LD_0RB1LD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB0LC_1RC1RA_1LD1LD_0RB1LD.

(** 1RB0LC_1RC1RA_1LD1LD_0RB1LD *)
(** 1RB0LC_1RC1RA_1LD1LD_0RB1LD -- the real machine (its counter grows RIGHT). *)
Definition tm_1RB0LC_1RC1RA_1LD1LD_0RB1LD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StC
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DR StA
  | StC, S0 => mk S1 DL StD | StC, S1 => mk S1 DL StD
  | StD, S0 => mk S0 DR StB | StD, S1 => mk S1 DL StD end.

(** Its mirror 1LB0RC_1LC1LA_1RD1RD_0LB1RD: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_1RB0LC_1RC1RA_1LD1LD_0RB1LD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => mk S0 DR StC
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DL StA
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S1 DR StD
  | StD, S0 => mk S0 DL StB | StD, S1 => mk S1 DR StD end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_1RB0LC_1RC1RA_1LD1LD_0RB1LD : list Instr := [].
Definition tmw_1RB0LC_1RC1RA_1LD1LD_0RB1LD : TM := tm_wrap_trs tmm_1RB0LC_1RC1RA_1LD1LD_0RB1LD pins_1RB0LC_1RC1RA_1LD1LD_0RB1LD.
Local Notation tm := tmw_1RB0LC_1RC1RA_1LD1LD_0RB1LD.

Lemma mirror_ok_1RB0LC_1RC1RA_1LD1LD_0RB1LD : mirror_tm tm_1RB0LC_1RC1RA_1LD1LD_0RB1LD = tmm_1RB0LC_1RC1RA_1LD1LD_0RB1LD.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_1RB0LC_1RC1RA_1LD1LD_0RB1LD (p : positive) : cconf := (StD, (Jp p ++ [S0], S0, [])).
Local Notation Cc := Cc_1RB0LC_1RC1RA_1LD1LD_0RB1LD.

(** ** The certificate *)

(** j = 0: the repeated block is absent, so the whole lap is concrete. *)
Definition Z0_1RB0LC_1RC1RA_1LD1LD_0RB1LD : sconf := mkC StD (mkS [S1;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition Z1_1RB0LC_1RC1RA_1LD1LD_0RB1LD : sconf := mkC StD (mkS [S1;S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition chz_1RB0LC_1RC1RA_1LD1LD_0RB1LD : list lstep := [SWin 4].

Lemma run_z_1RB0LC_1RC1RA_1LD1LD_0RB1LD : srun tm false true chz_1RB0LC_1RC1RA_1LD1LD_0RB1LD Z0_1RB0LC_1RC1RA_1LD1LD_0RB1LD = Some (Z1_1RB0LC_1RC1RA_1LD1LD_0RB1LD, 0, 4).
Proof. vm_compute. reflexivity. Qed.

(** j = S j': one copy of the unit sits in the PREFIX, so the head always has
    a concrete cell to step onto. *)
Definition P0_1RB0LC_1RC1RA_1LD1LD_0RB1LD : sconf := mkC StD (mkS [S1;S0] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition P1_1RB0LC_1RC1RA_1LD1LD_0RB1LD : sconf := mkC StD (mkS [S1;S1] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chp_1RB0LC_1RC1RA_1LD1LD_0RB1LD : list lstep := [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 2].

Lemma run_p_1RB0LC_1RC1RA_1LD1LD_0RB1LD : srun tm false true chp_1RB0LC_1RC1RA_1LD1LD_0RB1LD P0_1RB0LC_1RC1RA_1LD1LD_0RB1LD = Some (P1_1RB0LC_1RC1RA_1LD1LD_0RB1LD, 4, 8).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB0LC_1RC1RA_1LD1LD_0RB1LD : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_1RB0LC_1RC1RA_1LD1LD_0RB1LD : sconf := mkC StD (mkS [] [S1;S1] 1 1 [S1;S0]) S0 (mkS [] [] 0 0 []).
(** ** The INNER anchor family -- Jp at StA *)
Definition Cin_1RB0LC_1RC1RA_1LD1LD_0RB1LD (v : positive) : cconf := (StA, (Jp v ++ [S1], S0, [S1])).
Local Notation Cin := Cin_1RB0LC_1RC1RA_1LD1LD_0RB1LD.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow2_1RB0LC_1RC1RA_1LD1LD_0RB1LD : forall n, Jp (pow2 n) = rep [S1;S1] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap -- ordinary and affine.  Iterating it to the fill is
    where a [Theta(2^j)] lives, and [inner_to_fill_lift] keeps it inside an
    existential. *)
Definition AI0_1RB0LC_1RC1RA_1LD1LD_0RB1LD : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition AI1_1RB0LC_1RC1RA_1LD1LD_0RB1LD : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S1;S0] [] 0 0 []).
Definition chn_1RB0LC_1RC1RA_1LD1LD_0RB1LD : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWin 1; SWinR 7].

Lemma run_inner_1RB0LC_1RC1RA_1LD1LD_0RB1LD : srun tm false true chn_1RB0LC_1RC1RA_1LD1LD_0RB1LD AI0_1RB0LC_1RC1RA_1LD1LD_0RB1LD = Some (AI1_1RB0LC_1RC1RA_1LD1LD_0RB1LD, 4, 12).
Proof. vm_compute. reflexivity. Qed.

(** *** boot: the outer overflow anchor -> the first inner anchor at [pow2 j] *)
Definition BB1_1RB0LC_1RC1RA_1LD1LD_0RB1LD : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S1]) S0 (mkS [S1;S0] [] 0 0 []).
Definition chb_1RB0LC_1RC1RA_1LD1LD_0RB1LD : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 5; SCycR 2; SWin 2; SRotL 1; SWin 5].

Lemma run_boot_1RB0LC_1RC1RA_1LD1LD_0RB1LD : srun tm true true chb_1RB0LC_1RC1RA_1LD1LD_0RB1LD B0_1RB0LC_1RC1RA_1LD1LD_0RB1LD = Some (BB1_1RB0LC_1RC1RA_1LD1LD_0RB1LD, 4, 14).
Proof. vm_compute. reflexivity. Qed.

(** *** exit: the last inner all-ones fill -> the outer successor *)
Definition BE0_1RB0LC_1RC1RA_1LD1LD_0RB1LD : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition che_1RB0LC_1RC1RA_1LD1LD_0RB1LD : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWin 1; SWinR 1; SFoldL 1].

Lemma run_exit_1RB0LC_1RC1RA_1LD1LD_0RB1LD : srun tm true true che_1RB0LC_1RC1RA_1LD1LD_0RB1LD BE0_1RB0LC_1RC1RA_1LD1LD_0RB1LD = Some (B1_1RB0LC_1RC1RA_1LD1LD_0RB1LD, 4, 6).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gz_1RB0LC_1RC1RA_1LD1LD_0RB1LD : forall p q0, cview p = (0, Some q0) ->
  Cc p = cden (Jp q0 ++ [S0]) [] 0 Z0_1RB0LC_1RC1RA_1LD1LD_0RB1LD /\
  cden (Jp q0 ++ [S0]) [] 0 Z1_1RB0LC_1RC1RA_1LD1LD_0RB1LD = Cc (Pos.succ p).
Proof.
  intros p q0 E. destruct (JpCounter.cview_some_J p 0 q0 E) as (H1 & H2).
  unfold Cc_1RB0LC_1RC1RA_1LD1LD_0RB1LD, cden, Z0_1RB0LC_1RC1RA_1LD1LD_0RB1LD, Z1_1RB0LC_1RC1RA_1LD1LD_0RB1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gp_1RB0LC_1RC1RA_1LD1LD_0RB1LD : forall p j q0, cview p = (S j, Some q0) ->
  Cc p = cden (Jp q0 ++ [S0]) [] j P0_1RB0LC_1RC1RA_1LD1LD_0RB1LD /\
  cden (Jp q0 ++ [S0]) [] j P1_1RB0LC_1RC1RA_1LD1LD_0RB1LD = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p (S j) q0 E) as (H1 & H2).
  unfold Cc_1RB0LC_1RC1RA_1LD1LD_0RB1LD, cden, P0_1RB0LC_1RC1RA_1LD1LD_0RB1LD, P1_1RB0LC_1RC1RA_1LD1LD_0RB1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB0LC_1RC1RA_1LD1LD_0RB1LD : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct j as [|j'].
  - destruct (gz_1RB0LC_1RC1RA_1LD1LD_0RB1LD p q0 E) as (HA & HB).
    exists (0 * 0 + 4). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chz_1RB0LC_1RC1RA_1LD1LD_0RB1LD Z0_1RB0LC_1RC1RA_1LD1LD_0RB1LD Z1_1RB0LC_1RC1RA_1LD1LD_0RB1LD 0 4
               run_z_1RB0LC_1RC1RA_1LD1LD_0RB1LD (Jp q0 ++ [S0]) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gp_1RB0LC_1RC1RA_1LD1LD_0RB1LD p j' q0 E) as (HA & HB).
    exists (4 * j' + 8). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chp_1RB0LC_1RC1RA_1LD1LD_0RB1LD P0_1RB0LC_1RC1RA_1LD1LD_0RB1LD P1_1RB0LC_1RC1RA_1LD1LD_0RB1LD 4 8
               run_p_1RB0LC_1RC1RA_1LD1LD_0RB1LD (Jp q0 ++ [S0]) [] j'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
Qed.

Lemma gso_1RB0LC_1RC1RA_1LD1LD_0RB1LD : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_1RB0LC_1RC1RA_1LD1LD_0RB1LD.
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (H1 & _).
  unfold Cc_1RB0LC_1RC1RA_1LD1LD_0RB1LD, cden, B0_1RB0LC_1RC1RA_1LD1LD_0RB1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB0LC_1RC1RA_1LD1LD_0RB1LD : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB0LC_1RC1RA_1LD1LD_0RB1LD : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB0LC_1RC1RA_1LD1LD_0RB1LD) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB0LC_1RC1RA_1LD1LD_0RB1LD
             = (StD, (rep [S1;S1] (S j) ++ [S1;S0], S0, []))).
  { unfold cden, B1_1RB0LC_1RC1RA_1LD1LD_0RB1LD, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StD, (rep [S1;S1] (S j) ++ [S1;S0], S0, []))).
  { unfold Cc_1RB0LC_1RC1RA_1LD1LD_0RB1LD. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. reflexivity.
Qed.

Lemma gsn_1RB0LC_1RC1RA_1LD1LD_0RB1LD : forall v i q0, cview v = (i, Some q0) ->
  Cin v = cden (Jp q0 ++ [S1]) [] i AI0_1RB0LC_1RC1RA_1LD1LD_0RB1LD.
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (H1 & _).
  unfold Cin_1RB0LC_1RC1RA_1LD1LD_0RB1LD, cden, AI0_1RB0LC_1RC1RA_1LD1LD_0RB1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen_1RB0LC_1RC1RA_1LD1LD_0RB1LD : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Jp q0 ++ [S1]) [] i AI1_1RB0LC_1RC1RA_1LD1LD_0RB1LD) = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (_ & H2).
  unfold Cin_1RB0LC_1RC1RA_1LD1LD_0RB1LD, cden, AI1_1RB0LC_1RC1RA_1LD1LD_0RB1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S1;S0]) with (([S1]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin_1RB0LC_1RC1RA_1LD1LD_0RB1LD : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 12), (cden (Jp q0 ++ [S1]) [] i AI1_1RB0LC_1RC1RA_1LD1LD_0RB1LD).
  split; [lia|]. split; [| exact (gen_1RB0LC_1RC1RA_1LD1LD_0RB1LD v i q0 E)].
  rewrite (gsn_1RB0LC_1RC1RA_1LD1LD_0RB1LD v i q0 E).
  exact (srun_sound tm false true chn_1RB0LC_1RC1RA_1LD1LD_0RB1LD AI0_1RB0LC_1RC1RA_1LD1LD_0RB1LD AI1_1RB0LC_1RC1RA_1LD1LD_0RB1LD 4 12
           run_inner_1RB0LC_1RC1RA_1LD1LD_0RB1LD (Jp q0 ++ [S1]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The chain into this family lands on its anchor up to 0/1
    trailing blanks. *)
Lemma gbo_1RB0LC_1RC1RA_1LD1LD_0RB1LD : forall j, lift (cden [] [] j BB1_1RB0LC_1RC1RA_1LD1LD_0RB1LD) = lift (Cin (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_1RB0LC_1RC1RA_1LD1LD_0RB1LD = (StA, (rep [S1;S1] j ++ [S1;S1], S0, ([S1]) ++ [S0]))).
  { unfold cden, BB1_1RB0LC_1RC1RA_1LD1LD_0RB1LD, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin (pow2 j) = (StA, (rep [S1;S1] j ++ [S1;S1], S0, [S1]))).
  { unfold Cin_1RB0LC_1RC1RA_1LD1LD_0RB1LD. rewrite epow2_1RB0LC_1RC1RA_1LD1LD_0RB1LD.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_1RB0LC_1RC1RA_1LD1LD_0RB1LD. rewrite ?lift_app_blank. reflexivity.
Qed.

(** This family's all-ones fill IS the next chain's start.  [cview (fill
    (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    family's own overflow decomposition names the word. *)
Lemma gxi_1RB0LC_1RC1RA_1LD1LD_0RB1LD : forall j, Cin (fill (pow2 j)) = cden [] [] j BE0_1RB0LC_1RC1RA_1LD1LD_0RB1LD.
Proof.
  intro j.
  destruct (JpCounter.cview_none_J (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin_1RB0LC_1RC1RA_1LD1LD_0RB1LD, cden, BE0_1RB0LC_1RC1RA_1LD1LD_0RB1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

(** The interior lap, restated up to [lift] -- what [vis_via_ovf_lift] and
    [vis_via_fill] consume. *)
Lemma lapil_1RB0LC_1RC1RA_1LD1LD_0RB1LD : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof. intros p j q0 E. destruct (lapi_1RB0LC_1RC1RA_1LD1LD_0RB1LD p j q0 E) as (n & Hn & Hr).
  exists n, (Cc (Pos.succ p)).
  split; [exact Hn | split; [exact Hr | reflexivity]]. Qed.

(** The outer OVERFLOW branch, composed.  The exponential cost is the
    [exists n] inside [inner_to_fill_lift]; no formula for it is ever
    written. *)
Lemma lapo_1RB0LC_1RC1RA_1LD1LD_0RB1LD : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E.
  apply (nested_overflow_lift tm Cc Cin lapin_1RB0LC_1RC1RA_1LD1LD_0RB1LD p (pow2 j)).
  - exists (4 * j + 14), (cden [] [] j BB1_1RB0LC_1RC1RA_1LD1LD_0RB1LD).
    split; [lia|]. split; [| exact (gbo_1RB0LC_1RC1RA_1LD1LD_0RB1LD j)].
    rewrite (gso_1RB0LC_1RC1RA_1LD1LD_0RB1LD p j E).
    exact (srun_sound tm true true chb_1RB0LC_1RC1RA_1LD1LD_0RB1LD B0_1RB0LC_1RC1RA_1LD1LD_0RB1LD BB1_1RB0LC_1RC1RA_1LD1LD_0RB1LD 4 14
             run_boot_1RB0LC_1RC1RA_1LD1LD_0RB1LD [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  - exists (4 * j + 6), (cden [] [] j B1_1RB0LC_1RC1RA_1LD1LD_0RB1LD).
    split; [| exact (geo_1RB0LC_1RC1RA_1LD1LD_0RB1LD p j E)].
    rewrite (gxi_1RB0LC_1RC1RA_1LD1LD_0RB1LD j).
    exact (srun_sound tm true true che_1RB0LC_1RC1RA_1LD1LD_0RB1LD BE0_1RB0LC_1RC1RA_1LD1LD_0RB1LD B1_1RB0LC_1RC1RA_1LD1LD_0RB1LD 4 6
             run_exit_1RB0LC_1RC1RA_1LD1LD_0RB1LD [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.



(** ** The lap *)

Lemma lap_1RB0LC_1RC1RA_1LD1LD_0RB1LD : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB0LC_1RC1RA_1LD1LD_0RB1LD p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->). exact (lapo_1RB0LC_1RC1RA_1LD1LD_0RB1LD p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_1RB0LC_1RC1RA_1LD1LD_0RB1LD : exists t0, stepn tm t0 InitES = Some (lift (Cc 2)).
Proof.
  exists 5.
  assert (H : match csteps tm 5 c0 with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 5 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_1RB0LC_1RC1RA_1LD1LD_0RB1LD : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_1RB0LC_1RC1RA_1LD1LD_0RB1LD = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_1RB0LC_1RC1RA_1LD1LD_0RB1LD p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB0LC_1RC1RA_1LD1LD_0RB1LD p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_1RB0LC_1RC1RA_1LD1LD_0RB1LD : forall t, ~ In t pins_1RB0LC_1RC1RA_1LD1LD_0RB1LD ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_1RB0LC_1RC1RA_1LD1LD_0RB1LD.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_via_ovf tm Cc Hi (StA, S0)), fireo_1RB0LC_1RC1RA_1LD1LD_0RB1LD
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1]).
    vm_compute; reflexivity.
  - (* A1 *)
    apply (fire_via_ovf tm Cc Hi (StA, S1)), fireo_1RB0LC_1RC1RA_1LD1LD_0RB1LD
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 5; SCycR 2; SWin 2; SRotL 1; SWin 1]).
    vm_compute; reflexivity.
  - (* B0 *)
    apply (fire_via_ovf tm Cc Hi (StB, S0)), fireo_1RB0LC_1RC1RA_1LD1LD_0RB1LD
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 1]).
    vm_compute; reflexivity.
  - (* B1 *)
    apply (fire_via_ovf tm Cc Hi (StB, S1)), fireo_1RB0LC_1RC1RA_1LD1LD_0RB1LD
      with (l := [SRotL 1; SWin 1]).
    vm_compute; reflexivity.
  - (* C0 *)
    apply (fire_via_ovf tm Cc Hi (StC, S0)), fireo_1RB0LC_1RC1RA_1LD1LD_0RB1LD
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 2]).
    vm_compute; reflexivity.
  - (* C1 *)
    apply (fire_via_ovf tm Cc Hi (StC, S1)), fireo_1RB0LC_1RC1RA_1LD1LD_0RB1LD
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 5; SCycR 2; SWin 2; SRotL 1; SWin 2]).
    vm_compute; reflexivity.
  - (* D0 *)
    apply (fire_via_ovf tm Cc Hi (StD, S0)), fireo_1RB0LC_1RC1RA_1LD1LD_0RB1LD
      with (l := []).
    vm_compute; reflexivity.
  - (* D1 *)
    apply (fire_via_ovf tm Cc Hi (StD, S1)), fireo_1RB0LC_1RC1RA_1LD1LD_0RB1LD
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 3]).
    vm_compute; reflexivity.
Qed.

Theorem nqhtrm_1RB0LC_1RC1RA_1LD1LD_0RB1LD : NeverQuasiHaltsTr tmm_1RB0LC_1RC1RA_1LD1LD_0RB1LD.
Proof.
  apply (glue_neverqhtr tmm_1RB0LC_1RC1RA_1LD1LD_0RB1LD pins_1RB0LC_1RC1RA_1LD1LD_0RB1LD Cc 2).
  - exact boot_1RB0LC_1RC1RA_1LD1LD_0RB1LD.
  - intros p _. apply lap_1RB0LC_1RC1RA_1LD1LD_0RB1LD.
  - intros t Ht p _. apply fire_1RB0LC_1RC1RA_1LD1LD_0RB1LD. exact Ht.
Qed.

Theorem nqhtr_1RB0LC_1RC1RA_1LD1LD_0RB1LD : NeverQuasiHaltsTr tm_1RB0LC_1RC1RA_1LD1LD_0RB1LD.
Proof. apply (neverqhtr_mirror tm_1RB0LC_1RC1RA_1LD1LD_0RB1LD). rewrite mirror_ok_1RB0LC_1RC1RA_1LD1LD_0RB1LD. exact nqhtrm_1RB0LC_1RC1RA_1LD1LD_0RB1LD. Qed.

Theorem nonhalt_1RB0LC_1RC1RA_1LD1LD_0RB1LD : NonHalt tm_1RB0LC_1RC1RA_1LD1LD_0RB1LD.
Proof. apply never_qh_tr_nonhalt, nqhtr_1RB0LC_1RC1RA_1LD1LD_0RB1LD. Qed.
