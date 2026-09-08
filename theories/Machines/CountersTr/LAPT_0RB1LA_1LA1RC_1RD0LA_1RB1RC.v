(** * LAPT_0RB1LA_1LA1RC_1RD0LA_1RB1RC: TRANSITION-LEVEL board for machine 0RB1LA_1LA1RC_1RD0LA_1RB1RC, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Jp digit alphabet (JpCounter.v), anchored at

      Cc p = (StA, (Jp p ++ [S0], S0, []))

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

Definition mk_0RB1LA_1LA1RC_1RD0LA_1RB1RC (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB1LA_1LA1RC_1RD0LA_1RB1RC.

(** 0RB1LA_1LA1RC_1RD0LA_1RB1RC *)
(** 0RB1LA_1LA1RC_1RD0LA_1RB1RC -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB1LA_1LA1RC_1RD0LA_1RB1RC : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S1 DL StA
  | StB, S0 => mk S1 DL StA | StB, S1 => mk S1 DR StC
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S0 DL StA
  | StD, S0 => mk S1 DR StB | StD, S1 => mk S1 DR StC end.

(** Its mirror 0LB1RA_1RA1LC_1LD0RA_1LB1LC: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB1LA_1LA1RC_1RD0LA_1RB1RC : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S1 DR StA
  | StB, S0 => mk S1 DR StA | StB, S1 => mk S1 DL StC
  | StC, S0 => mk S1 DL StD | StC, S1 => mk S0 DR StA
  | StD, S0 => mk S1 DL StB | StD, S1 => mk S1 DL StC end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_0RB1LA_1LA1RC_1RD0LA_1RB1RC : list Instr := [].
Definition tmw_0RB1LA_1LA1RC_1RD0LA_1RB1RC : TM := tm_wrap_trs tmm_0RB1LA_1LA1RC_1RD0LA_1RB1RC pins_0RB1LA_1LA1RC_1RD0LA_1RB1RC.
Local Notation tm := tmw_0RB1LA_1LA1RC_1RD0LA_1RB1RC.

Lemma mirror_ok_0RB1LA_1LA1RC_1RD0LA_1RB1RC : mirror_tm tm_0RB1LA_1LA1RC_1RD0LA_1RB1RC = tmm_0RB1LA_1LA1RC_1RD0LA_1RB1RC.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_0RB1LA_1LA1RC_1RD0LA_1RB1RC (p : positive) : cconf := (StA, (Jp p ++ [S0], S0, [])).
Local Notation Cc := Cc_0RB1LA_1LA1RC_1RD0LA_1RB1RC.

(** ** The certificate *)

(** j = 0: the repeated block is absent, so the whole lap is concrete. *)
Definition Z0_0RB1LA_1LA1RC_1RD0LA_1RB1RC : sconf := mkC StA (mkS [S1;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition Z1_0RB1LA_1LA1RC_1RD0LA_1RB1RC : sconf := mkC StA (mkS [S1;S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition chz_0RB1LA_1LA1RC_1RD0LA_1RB1RC : list lstep := [SWin 4].

Lemma run_z_0RB1LA_1LA1RC_1RD0LA_1RB1RC : srun tm false true chz_0RB1LA_1LA1RC_1RD0LA_1RB1RC Z0_0RB1LA_1LA1RC_1RD0LA_1RB1RC = Some (Z1_0RB1LA_1LA1RC_1RD0LA_1RB1RC, 0, 4).
Proof. vm_compute. reflexivity. Qed.

(** j = S j': one copy of the unit sits in the PREFIX, so the head always has
    a concrete cell to step onto. *)
Definition P0_0RB1LA_1LA1RC_1RD0LA_1RB1RC : sconf := mkC StA (mkS [S1;S0] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition P1_0RB1LA_1LA1RC_1RD0LA_1RB1RC : sconf := mkC StA (mkS [S1;S1] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chp_0RB1LA_1LA1RC_1RD0LA_1RB1RC : list lstep := [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 2].

Lemma run_p_0RB1LA_1LA1RC_1RD0LA_1RB1RC : srun tm false true chp_0RB1LA_1LA1RC_1RD0LA_1RB1RC P0_0RB1LA_1LA1RC_1RD0LA_1RB1RC = Some (P1_0RB1LA_1LA1RC_1RD0LA_1RB1RC, 4, 8).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB1LA_1LA1RC_1RD0LA_1RB1RC : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_0RB1LA_1LA1RC_1RD0LA_1RB1RC : sconf := mkC StA (mkS [] [S1;S1] 1 1 [S1;S0]) S0 (mkS [] [] 0 0 []).
(** ** The INNER anchor family -- Jp at StC *)
Definition Cin_0RB1LA_1LA1RC_1RD0LA_1RB1RC (v : positive) : cconf := (StC, (Jp v ++ [S1], S0, [S1])).
Local Notation Cin := Cin_0RB1LA_1LA1RC_1RD0LA_1RB1RC.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow2_0RB1LA_1LA1RC_1RD0LA_1RB1RC : forall n, Jp (pow2 n) = rep [S1;S1] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap -- ordinary and affine.  Iterating it to the fill is
    where a [Theta(2^j)] lives, and [inner_to_fill_lift] keeps it inside an
    existential. *)
Definition AI0_0RB1LA_1LA1RC_1RD0LA_1RB1RC : sconf := mkC StC (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition AI1_0RB1LA_1LA1RC_1RD0LA_1RB1RC : sconf := mkC StC (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S1;S0] [] 0 0 []).
Definition chn_0RB1LA_1LA1RC_1RD0LA_1RB1RC : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWin 1; SWinR 7].

Lemma run_inner_0RB1LA_1LA1RC_1RD0LA_1RB1RC : srun tm false true chn_0RB1LA_1LA1RC_1RD0LA_1RB1RC AI0_0RB1LA_1LA1RC_1RD0LA_1RB1RC = Some (AI1_0RB1LA_1LA1RC_1RD0LA_1RB1RC, 4, 12).
Proof. vm_compute. reflexivity. Qed.

(** *** boot: the outer overflow anchor -> the first inner anchor at [pow2 j] *)
Definition BB1_0RB1LA_1LA1RC_1RD0LA_1RB1RC : sconf := mkC StC (mkS [] [S1;S1] 1 0 [S1;S1]) S0 (mkS [S1;S0] [] 0 0 []).
Definition chb_0RB1LA_1LA1RC_1RD0LA_1RB1RC : list lstep := [SRotL 1; SWin 1; SRotL 1; SWin 1; SCycL 2 0; SWinL 4; SCycR 2; SWin 8].

Lemma run_boot_0RB1LA_1LA1RC_1RD0LA_1RB1RC : srun tm true true chb_0RB1LA_1LA1RC_1RD0LA_1RB1RC B0_0RB1LA_1LA1RC_1RD0LA_1RB1RC = Some (BB1_0RB1LA_1LA1RC_1RD0LA_1RB1RC, 4, 14).
Proof. vm_compute. reflexivity. Qed.

(** *** exit: the last inner all-ones fill -> the outer successor *)
Definition BE0_0RB1LA_1LA1RC_1RD0LA_1RB1RC : sconf := mkC StC (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition che_0RB1LA_1LA1RC_1RD0LA_1RB1RC : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWin 1; SWinR 1; SFoldL 1].

Lemma run_exit_0RB1LA_1LA1RC_1RD0LA_1RB1RC : srun tm true true che_0RB1LA_1LA1RC_1RD0LA_1RB1RC BE0_0RB1LA_1LA1RC_1RD0LA_1RB1RC = Some (B1_0RB1LA_1LA1RC_1RD0LA_1RB1RC, 4, 6).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gz_0RB1LA_1LA1RC_1RD0LA_1RB1RC : forall p q0, cview p = (0, Some q0) ->
  Cc p = cden (Jp q0 ++ [S0]) [] 0 Z0_0RB1LA_1LA1RC_1RD0LA_1RB1RC /\
  cden (Jp q0 ++ [S0]) [] 0 Z1_0RB1LA_1LA1RC_1RD0LA_1RB1RC = Cc (Pos.succ p).
Proof.
  intros p q0 E. destruct (JpCounter.cview_some_J p 0 q0 E) as (H1 & H2).
  unfold Cc_0RB1LA_1LA1RC_1RD0LA_1RB1RC, cden, Z0_0RB1LA_1LA1RC_1RD0LA_1RB1RC, Z1_0RB1LA_1LA1RC_1RD0LA_1RB1RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gp_0RB1LA_1LA1RC_1RD0LA_1RB1RC : forall p j q0, cview p = (S j, Some q0) ->
  Cc p = cden (Jp q0 ++ [S0]) [] j P0_0RB1LA_1LA1RC_1RD0LA_1RB1RC /\
  cden (Jp q0 ++ [S0]) [] j P1_0RB1LA_1LA1RC_1RD0LA_1RB1RC = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p (S j) q0 E) as (H1 & H2).
  unfold Cc_0RB1LA_1LA1RC_1RD0LA_1RB1RC, cden, P0_0RB1LA_1LA1RC_1RD0LA_1RB1RC, P1_0RB1LA_1LA1RC_1RD0LA_1RB1RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_0RB1LA_1LA1RC_1RD0LA_1RB1RC : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct j as [|j'].
  - destruct (gz_0RB1LA_1LA1RC_1RD0LA_1RB1RC p q0 E) as (HA & HB).
    exists (0 * 0 + 4). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chz_0RB1LA_1LA1RC_1RD0LA_1RB1RC Z0_0RB1LA_1LA1RC_1RD0LA_1RB1RC Z1_0RB1LA_1LA1RC_1RD0LA_1RB1RC 0 4
               run_z_0RB1LA_1LA1RC_1RD0LA_1RB1RC (Jp q0 ++ [S0]) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gp_0RB1LA_1LA1RC_1RD0LA_1RB1RC p j' q0 E) as (HA & HB).
    exists (4 * j' + 8). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chp_0RB1LA_1LA1RC_1RD0LA_1RB1RC P0_0RB1LA_1LA1RC_1RD0LA_1RB1RC P1_0RB1LA_1LA1RC_1RD0LA_1RB1RC 4 8
               run_p_0RB1LA_1LA1RC_1RD0LA_1RB1RC (Jp q0 ++ [S0]) [] j'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
Qed.

Lemma gso_0RB1LA_1LA1RC_1RD0LA_1RB1RC : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_0RB1LA_1LA1RC_1RD0LA_1RB1RC.
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (H1 & _).
  unfold Cc_0RB1LA_1LA1RC_1RD0LA_1RB1RC, cden, B0_0RB1LA_1LA1RC_1RD0LA_1RB1RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_0RB1LA_1LA1RC_1RD0LA_1RB1RC : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_0RB1LA_1LA1RC_1RD0LA_1RB1RC : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB1LA_1LA1RC_1RD0LA_1RB1RC) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_0RB1LA_1LA1RC_1RD0LA_1RB1RC
             = (StA, (rep [S1;S1] (S j) ++ [S1;S0], S0, []))).
  { unfold cden, B1_0RB1LA_1LA1RC_1RD0LA_1RB1RC, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StA, (rep [S1;S1] (S j) ++ [S1;S0], S0, []))).
  { unfold Cc_0RB1LA_1LA1RC_1RD0LA_1RB1RC. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. reflexivity.
Qed.

Lemma gsn_0RB1LA_1LA1RC_1RD0LA_1RB1RC : forall v i q0, cview v = (i, Some q0) ->
  Cin v = cden (Jp q0 ++ [S1]) [] i AI0_0RB1LA_1LA1RC_1RD0LA_1RB1RC.
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (H1 & _).
  unfold Cin_0RB1LA_1LA1RC_1RD0LA_1RB1RC, cden, AI0_0RB1LA_1LA1RC_1RD0LA_1RB1RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen_0RB1LA_1LA1RC_1RD0LA_1RB1RC : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Jp q0 ++ [S1]) [] i AI1_0RB1LA_1LA1RC_1RD0LA_1RB1RC) = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (_ & H2).
  unfold Cin_0RB1LA_1LA1RC_1RD0LA_1RB1RC, cden, AI1_0RB1LA_1LA1RC_1RD0LA_1RB1RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S1;S0]) with (([S1]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin_0RB1LA_1LA1RC_1RD0LA_1RB1RC : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 12), (cden (Jp q0 ++ [S1]) [] i AI1_0RB1LA_1LA1RC_1RD0LA_1RB1RC).
  split; [lia|]. split; [| exact (gen_0RB1LA_1LA1RC_1RD0LA_1RB1RC v i q0 E)].
  rewrite (gsn_0RB1LA_1LA1RC_1RD0LA_1RB1RC v i q0 E).
  exact (srun_sound tm false true chn_0RB1LA_1LA1RC_1RD0LA_1RB1RC AI0_0RB1LA_1LA1RC_1RD0LA_1RB1RC AI1_0RB1LA_1LA1RC_1RD0LA_1RB1RC 4 12
           run_inner_0RB1LA_1LA1RC_1RD0LA_1RB1RC (Jp q0 ++ [S1]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The chain into this family lands on its anchor up to 0/1
    trailing blanks. *)
Lemma gbo_0RB1LA_1LA1RC_1RD0LA_1RB1RC : forall j, lift (cden [] [] j BB1_0RB1LA_1LA1RC_1RD0LA_1RB1RC) = lift (Cin (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_0RB1LA_1LA1RC_1RD0LA_1RB1RC = (StC, (rep [S1;S1] j ++ [S1;S1], S0, ([S1]) ++ [S0]))).
  { unfold cden, BB1_0RB1LA_1LA1RC_1RD0LA_1RB1RC, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin (pow2 j) = (StC, (rep [S1;S1] j ++ [S1;S1], S0, [S1]))).
  { unfold Cin_0RB1LA_1LA1RC_1RD0LA_1RB1RC. rewrite epow2_0RB1LA_1LA1RC_1RD0LA_1RB1RC.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_0RB1LA_1LA1RC_1RD0LA_1RB1RC. rewrite ?lift_app_blank. reflexivity.
Qed.

(** This family's all-ones fill IS the next chain's start.  [cview (fill
    (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    family's own overflow decomposition names the word. *)
Lemma gxi_0RB1LA_1LA1RC_1RD0LA_1RB1RC : forall j, Cin (fill (pow2 j)) = cden [] [] j BE0_0RB1LA_1LA1RC_1RD0LA_1RB1RC.
Proof.
  intro j.
  destruct (JpCounter.cview_none_J (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin_0RB1LA_1LA1RC_1RD0LA_1RB1RC, cden, BE0_0RB1LA_1LA1RC_1RD0LA_1RB1RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

(** The interior lap, restated up to [lift] -- what [vis_via_ovf_lift] and
    [vis_via_fill] consume. *)
Lemma lapil_0RB1LA_1LA1RC_1RD0LA_1RB1RC : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof. intros p j q0 E. destruct (lapi_0RB1LA_1LA1RC_1RD0LA_1RB1RC p j q0 E) as (n & Hn & Hr).
  exists n, (Cc (Pos.succ p)).
  split; [exact Hn | split; [exact Hr | reflexivity]]. Qed.

(** The outer OVERFLOW branch, composed.  The exponential cost is the
    [exists n] inside [inner_to_fill_lift]; no formula for it is ever
    written. *)
Lemma lapo_0RB1LA_1LA1RC_1RD0LA_1RB1RC : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E.
  apply (nested_overflow_lift tm Cc Cin lapin_0RB1LA_1LA1RC_1RD0LA_1RB1RC p (pow2 j)).
  - exists (4 * j + 14), (cden [] [] j BB1_0RB1LA_1LA1RC_1RD0LA_1RB1RC).
    split; [lia|]. split; [| exact (gbo_0RB1LA_1LA1RC_1RD0LA_1RB1RC j)].
    rewrite (gso_0RB1LA_1LA1RC_1RD0LA_1RB1RC p j E).
    exact (srun_sound tm true true chb_0RB1LA_1LA1RC_1RD0LA_1RB1RC B0_0RB1LA_1LA1RC_1RD0LA_1RB1RC BB1_0RB1LA_1LA1RC_1RD0LA_1RB1RC 4 14
             run_boot_0RB1LA_1LA1RC_1RD0LA_1RB1RC [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  - exists (4 * j + 6), (cden [] [] j B1_0RB1LA_1LA1RC_1RD0LA_1RB1RC).
    split; [| exact (geo_0RB1LA_1LA1RC_1RD0LA_1RB1RC p j E)].
    rewrite (gxi_0RB1LA_1LA1RC_1RD0LA_1RB1RC j).
    exact (srun_sound tm true true che_0RB1LA_1LA1RC_1RD0LA_1RB1RC BE0_0RB1LA_1LA1RC_1RD0LA_1RB1RC B1_0RB1LA_1LA1RC_1RD0LA_1RB1RC 4 6
             run_exit_0RB1LA_1LA1RC_1RD0LA_1RB1RC [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.



(** ** The lap *)

Lemma lap_0RB1LA_1LA1RC_1RD0LA_1RB1RC : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB1LA_1LA1RC_1RD0LA_1RB1RC p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->). exact (lapo_0RB1LA_1LA1RC_1RD0LA_1RB1RC p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_0RB1LA_1LA1RC_1RD0LA_1RB1RC : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 2.
  assert (H : match csteps tm 2 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 2 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_0RB1LA_1LA1RC_1RD0LA_1RB1RC : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_0RB1LA_1LA1RC_1RD0LA_1RB1RC = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_0RB1LA_1LA1RC_1RD0LA_1RB1RC p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB1LA_1LA1RC_1RD0LA_1RB1RC p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_0RB1LA_1LA1RC_1RD0LA_1RB1RC : forall t, ~ In t pins_0RB1LA_1LA1RC_1RD0LA_1RB1RC ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_0RB1LA_1LA1RC_1RD0LA_1RB1RC.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_via_ovf tm Cc Hi (StA, S0)), fireo_0RB1LA_1LA1RC_1RD0LA_1RB1RC
      with (l := []).
    vm_compute; reflexivity.
  - (* A1 *)
    apply (fire_via_ovf tm Cc Hi (StA, S1)), fireo_0RB1LA_1LA1RC_1RD0LA_1RB1RC
      with (l := [SRotL 1; SWin 1; SRotL 1; SWin 1; SCycL 2 0; SWinL 3]).
    vm_compute; reflexivity.
  - (* B0 *)
    apply (fire_via_ovf tm Cc Hi (StB, S0)), fireo_0RB1LA_1LA1RC_1RD0LA_1RB1RC
      with (l := [SRotL 1; SWin 1; SRotL 1; SWin 1; SCycL 2 0; SWinL 2]).
    vm_compute; reflexivity.
  - (* B1 *)
    apply (fire_via_ovf tm Cc Hi (StB, S1)), fireo_0RB1LA_1LA1RC_1RD0LA_1RB1RC
      with (l := [SRotL 1; SWin 1]).
    vm_compute; reflexivity.
  - (* C0 *)
    apply (fire_via_ovf tm Cc Hi (StC, S0)), fireo_0RB1LA_1LA1RC_1RD0LA_1RB1RC
      with (l := [SRotL 1; SWin 1; SRotL 1; SWin 1]).
    vm_compute; reflexivity.
  - (* C1 *)
    apply (fire_via_ovf tm Cc Hi (StC, S1)), fireo_0RB1LA_1LA1RC_1RD0LA_1RB1RC
      with (l := [SRotL 1; SWin 1; SRotL 1; SWin 1; SCycL 2 0; SWinL 4; SCycR 2; SWin 4]).
    vm_compute; reflexivity.
  - (* D0 *)
    apply (fire_via_ovf tm Cc Hi (StD, S0)), fireo_0RB1LA_1LA1RC_1RD0LA_1RB1RC
      with (l := [SRotL 1; SWin 1; SRotL 1; SWin 1; SCycL 2 0; SWinL 1]).
    vm_compute; reflexivity.
  - (* D1 *)
    apply (fire_via_ovf tm Cc Hi (StD, S1)), fireo_0RB1LA_1LA1RC_1RD0LA_1RB1RC
      with (l := [SRotL 1; SWin 1; SRotL 1; SWin 1; SCycL 2 0; SWinL 4; SCycR 2; SWin 8; SRotL 1; SWin 1]).
    vm_compute; reflexivity.
Qed.

Theorem nqhtrm_0RB1LA_1LA1RC_1RD0LA_1RB1RC : NeverQuasiHaltsTr tmm_0RB1LA_1LA1RC_1RD0LA_1RB1RC.
Proof.
  apply (glue_neverqhtr tmm_0RB1LA_1LA1RC_1RD0LA_1RB1RC pins_0RB1LA_1LA1RC_1RD0LA_1RB1RC Cc 1).
  - exact boot_0RB1LA_1LA1RC_1RD0LA_1RB1RC.
  - intros p _. apply lap_0RB1LA_1LA1RC_1RD0LA_1RB1RC.
  - intros t Ht p _. apply fire_0RB1LA_1LA1RC_1RD0LA_1RB1RC. exact Ht.
Qed.

Theorem nqhtr_0RB1LA_1LA1RC_1RD0LA_1RB1RC : NeverQuasiHaltsTr tm_0RB1LA_1LA1RC_1RD0LA_1RB1RC.
Proof. apply (neverqhtr_mirror tm_0RB1LA_1LA1RC_1RD0LA_1RB1RC). rewrite mirror_ok_0RB1LA_1LA1RC_1RD0LA_1RB1RC. exact nqhtrm_0RB1LA_1LA1RC_1RD0LA_1RB1RC. Qed.

Theorem nonhalt_0RB1LA_1LA1RC_1RD0LA_1RB1RC : NonHalt tm_0RB1LA_1LA1RC_1RD0LA_1RB1RC.
Proof. apply never_qh_tr_nonhalt, nqhtr_0RB1LA_1LA1RC_1RD0LA_1RB1RC. Qed.
