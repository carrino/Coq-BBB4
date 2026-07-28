(** * NLAP_1RB0LC_1LC1RD_0RD1LA_1LC1RD: machine 1RB0LC_1LC1RD_0RD1LA_1LC1RD, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Mp digit alphabet (MpCounter.v), anchored at

      Cc p = (StC, (Mp p ++ [S1;S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  j=0: 2 ; j=S j': 4*j'+6 steps
      overflow  (cview p = (S j, None)):   boot 4*j+17, then the inner counter's own laps to the
                                           all-ones fill, then exit 4*j+10

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 192 interior anchors (interior); offset c=2: 7 overflow phases, j = 1..7 (487 inner laps), plus the concrete j=0 lap (nested overflow).
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter MpCounter LapCertGlue LapCertGlueLift IXPGadgets NestedLap NestedLapLift Alph_01_11_011.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_1RB0LC_1LC1RD_0RD1LA_1LC1RD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB0LC_1LC1RD_0RD1LA_1LC1RD.

(** 1RB0LC_1LC1RD_0RD1LA_1LC1RD *)
(** 1RB0LC_1LC1RD_0RD1LA_1LC1RD -- the real machine (its counter grows RIGHT). *)
Definition tm_1RB0LC_1LC1RD_0RD1LA_1LC1RD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StC
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S0 DR StD | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S1 DL StC | StD, S1 => mk S1 DR StD end.

(** Its mirror 1LB0RC_1RC1LD_0LD1RA_1RC1LD: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_1RB0LC_1LC1RD_0RD1LA_1LC1RD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => mk S0 DR StC
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DL StD
  | StC, S0 => mk S0 DL StD | StC, S1 => mk S1 DR StA
  | StD, S0 => mk S1 DR StC | StD, S1 => mk S1 DL StD end.
Local Notation tm := tmm_1RB0LC_1LC1RD_0RD1LA_1LC1RD.

Lemma mirror_ok_1RB0LC_1LC1RD_0RD1LA_1LC1RD : mirror_tm tm_1RB0LC_1LC1RD_0RD1LA_1LC1RD = tmm_1RB0LC_1LC1RD_0RD1LA_1LC1RD.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_1RB0LC_1LC1RD_0RD1LA_1LC1RD (p : positive) : cconf := (StC, (Mp p ++ [S1;S0], S0, [])).
Local Notation Cc := Cc_1RB0LC_1LC1RD_0RD1LA_1LC1RD.

(** ** The certificate *)

(** j = 0: the repeated block is absent, so the whole lap is concrete. *)
Definition Z0_1RB0LC_1LC1RD_0RD1LA_1LC1RD : sconf := mkC StC (mkS [S0;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition Z1_1RB0LC_1LC1RD_0RD1LA_1LC1RD : sconf := mkC StC (mkS [S1;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition chz_1RB0LC_1LC1RD_0RD1LA_1LC1RD : list lstep := [SWin 2].

Lemma run_z_1RB0LC_1LC1RD_0RD1LA_1LC1RD : srun tm false true chz_1RB0LC_1LC1RD_0RD1LA_1LC1RD Z0_1RB0LC_1LC1RD_0RD1LA_1LC1RD = Some (Z1_1RB0LC_1LC1RD_0RD1LA_1LC1RD, 0, 2).
Proof. vm_compute. reflexivity. Qed.

(** j = S j': one copy of the unit sits in the PREFIX, so the head always has
    a concrete cell to step onto. *)
Definition P0_1RB0LC_1LC1RD_0RD1LA_1LC1RD : sconf := mkC StC (mkS [S1;S1] [S1;S1] 1 0 [S0;S1]) S0 (mkS [] [] 0 0 []).
Definition P1_1RB0LC_1LC1RD_0RD1LA_1LC1RD : sconf := mkC StC (mkS [S0;S1] [S0;S1] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chp_1RB0LC_1LC1RD_0RD1LA_1LC1RD : list lstep := [SWin 2; SCycL 2 0; SWin 2; SCycR 2; SWin 2].

Lemma run_p_1RB0LC_1LC1RD_0RD1LA_1LC1RD : srun tm false true chp_1RB0LC_1LC1RD_0RD1LA_1LC1RD P0_1RB0LC_1LC1RD_0RD1LA_1LC1RD = Some (P1_1RB0LC_1LC1RD_0RD1LA_1LC1RD, 4, 6).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB0LC_1LC1RD_0RD1LA_1LC1RD : sconf := mkC StC (mkS [S1;S1] [S1;S1] 1 1 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_1RB0LC_1LC1RD_0RD1LA_1LC1RD : sconf := mkC StC (mkS [] [S0;S1] 1 2 [S1;S1;S1]) S0 (mkS [] [] 0 0 []).
(** ** The INNER anchor family -- Ap_Alph_01_11_011 at StC *)
Definition Cin_1RB0LC_1LC1RD_0RD1LA_1LC1RD (v : positive) : cconf := (StC, (Ap_Alph_01_11_011 v ++ [], S0, [])).
Local Notation Cin := Cin_1RB0LC_1LC1RD_0RD1LA_1LC1RD.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow2_1RB0LC_1LC1RD_0RD1LA_1LC1RD : forall n, Ap_Alph_01_11_011 (pow2 n) = rep [S0;S1] n ++ [S0;S1;S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap, SPLIT: the carry sweep's period sits one cell
    into the unit, so i = 0 is one concrete window and i = S i' runs with a
    unit PEELED into the prefix (count i' = i - 1) -- the interior-lap
    mirror of the outer j = 0 split. *)
Definition AIZ0_1RB0LC_1LC1RD_0RD1LA_1LC1RD : sconf := mkC StC (mkS [S0;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition AIZ1_1RB0LC_1LC1RD_0RD1LA_1LC1RD : sconf := mkC StC (mkS [S1;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition chnz_1RB0LC_1LC1RD_0RD1LA_1LC1RD : list lstep := [SWin 2].

Lemma run_innerz_1RB0LC_1LC1RD_0RD1LA_1LC1RD : srun tm false true chnz_1RB0LC_1LC1RD_0RD1LA_1LC1RD AIZ0_1RB0LC_1LC1RD_0RD1LA_1LC1RD = Some (AIZ1_1RB0LC_1LC1RD_0RD1LA_1LC1RD, 0, 2).
Proof. vm_compute. reflexivity. Qed.

Definition AIP0_1RB0LC_1LC1RD_0RD1LA_1LC1RD : sconf := mkC StC (mkS [S1;S1] [S1;S1] 1 0 [S0;S1]) S0 (mkS [] [] 0 0 []).
Definition AIP1_1RB0LC_1LC1RD_0RD1LA_1LC1RD : sconf := mkC StC (mkS [S0;S1] [S0;S1] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chnp_1RB0LC_1LC1RD_0RD1LA_1LC1RD : list lstep := [SWin 2; SCycL 2 0; SWin 2; SCycR 2; SWin 2].

Lemma run_innerp_1RB0LC_1LC1RD_0RD1LA_1LC1RD : srun tm false true chnp_1RB0LC_1LC1RD_0RD1LA_1LC1RD AIP0_1RB0LC_1LC1RD_0RD1LA_1LC1RD = Some (AIP1_1RB0LC_1LC1RD_0RD1LA_1LC1RD, 4, 6).
Proof. vm_compute. reflexivity. Qed.

(** The OFFSET start: [E (2^(n+2)+2)] is fixed digit blocks, then the rep.
    Its block count is one short of the outer index, which is why [lapo_]
    below REINDEXES at [j = S j']. *)
Lemma epre_1RB0LC_1LC1RD_0RD1LA_1LC1RD : forall n, Ap_Alph_01_11_011 (xO (xI (pow2 n))) = [S0;S1;S1;S1] ++ rep [S0;S1] n ++ [S0;S1;S1].
Proof.
  intro n. cbn [Ap_Alph_01_11_011]. rewrite epow2_1RB0LC_1LC1RD_0RD1LA_1LC1RD.
  cbn [app]. rewrite <- ?app_assoc. cbn [app]. reflexivity.
Qed.

(** Rotating one fixed cell across a rep -- the bridge between a chain's
    natural landing frame and the encoding's block frame ([WTape.rep_rot],
    with the trailing cell fused into the tail). *)
Lemma rrc_1RB0LC_1LC1RD_0RD1LA_1LC1RD : forall (x : Sym) (u : list Sym) k (Y : list Sym),
  rep (x :: u) k ++ x :: Y = x :: rep (u ++ [x]) k ++ Y.
Proof.
  intros. change (x :: Y) with ([x] ++ Y). rewrite app_assoc, <- rep_rot.
  cbn [app]. rewrite <- ?app_assoc. reflexivity.
Qed.

(** *** boot: the outer overflow anchor -> the first inner anchor at [pow2 j] *)
Definition BB1_1RB0LC_1LC1RD_0RD1LA_1LC1RD : sconf := mkC StC (mkS [S0;S1;S1] [S1;S0] 1 1 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chb_1RB0LC_1LC1RD_0RD1LA_1LC1RD : list lstep := [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 6; SWinR 1].

Lemma run_boot_1RB0LC_1LC1RD_0RD1LA_1LC1RD : srun tm true true chb_1RB0LC_1LC1RD_0RD1LA_1LC1RD B0_1RB0LC_1LC1RD_0RD1LA_1LC1RD = Some (BB1_1RB0LC_1LC1RD_0RD1LA_1LC1RD, 4, 17).
Proof. vm_compute. reflexivity. Qed.

(** *** exit: the last inner all-ones fill -> the outer successor *)
Definition BE0_1RB0LC_1LC1RD_0RD1LA_1LC1RD : sconf := mkC StC (mkS [S1] [S1;S1] 1 1 [S1;S0;S1;S1]) S0 (mkS [] [] 0 0 []).
Definition che_1RB0LC_1LC1RD_0RD1LA_1LC1RD : list lstep := [SWin 1; SCycL 2 0; SWin 4; SCycR 2; SWin 1; SRotL 1; SFoldL 1].

Lemma run_exit_1RB0LC_1LC1RD_0RD1LA_1LC1RD : srun tm true true che_1RB0LC_1LC1RD_0RD1LA_1LC1RD BE0_1RB0LC_1LC1RD_0RD1LA_1LC1RD = Some (B1_1RB0LC_1LC1RD_0RD1LA_1LC1RD, 4, 10).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gz_1RB0LC_1LC1RD_0RD1LA_1LC1RD : forall p q0, cview p = (0, Some q0) ->
  Cc p = cden (Mp q0 ++ [S1;S0]) [] 0 Z0_1RB0LC_1LC1RD_0RD1LA_1LC1RD /\
  cden (Mp q0 ++ [S1;S0]) [] 0 Z1_1RB0LC_1LC1RD_0RD1LA_1LC1RD = Cc (Pos.succ p).
Proof.
  intros p q0 E. destruct (MpCounter.cview_some_M p 0 q0 E) as (H1 & H2).
  unfold Cc_1RB0LC_1LC1RD_0RD1LA_1LC1RD, cden, Z0_1RB0LC_1LC1RD_0RD1LA_1LC1RD, Z1_1RB0LC_1LC1RD_0RD1LA_1LC1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gp_1RB0LC_1LC1RD_0RD1LA_1LC1RD : forall p j q0, cview p = (S j, Some q0) ->
  Cc p = cden (Mp q0 ++ [S1;S0]) [] j P0_1RB0LC_1LC1RD_0RD1LA_1LC1RD /\
  cden (Mp q0 ++ [S1;S0]) [] j P1_1RB0LC_1LC1RD_0RD1LA_1LC1RD = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (MpCounter.cview_some_M p (S j) q0 E) as (H1 & H2).
  unfold Cc_1RB0LC_1LC1RD_0RD1LA_1LC1RD, cden, P0_1RB0LC_1LC1RD_0RD1LA_1LC1RD, P1_1RB0LC_1LC1RD_0RD1LA_1LC1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB0LC_1LC1RD_0RD1LA_1LC1RD : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct j as [|j'].
  - destruct (gz_1RB0LC_1LC1RD_0RD1LA_1LC1RD p q0 E) as (HA & HB).
    exists (0 * 0 + 2). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chz_1RB0LC_1LC1RD_0RD1LA_1LC1RD Z0_1RB0LC_1LC1RD_0RD1LA_1LC1RD Z1_1RB0LC_1LC1RD_0RD1LA_1LC1RD 0 2
               run_z_1RB0LC_1LC1RD_0RD1LA_1LC1RD (Mp q0 ++ [S1;S0]) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gp_1RB0LC_1LC1RD_0RD1LA_1LC1RD p j' q0 E) as (HA & HB).
    exists (4 * j' + 6). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chp_1RB0LC_1LC1RD_0RD1LA_1LC1RD P0_1RB0LC_1LC1RD_0RD1LA_1LC1RD P1_1RB0LC_1LC1RD_0RD1LA_1LC1RD 4 6
               run_p_1RB0LC_1LC1RD_0RD1LA_1LC1RD (Mp q0 ++ [S1;S0]) [] j'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
Qed.

Lemma gso_1RB0LC_1LC1RD_0RD1LA_1LC1RD : forall p j, cview p = (S (S j), None) ->
  Cc p = cden [] [] j B0_1RB0LC_1LC1RD_0RD1LA_1LC1RD.
Proof.
  intros p j E. destruct (MpCounter.cview_none_M p (S j) E) as (H1 & _).
  unfold Cc_1RB0LC_1LC1RD_0RD1LA_1LC1RD, cden, B0_1RB0LC_1LC1RD_0RD1LA_1LC1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 1) with ((S j)) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB0LC_1LC1RD_0RD1LA_1LC1RD : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB0LC_1LC1RD_0RD1LA_1LC1RD : forall p j, cview p = (S (S j), None) ->
  lift (cden [] [] j B1_1RB0LC_1LC1RD_0RD1LA_1LC1RD) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (MpCounter.cview_none_M p (S j) E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB0LC_1LC1RD_0RD1LA_1LC1RD
             = (StC, (rep [S0;S1] (S (S j)) ++ [S1;S1;S1], S0, []))).
  { unfold cden, B1_1RB0LC_1LC1RD_0RD1LA_1LC1RD, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 2) with (S (S j)) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StC, ((rep [S0;S1] (S (S j)) ++ [S1;S1;S1]) ++ [S0], S0, []))).
  { unfold Cc_1RB0LC_1LC1RD_0RD1LA_1LC1RD. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_1RB0LC_1LC1RD_0RD1LA_1LC1RD. reflexivity.
Qed.

Lemma gsnz_1RB0LC_1LC1RD_0RD1LA_1LC1RD : forall v q0, cview v = (0%nat, Some q0) ->
  Cin v = cden (Ap_Alph_01_11_011 q0 ++ []) [] 0 AIZ0_1RB0LC_1LC1RD_0RD1LA_1LC1RD.
Proof.
  intros v q0 E. destruct (Alph_01_11_011.cview_some_Alph_01_11_011 v 0 q0 E) as (H1 & _).
  unfold Cin_1RB0LC_1LC1RD_0RD1LA_1LC1RD, cden, AIZ0_1RB0LC_1LC1RD_0RD1LA_1LC1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  rewrite H1. cbn [rep app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?app_nil_r. reflexivity.
Qed.

Lemma genz_1RB0LC_1LC1RD_0RD1LA_1LC1RD : forall v q0, cview v = (0%nat, Some q0) ->
  lift (cden (Ap_Alph_01_11_011 q0 ++ []) [] 0 AIZ1_1RB0LC_1LC1RD_0RD1LA_1LC1RD) = lift (Cin (Pos.succ v)).
Proof.
  intros v q0 E. destruct (Alph_01_11_011.cview_some_Alph_01_11_011 v 0 q0 E) as (_ & H2).
  unfold Cin_1RB0LC_1LC1RD_0RD1LA_1LC1RD, cden, AIZ1_1RB0LC_1LC1RD_0RD1LA_1LC1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  cbn [rep app]. rewrite ?app_nil_r.
  rewrite H2. first [ reflexivity
        | cbn [rep app]; rewrite <- ?app_assoc; cbn [app];
          rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gsnp_1RB0LC_1LC1RD_0RD1LA_1LC1RD : forall v i q0, cview v = (S i, Some q0) ->
  Cin v = cden (Ap_Alph_01_11_011 q0 ++ []) [] i AIP0_1RB0LC_1LC1RD_0RD1LA_1LC1RD.
Proof.
  intros v i q0 E. destruct (Alph_01_11_011.cview_some_Alph_01_11_011 v (S i) q0 E) as (H1 & _).
  unfold Cin_1RB0LC_1LC1RD_0RD1LA_1LC1RD, cden, AIP0_1RB0LC_1LC1RD_0RD1LA_1LC1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. cbn [rep app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?app_nil_r. reflexivity.
Qed.

Lemma genp_1RB0LC_1LC1RD_0RD1LA_1LC1RD : forall v i q0, cview v = (S i, Some q0) ->
  lift (cden (Ap_Alph_01_11_011 q0 ++ []) [] i AIP1_1RB0LC_1LC1RD_0RD1LA_1LC1RD) = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (Alph_01_11_011.cview_some_Alph_01_11_011 v (S i) q0 E) as (_ & H2).
  unfold Cin_1RB0LC_1LC1RD_0RD1LA_1LC1RD, cden, AIP1_1RB0LC_1LC1RD_0RD1LA_1LC1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H2. cbn [rep app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?app_nil_r. reflexivity.
Qed.

Lemma lapin_1RB0LC_1LC1RD_0RD1LA_1LC1RD : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E. destruct i as [|i'].
  - exists (0 * 0 + 2), (cden (Ap_Alph_01_11_011 q0 ++ []) [] 0 AIZ1_1RB0LC_1LC1RD_0RD1LA_1LC1RD).
    split; [lia|]. split; [| exact (genz_1RB0LC_1LC1RD_0RD1LA_1LC1RD v q0 E)].
    rewrite (gsnz_1RB0LC_1LC1RD_0RD1LA_1LC1RD v q0 E).
    exact (srun_sound tm false true chnz_1RB0LC_1LC1RD_0RD1LA_1LC1RD AIZ0_1RB0LC_1LC1RD_0RD1LA_1LC1RD AIZ1_1RB0LC_1LC1RD_0RD1LA_1LC1RD 0 2
             run_innerz_1RB0LC_1LC1RD_0RD1LA_1LC1RD (Ap_Alph_01_11_011 q0 ++ []) [] 0
             ltac:(discriminate) ltac:(reflexivity)).
  - exists (4 * i' + 6), (cden (Ap_Alph_01_11_011 q0 ++ []) [] i' AIP1_1RB0LC_1LC1RD_0RD1LA_1LC1RD).
    split; [lia|]. split; [| exact (genp_1RB0LC_1LC1RD_0RD1LA_1LC1RD v i' q0 E)].
    rewrite (gsnp_1RB0LC_1LC1RD_0RD1LA_1LC1RD v i' q0 E).
    exact (srun_sound tm false true chnp_1RB0LC_1LC1RD_0RD1LA_1LC1RD AIP0_1RB0LC_1LC1RD_0RD1LA_1LC1RD AIP1_1RB0LC_1LC1RD_0RD1LA_1LC1RD 4 6
             run_innerp_1RB0LC_1LC1RD_0RD1LA_1LC1RD (Ap_Alph_01_11_011 q0 ++ []) [] i'
             ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The boot lands in the SHIFT1 frame (the unit rotated one cell against
    the block frame), up to 0/0 trailing blanks; [rrc_] bridges. *)
Lemma gbo_1RB0LC_1LC1RD_0RD1LA_1LC1RD : forall j, lift (cden [] [] j BB1_1RB0LC_1LC1RD_0RD1LA_1LC1RD) = lift (Cin (xO (xI (pow2 j)))).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_1RB0LC_1LC1RD_0RD1LA_1LC1RD = (StC, ([S0;S1;S1] ++ rep [S1;S0] j ++ [S1;S0;S1;S1], S0, []))).
  { unfold cden, BB1_1RB0LC_1LC1RD_0RD1LA_1LC1RD, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (j + 1) by lia.
    rewrite rep_add. cbn [rep app]. rewrite ?app_nil_r.
    rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin (xO (xI (pow2 j))) = (StC, ([S0;S1;S1] ++ rep [S1;S0] j ++ [S1;S0;S1;S1], S0, []))).
  { unfold Cin_1RB0LC_1LC1RD_0RD1LA_1LC1RD. rewrite epre_1RB0LC_1LC1RD_0RD1LA_1LC1RD.
    cbn [app]. rewrite <- ?app_assoc. cbn [app].
    rewrite (rrc_1RB0LC_1LC1RD_0RD1LA_1LC1RD S1 [S0] j).
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  rewrite HD, HC. cbn [app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?lbl_1RB0LC_1LC1RD_0RD1LA_1LC1RD. rewrite ?lift_app_blank. reflexivity.
Qed.

(** The exit chain starts from the REPHASED fill (one unit cell rotated out
    front); [rrc_] bridges it back to the encoding's block frame. *)
Lemma gxi_1RB0LC_1LC1RD_0RD1LA_1LC1RD : forall j, Cin (fill (xO (xI (pow2 j)))) = cden [] [] j BE0_1RB0LC_1LC1RD_0RD1LA_1LC1RD.
Proof.
  intro j.
  assert (Hf : fill (xO (xI (pow2 j))) = fill (pow2 (S (S j))))
    by (cbn [pow2 fill]; reflexivity).
  rewrite Hf.
  destruct (Alph_01_11_011.cview_none_Alph_01_11_011 (fill (pow2 (S (S j)))) (S (S j))
              (cview_fill_pow2 (S (S j)))) as (H1 & _).
  unfold Cin_1RB0LC_1LC1RD_0RD1LA_1LC1RD, cden, BE0_1RB0LC_1LC1RD_0RD1LA_1LC1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 1) with (S j) by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1.
  cbn [app]. rewrite <- ?app_assoc. cbn [app].
  rewrite (rrc_1RB0LC_1LC1RD_0RD1LA_1LC1RD S1 [S1] (S j)).
  cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
  reflexivity.
Qed.

(** The interior lap, restated up to [lift] -- what [vis_via_ovf_lift] and
    [vis_via_fill] consume. *)
Lemma lapil_1RB0LC_1LC1RD_0RD1LA_1LC1RD : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof. intros p j q0 E. destruct (lapi_1RB0LC_1LC1RD_0RD1LA_1LC1RD p j q0 E) as (n & Hn & Hr).
  exists n, (Cc (Pos.succ p)).
  split; [exact Hn | split; [exact Hr | reflexivity]]. Qed.

(** [cview p = (1, None)] forces [p = 1], where the offset family's count is
    empty: the overflow lap at p = 1 is ONE CONCRETE run, checked the way the
    bootstrap lemma is. *)
Lemma lapo0_1RB0LC_1LC1RD_0RD1LA_1LC1RD : exists n c', csteps tm n (Cc 1) = Some c'
    /\ lift c' = lift (Cc 2) /\ 0 < n.
Proof.
  exists 13.
  assert (H : match csteps tm 13 (Cc 1) with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 13 (Cc 1)) as [c|] eqn:E0; [|discriminate].
  exists c. split; [reflexivity|]. split; [apply ceqb_lift; exact H | lia].
Qed.

(** The outer OVERFLOW branch.  The offset family's block count is one short
    of the outer index, so the branch REINDEXES: the generic route runs at
    [j = S j'] and [j = 0] is the concrete lap above. *)
Lemma lapo_1RB0LC_1LC1RD_0RD1LA_1LC1RD : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E.
  destruct j as [|j'].
  - rewrite (cview_none_shape p 0 E). exact lapo0_1RB0LC_1LC1RD_0RD1LA_1LC1RD.
  - apply (nested_overflow_lift tm Cc Cin lapin_1RB0LC_1LC1RD_0RD1LA_1LC1RD p (xO (xI (pow2 j')))).
    + exists (4 * j' + 17), (cden [] [] j' BB1_1RB0LC_1LC1RD_0RD1LA_1LC1RD).
      split; [lia|]. split; [| exact (gbo_1RB0LC_1LC1RD_0RD1LA_1LC1RD j')].
      rewrite (gso_1RB0LC_1LC1RD_0RD1LA_1LC1RD p j' E).
      exact (srun_sound tm true true chb_1RB0LC_1LC1RD_0RD1LA_1LC1RD B0_1RB0LC_1LC1RD_0RD1LA_1LC1RD BB1_1RB0LC_1LC1RD_0RD1LA_1LC1RD 4 17
               run_boot_1RB0LC_1LC1RD_0RD1LA_1LC1RD [] [] j' ltac:(reflexivity) ltac:(reflexivity)).
    + exists (4 * j' + 10), (cden [] [] j' B1_1RB0LC_1LC1RD_0RD1LA_1LC1RD).
      split; [| exact (geo_1RB0LC_1LC1RD_0RD1LA_1LC1RD p j' E)].
      rewrite (gxi_1RB0LC_1LC1RD_0RD1LA_1LC1RD j').
      exact (srun_sound tm true true che_1RB0LC_1LC1RD_0RD1LA_1LC1RD BE0_1RB0LC_1LC1RD_0RD1LA_1LC1RD B1_1RB0LC_1LC1RD_0RD1LA_1LC1RD 4 10
               run_exit_1RB0LC_1LC1RD_0RD1LA_1LC1RD [] [] j' ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** State StA's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StA_1RB0LC_1LC1RD_0RD1LA_1LC1RD : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StA.
Proof. exists 6. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StB's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StB_1RB0LC_1LC1RD_0RD1LA_1LC1RD : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StB.
Proof. exists 9. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StC's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StC_1RB0LC_1LC1RD_0RD1LA_1LC1RD : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StC.
Proof. exists 0. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StD's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StD_1RB0LC_1LC1RD_0RD1LA_1LC1RD : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StD.
Proof. exists 1. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.



(** ** The lap *)

Lemma lap_1RB0LC_1LC1RD_0RD1LA_1LC1RD : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB0LC_1LC1RD_0RD1LA_1LC1RD p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->). exact (lapo_1RB0LC_1LC1RD_0RD1LA_1LC1RD p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_1RB0LC_1LC1RD_0RD1LA_1LC1RD : exists t0, stepn tm t0 InitES = Some (lift (Cc 2)).
Proof.
  exists 15.
  assert (H : match csteps tm 15 c0 with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 15 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma viso_1RB0LC_1LC1RD_0RD1LA_1LC1RD : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_1RB0LC_1LC1RD_0RD1LA_1LC1RD = Some q ->
  forall p j, cview p = (S (S j), None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_1RB0LC_1LC1RD_0RD1LA_1LC1RD p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB0LC_1LC1RD_0RD1LA_1LC1RD p j E)].
Qed.

Lemma vis_1RB0LC_1LC1RD_0RD1LA_1LC1RD : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_1RB0LC_1LC1RD_0RD1LA_1LC1RD.
  destruct q.

  - (* StA *)
    apply (vis_via_ovf tm Cc Hi StA).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1). exact visz_StA_1RB0LC_1LC1RD_0RD1LA_1LC1RD.
    + exact (viso_1RB0LC_1LC1RD_0RD1LA_1LC1RD [SWin 2; SCycL 2 0; SWin 4] StA ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* StB *)
    apply (vis_via_ovf tm Cc Hi StB).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1). exact visz_StB_1RB0LC_1LC1RD_0RD1LA_1LC1RD.
    + exact (viso_1RB0LC_1LC1RD_0RD1LA_1LC1RD [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 3] StB ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* StC: the anchor state *)
    exists 0. eexists. split; reflexivity.
  - (* StD *)
    apply (vis_via_ovf tm Cc Hi StD).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1). exact visz_StD_1RB0LC_1LC1RD_0RD1LA_1LC1RD.
    + exact (viso_1RB0LC_1LC1RD_0RD1LA_1LC1RD [SWin 1] StD ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
Qed.

Theorem nqhm_1RB0LC_1LC1RD_0RD1LA_1LC1RD : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 2). - exact boot_1RB0LC_1LC1RD_0RD1LA_1LC1RD. - intros p _. apply lap_1RB0LC_1LC1RD_0RD1LA_1LC1RD. - intros p q _. apply vis_1RB0LC_1LC1RD_0RD1LA_1LC1RD. Qed.

Theorem nqh_1RB0LC_1LC1RD_0RD1LA_1LC1RD : NeverQuasiHaltsSt tm_1RB0LC_1LC1RD_0RD1LA_1LC1RD.
Proof. apply (mirror_never_qh tm_1RB0LC_1LC1RD_0RD1LA_1LC1RD). rewrite mirror_ok_1RB0LC_1LC1RD_0RD1LA_1LC1RD. exact nqhm_1RB0LC_1LC1RD_0RD1LA_1LC1RD. Qed.

Theorem nonhalt_1RB0LC_1LC1RD_0RD1LA_1LC1RD : NonHalt tm_1RB0LC_1LC1RD_0RD1LA_1LC1RD.
Proof. apply never_qh_nonhalt, nqh_1RB0LC_1LC1RD_0RD1LA_1LC1RD. Qed.
