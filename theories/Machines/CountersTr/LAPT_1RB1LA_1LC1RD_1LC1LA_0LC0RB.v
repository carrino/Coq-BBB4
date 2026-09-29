(** * LAPT_1RB1LA_1LC1RD_1LC1LA_0LC0RB: TRANSITION-LEVEL board for machine 1RB1LA_1LC1RD_1LC1LA_0LC0RB, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Ap_Alph_10_11_11 digit alphabet (Alph_10_11_11.v), anchored at

      Cc p = (StD, (Ap_Alph_10_11_11 p ++ [S1;S1;S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  j=0: 4 ; j=S j': 4*j'+8 steps
      overflow  (cview p = (S j, None)):   boot 4*j+21, then the inner counter's own laps to the
                                           all-ones fill, then exit 4*j+12

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 192 interior anchors (interior); offset c=2: 7 overflow phases, j = 1..7 (487 inner laps), plus the concrete j=0 lap (nested overflow).
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter Alph_10_11_11 LapCertGlue LapCertGlueLift IXPGadgets NestedLap NestedLapLift ILCounter.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
From BBB4 Require Import BBBT4_Statement.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
Import ListNotations.

Definition mk_1RB1LA_1LC1RD_1LC1LA_0LC0RB (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1LA_1LC1RD_1LC1LA_0LC0RB.

(** 1RB1LA_1LC1RD_1LC1LA_0LC0RB *)
Definition tm_1RB1LA_1LC1RD_1LC1LA_0LC0RB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StA
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S1 DL StC | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S0 DL StC | StD, S1 => mk S0 DR StB end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_1RB1LA_1LC1RD_1LC1LA_0LC0RB : list Instr := [].
Definition tmw_1RB1LA_1LC1RD_1LC1LA_0LC0RB : TM := tm_wrap_trs tm_1RB1LA_1LC1RD_1LC1LA_0LC0RB pins_1RB1LA_1LC1RD_1LC1LA_0LC0RB.
Local Notation tm := tmw_1RB1LA_1LC1RD_1LC1LA_0LC0RB.

Definition Cc_1RB1LA_1LC1RD_1LC1LA_0LC0RB (p : positive) : cconf := (StD, (Ap_Alph_10_11_11 p ++ [S1;S1;S0], S0, [])).
Local Notation Cc := Cc_1RB1LA_1LC1RD_1LC1LA_0LC0RB.

(** ** The certificate *)

(** j = 0: the repeated block is absent, so the whole lap is concrete. *)
Definition Z0_1RB1LA_1LC1RD_1LC1LA_0LC0RB : sconf := mkC StD (mkS [S1;S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition Z1_1RB1LA_1LC1RD_1LC1LA_0LC0RB : sconf := mkC StD (mkS [S1;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition chz_1RB1LA_1LC1RD_1LC1LA_0LC0RB : list lstep := [SWin 4].

Lemma run_z_1RB1LA_1LC1RD_1LC1LA_0LC0RB : srun tm false true chz_1RB1LA_1LC1RD_1LC1LA_0LC0RB Z0_1RB1LA_1LC1RD_1LC1LA_0LC0RB = Some (Z1_1RB1LA_1LC1RD_1LC1LA_0LC0RB, 0, 4).
Proof. vm_compute. reflexivity. Qed.

(** j = S j': one copy of the unit sits in the PREFIX, so the head always has
    a concrete cell to step onto. *)
Definition P0_1RB1LA_1LC1RD_1LC1LA_0LC0RB : sconf := mkC StD (mkS [S1;S1] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition P1_1RB1LA_1LC1RD_1LC1LA_0LC0RB : sconf := mkC StD (mkS [S1;S0] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chp_1RB1LA_1LC1RD_1LC1LA_0LC0RB : list lstep := [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 2].

Lemma run_p_1RB1LA_1LC1RD_1LC1LA_0LC0RB : srun tm false true chp_1RB1LA_1LC1RD_1LC1LA_0LC0RB P0_1RB1LA_1LC1RD_1LC1LA_0LC0RB = Some (P1_1RB1LA_1LC1RD_1LC1LA_0LC0RB, 4, 8).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB1LA_1LC1RD_1LC1LA_0LC0RB : sconf := mkC StD (mkS [] [S1;S1] 1 1 [S1;S1;S1;S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_1RB1LA_1LC1RD_1LC1LA_0LC0RB : sconf := mkC StD (mkS [] [S1;S0] 1 2 [S1;S1;S1;S1]) S0 (mkS [] [] 0 0 []).
(** ** The INNER anchor family -- Ip at StD *)
Definition Cin_1RB1LA_1LC1RD_1LC1LA_0LC0RB (v : positive) : cconf := (StD, (Ip v ++ [S0;S1;S1], S0, [])).
Local Notation Cin := Cin_1RB1LA_1LC1RD_1LC1LA_0LC0RB.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow2_1RB1LA_1LC1RD_1LC1LA_0LC0RB : forall n, Ip (pow2 n) = rep [S1;S0] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap, SPLIT: the carry sweep's period sits one cell
    into the unit, so i = 0 is one concrete window and i = S i' runs with a
    unit PEELED into the prefix (count i' = i - 1) -- the interior-lap
    mirror of the outer j = 0 split. *)
Definition AIZ0_1RB1LA_1LC1RD_1LC1LA_0LC0RB : sconf := mkC StD (mkS [S1;S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition AIZ1_1RB1LA_1LC1RD_1LC1LA_0LC0RB : sconf := mkC StD (mkS [S1;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition chnz_1RB1LA_1LC1RD_1LC1LA_0LC0RB : list lstep := [SWin 4].

Lemma run_innerz_1RB1LA_1LC1RD_1LC1LA_0LC0RB : srun tm false true chnz_1RB1LA_1LC1RD_1LC1LA_0LC0RB AIZ0_1RB1LA_1LC1RD_1LC1LA_0LC0RB = Some (AIZ1_1RB1LA_1LC1RD_1LC1LA_0LC0RB, 0, 4).
Proof. vm_compute. reflexivity. Qed.

Definition AIP0_1RB1LA_1LC1RD_1LC1LA_0LC0RB : sconf := mkC StD (mkS [S1;S1] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition AIP1_1RB1LA_1LC1RD_1LC1LA_0LC0RB : sconf := mkC StD (mkS [S1;S0] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chnp_1RB1LA_1LC1RD_1LC1LA_0LC0RB : list lstep := [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 2].

Lemma run_innerp_1RB1LA_1LC1RD_1LC1LA_0LC0RB : srun tm false true chnp_1RB1LA_1LC1RD_1LC1LA_0LC0RB AIP0_1RB1LA_1LC1RD_1LC1LA_0LC0RB = Some (AIP1_1RB1LA_1LC1RD_1LC1LA_0LC0RB, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** The OFFSET start: [E (2^(n+2)+2)] is fixed digit blocks, then the rep.
    Its block count is one short of the outer index, which is why [lapo_]
    below REINDEXES at [j = S j']. *)
Lemma epre_1RB1LA_1LC1RD_1LC1LA_0LC0RB : forall n, Ip (xO (xI (pow2 n))) = [S1;S0;S1;S1] ++ rep [S1;S0] n ++ [S1].
Proof.
  intro n. cbn [Ip]. rewrite epow2_1RB1LA_1LC1RD_1LC1LA_0LC0RB.
  cbn [app]. rewrite <- ?app_assoc. cbn [app]. reflexivity.
Qed.

(** Rotating one fixed cell across a rep -- the bridge between a chain's
    natural landing frame and the encoding's block frame ([WTape.rep_rot],
    with the trailing cell fused into the tail). *)
Lemma rrc_1RB1LA_1LC1RD_1LC1LA_0LC0RB : forall (x : Sym) (u : list Sym) k (Y : list Sym),
  rep (x :: u) k ++ x :: Y = x :: rep (u ++ [x]) k ++ Y.
Proof.
  intros. change (x :: Y) with ([x] ++ Y). rewrite app_assoc, <- rep_rot.
  cbn [app]. rewrite <- ?app_assoc. reflexivity.
Qed.

(** *** boot: the outer overflow anchor -> the first inner anchor at [pow2 j] *)
Definition BB1_1RB1LA_1LC1RD_1LC1LA_0LC0RB : sconf := mkC StD (mkS [S1;S0;S1;S1] [S1;S0] 1 1 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chb_1RB1LA_1LC1RD_1LC1LA_0LC0RB : list lstep := [SRotL 1; SWin 1; SRotL 1; SWin 1; SCycL 2 0; SWin 6; SCycR 2; SWin 4; SRotL 1; SWin 4; SWinR 1].

Lemma run_boot_1RB1LA_1LC1RD_1LC1LA_0LC0RB : srun tm true true chb_1RB1LA_1LC1RD_1LC1LA_0LC0RB B0_1RB1LA_1LC1RD_1LC1LA_0LC0RB = Some (BB1_1RB1LA_1LC1RD_1LC1LA_0LC0RB, 4, 21).
Proof. vm_compute. reflexivity. Qed.

(** *** exit: the last inner all-ones fill -> the outer successor *)
Definition BE0_1RB1LA_1LC1RD_1LC1LA_0LC0RB : sconf := mkC StD (mkS [S1] [S1;S1] 1 1 [S1;S1;S0;S1;S1]) S0 (mkS [] [] 0 0 []).
Definition che_1RB1LA_1LC1RD_1LC1LA_0LC0RB : list lstep := [SWin 1; SRotL 1; SWin 1; SCycL 2 0; SWin 4; SCycR 2; SWin 2; SFoldL 1].

Lemma run_exit_1RB1LA_1LC1RD_1LC1LA_0LC0RB : srun tm true true che_1RB1LA_1LC1RD_1LC1LA_0LC0RB BE0_1RB1LA_1LC1RD_1LC1LA_0LC0RB = Some (B1_1RB1LA_1LC1RD_1LC1LA_0LC0RB, 4, 12).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gz_1RB1LA_1LC1RD_1LC1LA_0LC0RB : forall p q0, cview p = (0, Some q0) ->
  Cc p = cden (Ap_Alph_10_11_11 q0 ++ [S1;S1;S0]) [] 0 Z0_1RB1LA_1LC1RD_1LC1LA_0LC0RB /\
  cden (Ap_Alph_10_11_11 q0 ++ [S1;S1;S0]) [] 0 Z1_1RB1LA_1LC1RD_1LC1LA_0LC0RB = Cc (Pos.succ p).
Proof.
  intros p q0 E. destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p 0 q0 E) as (H1 & H2).
  unfold Cc_1RB1LA_1LC1RD_1LC1LA_0LC0RB, cden, Z0_1RB1LA_1LC1RD_1LC1LA_0LC0RB, Z1_1RB1LA_1LC1RD_1LC1LA_0LC0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gp_1RB1LA_1LC1RD_1LC1LA_0LC0RB : forall p j q0, cview p = (S j, Some q0) ->
  Cc p = cden (Ap_Alph_10_11_11 q0 ++ [S1;S1;S0]) [] j P0_1RB1LA_1LC1RD_1LC1LA_0LC0RB /\
  cden (Ap_Alph_10_11_11 q0 ++ [S1;S1;S0]) [] j P1_1RB1LA_1LC1RD_1LC1LA_0LC0RB = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p (S j) q0 E) as (H1 & H2).
  unfold Cc_1RB1LA_1LC1RD_1LC1LA_0LC0RB, cden, P0_1RB1LA_1LC1RD_1LC1LA_0LC0RB, P1_1RB1LA_1LC1RD_1LC1LA_0LC0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB1LA_1LC1RD_1LC1LA_0LC0RB : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct j as [|j'].
  - destruct (gz_1RB1LA_1LC1RD_1LC1LA_0LC0RB p q0 E) as (HA & HB).
    exists (0 * 0 + 4). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chz_1RB1LA_1LC1RD_1LC1LA_0LC0RB Z0_1RB1LA_1LC1RD_1LC1LA_0LC0RB Z1_1RB1LA_1LC1RD_1LC1LA_0LC0RB 0 4
               run_z_1RB1LA_1LC1RD_1LC1LA_0LC0RB (Ap_Alph_10_11_11 q0 ++ [S1;S1;S0]) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gp_1RB1LA_1LC1RD_1LC1LA_0LC0RB p j' q0 E) as (HA & HB).
    exists (4 * j' + 8). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chp_1RB1LA_1LC1RD_1LC1LA_0LC0RB P0_1RB1LA_1LC1RD_1LC1LA_0LC0RB P1_1RB1LA_1LC1RD_1LC1LA_0LC0RB 4 8
               run_p_1RB1LA_1LC1RD_1LC1LA_0LC0RB (Ap_Alph_10_11_11 q0 ++ [S1;S1;S0]) [] j'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
Qed.

Lemma gso_1RB1LA_1LC1RD_1LC1LA_0LC0RB : forall p j, cview p = (S (S j), None) ->
  Cc p = cden [] [] j B0_1RB1LA_1LC1RD_1LC1LA_0LC0RB.
Proof.
  intros p j E. destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p (S j) E) as (H1 & _).
  unfold Cc_1RB1LA_1LC1RD_1LC1LA_0LC0RB, cden, B0_1RB1LA_1LC1RD_1LC1LA_0LC0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 1) with ((S j)) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB1LA_1LC1RD_1LC1LA_0LC0RB : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB1LA_1LC1RD_1LC1LA_0LC0RB : forall p j, cview p = (S (S j), None) ->
  lift (cden [] [] j B1_1RB1LA_1LC1RD_1LC1LA_0LC0RB) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p (S j) E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB1LA_1LC1RD_1LC1LA_0LC0RB
             = (StD, (rep [S1;S0] (S (S j)) ++ [S1;S1;S1;S1], S0, []))).
  { unfold cden, B1_1RB1LA_1LC1RD_1LC1LA_0LC0RB, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 2) with (S (S j)) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StD, ((rep [S1;S0] (S (S j)) ++ [S1;S1;S1;S1]) ++ [S0], S0, []))).
  { unfold Cc_1RB1LA_1LC1RD_1LC1LA_0LC0RB. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_1RB1LA_1LC1RD_1LC1LA_0LC0RB. reflexivity.
Qed.

Lemma gsnz_1RB1LA_1LC1RD_1LC1LA_0LC0RB : forall v q0, cview v = (0%nat, Some q0) ->
  Cin v = cden (Ip q0 ++ [S0;S1;S1]) [] 0 AIZ0_1RB1LA_1LC1RD_1LC1LA_0LC0RB.
Proof.
  intros v q0 E. destruct (ILCounter.cview_some_I v 0 q0 E) as (H1 & _).
  unfold Cin_1RB1LA_1LC1RD_1LC1LA_0LC0RB, cden, AIZ0_1RB1LA_1LC1RD_1LC1LA_0LC0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  rewrite H1. cbn [rep app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?app_nil_r. reflexivity.
Qed.

Lemma genz_1RB1LA_1LC1RD_1LC1LA_0LC0RB : forall v q0, cview v = (0%nat, Some q0) ->
  lift (cden (Ip q0 ++ [S0;S1;S1]) [] 0 AIZ1_1RB1LA_1LC1RD_1LC1LA_0LC0RB) = lift (Cin (Pos.succ v)).
Proof.
  intros v q0 E. destruct (ILCounter.cview_some_I v 0 q0 E) as (_ & H2).
  unfold Cin_1RB1LA_1LC1RD_1LC1LA_0LC0RB, cden, AIZ1_1RB1LA_1LC1RD_1LC1LA_0LC0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  cbn [rep app]. rewrite ?app_nil_r.
  rewrite H2. first [ reflexivity
        | cbn [rep app]; rewrite <- ?app_assoc; cbn [app];
          rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gsnp_1RB1LA_1LC1RD_1LC1LA_0LC0RB : forall v i q0, cview v = (S i, Some q0) ->
  Cin v = cden (Ip q0 ++ [S0;S1;S1]) [] i AIP0_1RB1LA_1LC1RD_1LC1LA_0LC0RB.
Proof.
  intros v i q0 E. destruct (ILCounter.cview_some_I v (S i) q0 E) as (H1 & _).
  unfold Cin_1RB1LA_1LC1RD_1LC1LA_0LC0RB, cden, AIP0_1RB1LA_1LC1RD_1LC1LA_0LC0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. cbn [rep app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?app_nil_r. reflexivity.
Qed.

Lemma genp_1RB1LA_1LC1RD_1LC1LA_0LC0RB : forall v i q0, cview v = (S i, Some q0) ->
  lift (cden (Ip q0 ++ [S0;S1;S1]) [] i AIP1_1RB1LA_1LC1RD_1LC1LA_0LC0RB) = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (ILCounter.cview_some_I v (S i) q0 E) as (_ & H2).
  unfold Cin_1RB1LA_1LC1RD_1LC1LA_0LC0RB, cden, AIP1_1RB1LA_1LC1RD_1LC1LA_0LC0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H2. cbn [rep app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?app_nil_r. reflexivity.
Qed.

Lemma lapin_1RB1LA_1LC1RD_1LC1LA_0LC0RB : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E. destruct i as [|i'].
  - exists (0 * 0 + 4), (cden (Ip q0 ++ [S0;S1;S1]) [] 0 AIZ1_1RB1LA_1LC1RD_1LC1LA_0LC0RB).
    split; [lia|]. split; [| exact (genz_1RB1LA_1LC1RD_1LC1LA_0LC0RB v q0 E)].
    rewrite (gsnz_1RB1LA_1LC1RD_1LC1LA_0LC0RB v q0 E).
    exact (srun_sound tm false true chnz_1RB1LA_1LC1RD_1LC1LA_0LC0RB AIZ0_1RB1LA_1LC1RD_1LC1LA_0LC0RB AIZ1_1RB1LA_1LC1RD_1LC1LA_0LC0RB 0 4
             run_innerz_1RB1LA_1LC1RD_1LC1LA_0LC0RB (Ip q0 ++ [S0;S1;S1]) [] 0
             ltac:(discriminate) ltac:(reflexivity)).
  - exists (4 * i' + 8), (cden (Ip q0 ++ [S0;S1;S1]) [] i' AIP1_1RB1LA_1LC1RD_1LC1LA_0LC0RB).
    split; [lia|]. split; [| exact (genp_1RB1LA_1LC1RD_1LC1LA_0LC0RB v i' q0 E)].
    rewrite (gsnp_1RB1LA_1LC1RD_1LC1LA_0LC0RB v i' q0 E).
    exact (srun_sound tm false true chnp_1RB1LA_1LC1RD_1LC1LA_0LC0RB AIP0_1RB1LA_1LC1RD_1LC1LA_0LC0RB AIP1_1RB1LA_1LC1RD_1LC1LA_0LC0RB 4 8
             run_innerp_1RB1LA_1LC1RD_1LC1LA_0LC0RB (Ip q0 ++ [S0;S1;S1]) [] i'
             ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The boot lands on the OFFSET inner anchor up to 0/0 trailing
    blanks. *)
Lemma gbo_1RB1LA_1LC1RD_1LC1LA_0LC0RB : forall j, lift (cden [] [] j BB1_1RB1LA_1LC1RD_1LC1LA_0LC0RB) = lift (Cin (xO (xI (pow2 j)))).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_1RB1LA_1LC1RD_1LC1LA_0LC0RB = (StD, ([S1;S0;S1;S1] ++ rep [S1;S0] j ++ [S1;S0;S1;S1], S0, []))).
  { unfold cden, BB1_1RB1LA_1LC1RD_1LC1LA_0LC0RB, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (j + 1) by lia.
    rewrite rep_add. cbn [rep app]. rewrite ?app_nil_r.
    rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin (xO (xI (pow2 j))) = (StD, ([S1;S0;S1;S1] ++ rep [S1;S0] j ++ [S1;S0;S1;S1], S0, []))).
  { unfold Cin_1RB1LA_1LC1RD_1LC1LA_0LC0RB. rewrite epre_1RB1LA_1LC1RD_1LC1LA_0LC0RB.
    first [ rewrite <- ?app_assoc; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  (* The offset boot can land one written blank past the anchor on EITHER
     side, and [lift] sees neither.  Strip it FIRST: [cbn [app]] flattens
     `w ++ [S0]` into one literal and destroys the shape
     [WTape.lift_app_blank_l] matches on. *)
  rewrite HD, HC. rewrite ?lift_app_blank_l.
  cbn [app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?lbl_1RB1LA_1LC1RD_1LC1LA_0LC0RB. rewrite ?lift_app_blank. reflexivity.
Qed.

(** The exit chain starts from the REPHASED fill (one unit cell rotated out
    front); [rrc_] bridges it back to the encoding's block frame. *)
Lemma gxi_1RB1LA_1LC1RD_1LC1LA_0LC0RB : forall j, Cin (fill (xO (xI (pow2 j)))) = cden [] [] j BE0_1RB1LA_1LC1RD_1LC1LA_0LC0RB.
Proof.
  intro j.
  assert (Hf : fill (xO (xI (pow2 j))) = fill (pow2 (S (S j))))
    by (cbn [pow2 fill]; reflexivity).
  rewrite Hf.
  destruct (ILCounter.cview_none_I (fill (pow2 (S (S j)))) (S (S j))
              (cview_fill_pow2 (S (S j)))) as (H1 & _).
  unfold Cin_1RB1LA_1LC1RD_1LC1LA_0LC0RB, cden, BE0_1RB1LA_1LC1RD_1LC1LA_0LC0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 1) with (S j) by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1.
  cbn [app]. rewrite <- ?app_assoc. cbn [app].
  rewrite (rrc_1RB1LA_1LC1RD_1LC1LA_0LC0RB S1 [S1] (S j)).
  cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
  reflexivity.
Qed.

(** The interior lap, restated up to [lift] -- what [vis_via_ovf_lift] and
    [vis_via_fill] consume. *)
Lemma lapil_1RB1LA_1LC1RD_1LC1LA_0LC0RB : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof. intros p j q0 E. destruct (lapi_1RB1LA_1LC1RD_1LC1LA_0LC0RB p j q0 E) as (n & Hn & Hr).
  exists n, (Cc (Pos.succ p)).
  split; [exact Hn | split; [exact Hr | reflexivity]]. Qed.

(** [cview p = (1, None)] forces [p = 1], where the offset family's count is
    empty: the overflow lap at p = 1 is ONE CONCRETE run, checked the way the
    bootstrap lemma is. *)
Lemma lapo0_1RB1LA_1LC1RD_1LC1LA_0LC0RB : exists n c', csteps tm n (Cc 1) = Some c'
    /\ lift c' = lift (Cc 2) /\ 0 < n.
Proof.
  exists 17.
  assert (H : match csteps tm 17 (Cc 1) with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 17 (Cc 1)) as [c|] eqn:E0; [|discriminate].
  exists c. split; [reflexivity|]. split; [apply ceqb_lift; exact H | lia].
Qed.

(** The outer OVERFLOW branch.  The offset family's block count is one short
    of the outer index, so the branch REINDEXES: the generic route runs at
    [j = S j'] and [j = 0] is the concrete lap above. *)
Lemma lapo_1RB1LA_1LC1RD_1LC1LA_0LC0RB : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E.
  destruct j as [|j'].
  - rewrite (cview_none_shape p 0 E). exact lapo0_1RB1LA_1LC1RD_1LC1LA_0LC0RB.
  - apply (nested_overflow_lift tm Cc Cin lapin_1RB1LA_1LC1RD_1LC1LA_0LC0RB p (xO (xI (pow2 j')))).
    + exists (4 * j' + 21), (cden [] [] j' BB1_1RB1LA_1LC1RD_1LC1LA_0LC0RB).
      split; [lia|]. split; [| exact (gbo_1RB1LA_1LC1RD_1LC1LA_0LC0RB j')].
      rewrite (gso_1RB1LA_1LC1RD_1LC1LA_0LC0RB p j' E).
      exact (srun_sound tm true true chb_1RB1LA_1LC1RD_1LC1LA_0LC0RB B0_1RB1LA_1LC1RD_1LC1LA_0LC0RB BB1_1RB1LA_1LC1RD_1LC1LA_0LC0RB 4 21
               run_boot_1RB1LA_1LC1RD_1LC1LA_0LC0RB [] [] j' ltac:(reflexivity) ltac:(reflexivity)).
    + exists (4 * j' + 12), (cden [] [] j' B1_1RB1LA_1LC1RD_1LC1LA_0LC0RB).
      split; [| exact (geo_1RB1LA_1LC1RD_1LC1LA_0LC0RB p j' E)].
      rewrite (gxi_1RB1LA_1LC1RD_1LC1LA_0LC0RB j').
      exact (srun_sound tm true true che_1RB1LA_1LC1RD_1LC1LA_0LC0RB BE0_1RB1LA_1LC1RD_1LC1LA_0LC0RB B1_1RB1LA_1LC1RD_1LC1LA_0LC0RB 4 12
               run_exit_1RB1LA_1LC1RD_1LC1LA_0LC0RB [] [] j' ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** State StA's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StA_1RB1LA_1LC1RD_1LC1LA_0LC0RB : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StA.
Proof. exists 2. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StB's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StB_1RB1LA_1LC1RD_1LC1LA_0LC0RB : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StB.
Proof. exists 6. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StC's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StC_1RB1LA_1LC1RD_1LC1LA_0LC0RB : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StC.
Proof. exists 1. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StD's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StD_1RB1LA_1LC1RD_1LC1LA_0LC0RB : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StD.
Proof. exists 0. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.



(** ** The lap *)

Lemma lap_1RB1LA_1LC1RD_1LC1LA_0LC0RB : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB1LA_1LC1RD_1LC1LA_0LC0RB p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->). exact (lapo_1RB1LA_1LC1RD_1LC1LA_0LC0RB p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_1RB1LA_1LC1RD_1LC1LA_0LC0RB : exists t0, stepn tm t0 InitES = Some (lift (Cc 2)).
Proof.
  exists 22.
  assert (H : match csteps tm 22 c0 with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 22 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_1RB1LA_1LC1RD_1LC1LA_0LC0RB : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_1RB1LA_1LC1RD_1LC1LA_0LC0RB = Some t ->
  forall p j, cview p = (S (S j), None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_1RB1LA_1LC1RD_1LC1LA_0LC0RB p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB1LA_1LC1RD_1LC1LA_0LC0RB p j E)].
Qed.


(** Instruction A0 at the reindexed branch's p = 1 case -- concrete. *)
Lemma firez_A0_1RB1LA_1LC1RD_1LC1LA_0LC0RB : exists k c, csteps tm k (Cc 1) = Some c /\ cinstr c = (StA, S0).
Proof. exists 5. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** Instruction A1 at the reindexed branch's p = 1 case -- concrete. *)
Lemma firez_A1_1RB1LA_1LC1RD_1LC1LA_0LC0RB : exists k c, csteps tm k (Cc 1) = Some c /\ cinstr c = (StA, S1).
Proof. exists 2. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** Instruction B0 at the reindexed branch's p = 1 case -- concrete. *)
Lemma firez_B0_1RB1LA_1LC1RD_1LC1LA_0LC0RB : exists k c, csteps tm k (Cc 1) = Some c /\ cinstr c = (StB, S0).
Proof. exists 10. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** Instruction B1 at the reindexed branch's p = 1 case -- concrete. *)
Lemma firez_B1_1RB1LA_1LC1RD_1LC1LA_0LC0RB : exists k c, csteps tm k (Cc 1) = Some c /\ cinstr c = (StB, S1).
Proof. exists 6. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** Instruction C0 at the reindexed branch's p = 1 case -- concrete. *)
Lemma firez_C0_1RB1LA_1LC1RD_1LC1LA_0LC0RB : exists k c, csteps tm k (Cc 1) = Some c /\ cinstr c = (StC, S0).
Proof. exists 11. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** Instruction C1 at the reindexed branch's p = 1 case -- concrete. *)
Lemma firez_C1_1RB1LA_1LC1RD_1LC1LA_0LC0RB : exists k c, csteps tm k (Cc 1) = Some c /\ cinstr c = (StC, S1).
Proof. exists 1. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** Instruction D0 at the reindexed branch's p = 1 case -- concrete. *)
Lemma firez_D0_1RB1LA_1LC1RD_1LC1LA_0LC0RB : exists k c, csteps tm k (Cc 1) = Some c /\ cinstr c = (StD, S0).
Proof. exists 0. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** Instruction D1 at the reindexed branch's p = 1 case -- concrete. *)
Lemma firez_D1_1RB1LA_1LC1RD_1LC1LA_0LC0RB : exists k c, csteps tm k (Cc 1) = Some c /\ cinstr c = (StD, S1).
Proof. exists 7. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_1RB1LA_1LC1RD_1LC1LA_0LC0RB : forall t, ~ In t pins_1RB1LA_1LC1RD_1LC1LA_0LC0RB ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_1RB1LA_1LC1RD_1LC1LA_0LC0RB.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_via_ovf tm Cc Hi (StA, S0)).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      exact firez_A0_1RB1LA_1LC1RD_1LC1LA_0LC0RB.
    + exact (fireo_1RB1LA_1LC1RD_1LC1LA_0LC0RB [SRotL 1; SWin 1; SRotL 1; SWin 1; SCycL 2 0; SWin 3] (StA, S0) ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* A1 *)
    apply (fire_via_ovf tm Cc Hi (StA, S1)).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      exact firez_A1_1RB1LA_1LC1RD_1LC1LA_0LC0RB.
    + exact (fireo_1RB1LA_1LC1RD_1LC1LA_0LC0RB [SRotL 1; SWin 1; SRotL 1; SWin 1] (StA, S1) ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* B0 *)
    apply (fire_via_ovf tm Cc Hi (StB, S0)).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      exact firez_B0_1RB1LA_1LC1RD_1LC1LA_0LC0RB.
    + exact (fireo_1RB1LA_1LC1RD_1LC1LA_0LC0RB [SRotL 1; SWin 1; SRotL 1; SWin 1; SCycL 2 0; SWin 6; SCycR 2; SWin 2] (StB, S0) ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* B1 *)
    apply (fire_via_ovf tm Cc Hi (StB, S1)).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      exact firez_B1_1RB1LA_1LC1RD_1LC1LA_0LC0RB.
    + exact (fireo_1RB1LA_1LC1RD_1LC1LA_0LC0RB [SRotL 1; SWin 1; SRotL 1; SWin 1; SCycL 2 0; SWin 4] (StB, S1) ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* C0 *)
    apply (fire_via_ovf tm Cc Hi (StC, S0)).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      exact firez_C0_1RB1LA_1LC1RD_1LC1LA_0LC0RB.
    + exact (fireo_1RB1LA_1LC1RD_1LC1LA_0LC0RB [SRotL 1; SWin 1; SRotL 1; SWin 1; SCycL 2 0; SWin 6; SCycR 2; SWin 3] (StC, S0) ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* C1 *)
    apply (fire_via_ovf tm Cc Hi (StC, S1)).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      exact firez_C1_1RB1LA_1LC1RD_1LC1LA_0LC0RB.
    + exact (fireo_1RB1LA_1LC1RD_1LC1LA_0LC0RB [SRotL 1; SWin 1] (StC, S1) ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* D0 *)
    apply (fire_via_ovf tm Cc Hi (StD, S0)).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      exact firez_D0_1RB1LA_1LC1RD_1LC1LA_0LC0RB.
    + exact (fireo_1RB1LA_1LC1RD_1LC1LA_0LC0RB [] (StD, S0) ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* D1 *)
    apply (fire_via_ovf tm Cc Hi (StD, S1)).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      exact firez_D1_1RB1LA_1LC1RD_1LC1LA_0LC0RB.
    + exact (fireo_1RB1LA_1LC1RD_1LC1LA_0LC0RB [SRotL 1; SWin 1; SRotL 1; SWin 1; SCycL 2 0; SWin 5] (StD, S1) ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
Qed.

Theorem nqhtr_1RB1LA_1LC1RD_1LC1LA_0LC0RB : NeverQuasiHaltsTr tm_1RB1LA_1LC1RD_1LC1LA_0LC0RB.
Proof.
  apply (glue_neverqhtr tm_1RB1LA_1LC1RD_1LC1LA_0LC0RB pins_1RB1LA_1LC1RD_1LC1LA_0LC0RB Cc 2).
  - exact boot_1RB1LA_1LC1RD_1LC1LA_0LC0RB.
  - intros p _. apply lap_1RB1LA_1LC1RD_1LC1LA_0LC0RB.
  - intros t Ht p _. apply fire_1RB1LA_1LC1RD_1LC1LA_0LC0RB. exact Ht.
Qed.

Theorem nonhalt_1RB1LA_1LC1RD_1LC1LA_0LC0RB : NonHalt tm_1RB1LA_1LC1RD_1LC1LA_0LC0RB.
Proof. apply never_qh_tr_nonhalt, nqhtr_1RB1LA_1LC1RD_1LC1LA_0LC0RB. Qed.
