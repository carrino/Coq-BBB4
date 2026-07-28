(** * NLAP_0RB1LA_1RC1LB_0LB1RD_0LA0RC: machine 0RB1LA_1RC1LB_0LB1RD_0LA0RC, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Ap_Alph_10_11_11 digit alphabet (Alph_10_11_11.v), anchored at

      Cc p = (StD, (Ap_Alph_10_11_11 p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  4*j+6 steps
      overflow  (cview p = (S j, None)):   boot 4*j+9, then the inner counter's own laps to the
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
                                  MonoCounter JpCounter Alph_10_11_11 LapCertGlue LapCertGlueLift IXPGadgets NestedLap NestedLapLift ILCounter.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_0RB1LA_1RC1LB_0LB1RD_0LA0RC (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB1LA_1RC1LB_0LB1RD_0LA0RC.

(** 0RB1LA_1RC1LB_0LB1RD_0LA0RC *)
Definition tm_0RB1LA_1RC1LB_0LB1RD_0LA0RC : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S1 DL StA
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S0 DL StB | StC, S1 => mk S1 DR StD
  | StD, S0 => mk S0 DL StA | StD, S1 => mk S0 DR StC end.
Local Notation tm := tm_0RB1LA_1RC1LB_0LB1RD_0LA0RC.

Definition Cc_0RB1LA_1RC1LB_0LB1RD_0LA0RC (p : positive) : cconf := (StD, (Ap_Alph_10_11_11 p ++ [S0], S0, [])).
Local Notation Cc := Cc_0RB1LA_1RC1LB_0LB1RD_0LA0RC.

(** ** The certificate *)

Definition A0_0RB1LA_1RC1LB_0LB1RD_0LA0RC : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition A1_0RB1LA_1RC1LB_0LB1RD_0LA0RC : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chi_0RB1LA_1RC1LB_0LB1RD_0LA0RC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 4; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_int_0RB1LA_1RC1LB_0LB1RD_0LA0RC : srun tm false true chi_0RB1LA_1RC1LB_0LB1RD_0LA0RC A0_0RB1LA_1RC1LB_0LB1RD_0LA0RC = Some (A1_0RB1LA_1RC1LB_0LB1RD_0LA0RC, 4, 6).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB1LA_1RC1LB_0LB1RD_0LA0RC : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_0RB1LA_1RC1LB_0LB1RD_0LA0RC : sconf := mkC StD (mkS [] [S1;S0] 1 1 [S1;S1]) S0 (mkS [] [] 0 0 []).
(** ** The INNER anchor family

    The overflow phase runs a SECOND counter, in the Ip alphabet at
    state StB -- not necessarily the outer one (measured: inner /= outer on
    37% of this bucket, which is why an [Ip]-at-both-levels template derives
    none of it). *)
Definition Cin_0RB1LA_1RC1LB_0LB1RD_0LA0RC (v : positive) : cconf := (StB, (Ip v ++ [S1], S0, [])).
Local Notation Cin := Cin_0RB1LA_1RC1LB_0LB1RD_0LA0RC.

(** [E (2^n) = A^n C]: the boot's landing value, in the inner alphabet. *)
Lemma epow2_0RB1LA_1RC1LB_0LB1RD_0LA0RC : forall n, Ip (pow2 n) = rep [S1;S0] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** *** boot: the outer overflow anchor -> the inner anchor at [pow2 j] *)
Definition BB1_0RB1LA_1RC1LB_0LB1RD_0LA0RC : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S0] [] 0 0 []).
Definition chb_0RB1LA_1RC1LB_0LB1RD_0LA0RC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 6; SCycR 2; SWin 2].

Lemma run_boot_0RB1LA_1RC1LB_0LB1RD_0LA0RC : srun tm true true chb_0RB1LA_1RC1LB_0LB1RD_0LA0RC B0_0RB1LA_1RC1LB_0LB1RD_0LA0RC = Some (BB1_0RB1LA_1RC1LB_0LB1RD_0LA0RC, 4, 9).
Proof. vm_compute. reflexivity. Qed.

(** *** exit: the inner all-ones fill -> the outer successor *)
Definition BE0_0RB1LA_1RC1LB_0LB1RD_0LA0RC : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition che_0RB1LA_1RC1LB_0LB1RD_0LA0RC : list lstep := [SWinR 2; SCycL 2 0; SWin 2; SWinL 4; SCycR 2; SWin 1; SRotL 1; SFoldL 1].

Lemma run_exit_0RB1LA_1RC1LB_0LB1RD_0LA0RC : srun tm true true che_0RB1LA_1RC1LB_0LB1RD_0LA0RC BE0_0RB1LA_1RC1LB_0LB1RD_0LA0RC = Some (B1_0RB1LA_1RC1LB_0LB1RD_0LA0RC, 4, 9).
Proof. vm_compute. reflexivity. Qed.

(** *** the inner family's own INTERIOR lap -- ordinary and affine.  Iterating
    it to the fill is where the [Theta(2^j)] cost lives, and
    [NestedLapLift.inner_to_fill_lift] keeps it inside an existential. *)
Definition AI0_0RB1LA_1RC1LB_0LB1RD_0LA0RC : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition AI1_0RB1LA_1RC1LB_0LB1RD_0LA0RC : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S0] [] 0 0 []).
Definition chn_0RB1LA_1RC1LB_0LB1RD_0LA0RC : list lstep := [SWinR 2; SCycL 2 0; SWin 4; SCycR 2; SWin 2].

Lemma run_inner_0RB1LA_1RC1LB_0LB1RD_0LA0RC : srun tm false true chn_0RB1LA_1RC1LB_0LB1RD_0LA0RC AI0_0RB1LA_1RC1LB_0LB1RD_0LA0RC = Some (AI1_0RB1LA_1RC1LB_0LB1RD_0LA0RC, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_0RB1LA_1RC1LB_0LB1RD_0LA0RC : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Ap_Alph_10_11_11 q0 ++ [S0]) [] j A0_0RB1LA_1RC1LB_0LB1RD_0LA0RC.
Proof.
  intros p j q0 E. destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (H1 & _).
  unfold Cc_0RB1LA_1RC1LB_0LB1RD_0LA0RC, cden, A0_0RB1LA_1RC1LB_0LB1RD_0LA0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gei_0RB1LA_1RC1LB_0LB1RD_0LA0RC : forall p j q0, cview p = (j, Some q0) ->
  cden (Ap_Alph_10_11_11 q0 ++ [S0]) [] j A1_0RB1LA_1RC1LB_0LB1RD_0LA0RC = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (_ & H2).
  unfold Cc_0RB1LA_1RC1LB_0LB1RD_0LA0RC, cden, A1_0RB1LA_1RC1LB_0LB1RD_0LA0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_0RB1LA_1RC1LB_0LB1RD_0LA0RC : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (4 * j + 6). split; [lia|].
  rewrite (gsi_0RB1LA_1RC1LB_0LB1RD_0LA0RC p j q0 E).
  rewrite (srun_sound tm false true chi_0RB1LA_1RC1LB_0LB1RD_0LA0RC A0_0RB1LA_1RC1LB_0LB1RD_0LA0RC A1_0RB1LA_1RC1LB_0LB1RD_0LA0RC 4 6
             run_int_0RB1LA_1RC1LB_0LB1RD_0LA0RC (Ap_Alph_10_11_11 q0 ++ [S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_0RB1LA_1RC1LB_0LB1RD_0LA0RC p j q0 E).
Qed.

Lemma gso_0RB1LA_1RC1LB_0LB1RD_0LA0RC : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_0RB1LA_1RC1LB_0LB1RD_0LA0RC.
Proof.
  intros p j E. destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p j E) as (H1 & _).
  unfold Cc_0RB1LA_1RC1LB_0LB1RD_0LA0RC, cden, B0_0RB1LA_1RC1LB_0LB1RD_0LA0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_0RB1LA_1RC1LB_0LB1RD_0LA0RC : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_0RB1LA_1RC1LB_0LB1RD_0LA0RC : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB1LA_1RC1LB_0LB1RD_0LA0RC) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_0RB1LA_1RC1LB_0LB1RD_0LA0RC
             = (StD, (rep [S1;S0] (S j) ++ [S1;S1], S0, []))).
  { unfold cden, B1_0RB1LA_1RC1LB_0LB1RD_0LA0RC, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. reflexivity. }
  assert (HC : Cc (Pos.succ p) = (StD, ((rep [S1;S0] (S j) ++ [S1;S1]) ++ [S0], S0, []))).
  { unfold Cc_0RB1LA_1RC1LB_0LB1RD_0LA0RC. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_0RB1LA_1RC1LB_0LB1RD_0LA0RC. reflexivity.
Qed.

(** ** Nested-overflow glue *)

Lemma gsn_0RB1LA_1RC1LB_0LB1RD_0LA0RC : forall v i q0, cview v = (i, Some q0) ->
  Cin v = cden (Ip q0 ++ [S1]) [] i AI0_0RB1LA_1RC1LB_0LB1RD_0LA0RC.
Proof.
  intros v i q0 E. destruct (ILCounter.cview_some_I v i q0 E) as (H1 & _).
  unfold Cin_0RB1LA_1RC1LB_0LB1RD_0LA0RC, cden, AI0_0RB1LA_1RC1LB_0LB1RD_0LA0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen_0RB1LA_1RC1LB_0LB1RD_0LA0RC : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Ip q0 ++ [S1]) [] i AI1_0RB1LA_1RC1LB_0LB1RD_0LA0RC) = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (ILCounter.cview_some_I v i q0 E) as (_ & H2).
  unfold Cin_0RB1LA_1RC1LB_0LB1RD_0LA0RC, cden, AI1_0RB1LA_1RC1LB_0LB1RD_0LA0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S0]) with (([]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S0] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin_0RB1LA_1RC1LB_0LB1RD_0LA0RC : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 8), (cden (Ip q0 ++ [S1]) [] i AI1_0RB1LA_1RC1LB_0LB1RD_0LA0RC).
  split; [lia|]. split; [| exact (gen_0RB1LA_1RC1LB_0LB1RD_0LA0RC v i q0 E)].
  rewrite (gsn_0RB1LA_1RC1LB_0LB1RD_0LA0RC v i q0 E).
  exact (srun_sound tm false true chn_0RB1LA_1RC1LB_0LB1RD_0LA0RC AI0_0RB1LA_1RC1LB_0LB1RD_0LA0RC AI1_0RB1LA_1RC1LB_0LB1RD_0LA0RC 4 8
           run_inner_0RB1LA_1RC1LB_0LB1RD_0LA0RC (Ip q0 ++ [S1]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The boot lands on the inner anchor up to 0/1 trailing blanks. *)
Lemma gbo_0RB1LA_1RC1LB_0LB1RD_0LA0RC : forall j, lift (cden [] [] j BB1_0RB1LA_1RC1LB_0LB1RD_0LA0RC) = lift (Cin (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_0RB1LA_1RC1LB_0LB1RD_0LA0RC = (StB, (rep [S1;S0] j ++ [S1;S1], S0, ([]) ++ [S0]))).
  { unfold cden, BB1_0RB1LA_1RC1LB_0LB1RD_0LA0RC, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin (pow2 j) = (StB, (rep [S1;S0] j ++ [S1;S1], S0, []))).
  { unfold Cin_0RB1LA_1RC1LB_0LB1RD_0LA0RC. rewrite epow2_0RB1LA_1RC1LB_0LB1RD_0LA0RC.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_0RB1LA_1RC1LB_0LB1RD_0LA0RC. rewrite ?lift_app_blank. reflexivity.
Qed.

(** The inner counter's all-ones fill IS the exit chain's start.  [cview
    (fill (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    inner alphabet's own overflow decomposition names the word. *)
Lemma gxi_0RB1LA_1RC1LB_0LB1RD_0LA0RC : forall j, Cin (fill (pow2 j)) = cden [] [] j BE0_0RB1LA_1RC1LB_0LB1RD_0LA0RC.
Proof.
  intro j.
  destruct (ILCounter.cview_none_I (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin_0RB1LA_1RC1LB_0LB1RD_0LA0RC, cden, BE0_0RB1LA_1RC1LB_0LB1RD_0LA0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

(** The interior lap, restated up to [lift] -- what [vis_via_ovf_lift] and
    [vis_via_fill] consume. *)
Lemma lapil_0RB1LA_1RC1LB_0LB1RD_0LA0RC : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof. intros p j q0 E. destruct (lapi_0RB1LA_1RC1LB_0LB1RD_0LA0RC p j q0 E) as (n & Hn & Hr).
  exists n, (Cc (Pos.succ p)).
  split; [exact Hn | split; [exact Hr | reflexivity]]. Qed.

(** The outer OVERFLOW branch, composed.  The exponential cost is the [exists
    n] inside [inner_to_fill_lift]; no formula for it is ever written. *)
Lemma lapo_0RB1LA_1RC1LB_0LB1RD_0LA0RC : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E.
  apply (nested_overflow_lift tm Cc Cin lapin_0RB1LA_1RC1LB_0LB1RD_0LA0RC p (pow2 j)).
  - exists (4 * j + 9), (cden [] [] j BB1_0RB1LA_1RC1LB_0LB1RD_0LA0RC).
    split; [lia|]. split; [| exact (gbo_0RB1LA_1RC1LB_0LB1RD_0LA0RC j)].
    rewrite (gso_0RB1LA_1RC1LB_0LB1RD_0LA0RC p j E).
    exact (srun_sound tm true true chb_0RB1LA_1RC1LB_0LB1RD_0LA0RC B0_0RB1LA_1RC1LB_0LB1RD_0LA0RC BB1_0RB1LA_1RC1LB_0LB1RD_0LA0RC 4 9
             run_boot_0RB1LA_1RC1LB_0LB1RD_0LA0RC [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  - exists (4 * j + 9), (cden [] [] j B1_0RB1LA_1RC1LB_0LB1RD_0LA0RC).
    split; [| exact (geo_0RB1LA_1RC1LB_0LB1RD_0LA0RC p j E)].
    rewrite (gxi_0RB1LA_1RC1LB_0LB1RD_0LA0RC j).
    exact (srun_sound tm true true che_0RB1LA_1RC1LB_0LB1RD_0LA0RC BE0_0RB1LA_1RC1LB_0LB1RD_0LA0RC B1_0RB1LA_1RC1LB_0LB1RD_0LA0RC 4 9
             run_exit_0RB1LA_1RC1LB_0LB1RD_0LA0RC [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.



(** ** The lap *)

Lemma lap_0RB1LA_1RC1LB_0LB1RD_0LA0RC : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB1LA_1RC1LB_0LB1RD_0LA0RC p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->). exact (lapo_0RB1LA_1RC1LB_0LB1RD_0LA0RC p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_0RB1LA_1RC1LB_0LB1RD_0LA0RC : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
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

Lemma viso_0RB1LA_1RC1LB_0LB1RD_0LA0RC : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_0RB1LA_1RC1LB_0LB1RD_0LA0RC = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_0RB1LA_1RC1LB_0LB1RD_0LA0RC p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB1LA_1RC1LB_0LB1RD_0LA0RC p j E)].
Qed.

Lemma vis_0RB1LA_1RC1LB_0LB1RD_0LA0RC : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_0RB1LA_1RC1LB_0LB1RD_0LA0RC.
  destruct q.

  - (* StA *)
    apply (vis_via_ovf tm Cc Hi StA), viso_0RB1LA_1RC1LB_0LB1RD_0LA0RC
      with (l := [SRotL 1; SWin 1]).
    vm_compute; reflexivity.
  - (* StB *)
    apply (vis_via_ovf tm Cc Hi StB), viso_0RB1LA_1RC1LB_0LB1RD_0LA0RC
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 3]).
    vm_compute; reflexivity.
  - (* StC *)
    apply (vis_via_ovf tm Cc Hi StC), viso_0RB1LA_1RC1LB_0LB1RD_0LA0RC
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 5]).
    vm_compute; reflexivity.
  - (* StD: the anchor state *)
    exists 0. eexists. split; reflexivity.
Qed.

Theorem nqh_0RB1LA_1RC1LB_0LB1RD_0LA0RC : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 1). - exact boot_0RB1LA_1RC1LB_0LB1RD_0LA0RC. - intros p _. apply lap_0RB1LA_1RC1LB_0LB1RD_0LA0RC. - intros p q _. apply vis_0RB1LA_1RC1LB_0LB1RD_0LA0RC. Qed.

Theorem nonhalt_0RB1LA_1RC1LB_0LB1RD_0LA0RC : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_0RB1LA_1RC1LB_0LB1RD_0LA0RC. Qed.
