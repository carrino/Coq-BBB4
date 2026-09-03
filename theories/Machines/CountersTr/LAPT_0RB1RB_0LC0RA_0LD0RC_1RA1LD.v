(** * LAPT_0RB1RB_0LC0RA_0LD0RC_1RA1LD: TRANSITION-LEVEL board for machine 0RB1RB_0LC0RA_0LD0RC_1RA1LD, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Ap_Alph_10_11_11 digit alphabet (Alph_10_11_11.v), anchored at

      Cc p = (StA, (Ap_Alph_10_11_11 p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  4*j+10 steps
      overflow  (cview p = (S j, None)):   boot 4*j+11, then the inner counter's own laps to the
                                           all-ones fill, then exit 4*j+15

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
From BBB4 Require Import BBBT4_Statement.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
Import ListNotations.

Definition mk_0RB1RB_0LC0RA_0LD0RC_1RA1LD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB1RB_0LC0RA_0LD0RC_1RA1LD.

(** 0RB1RB_0LC0RA_0LD0RC_1RA1LD *)
Definition tm_0RB1RB_0LC0RA_0LD0RC_1RA1LD : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S1 DR StB
  | StB, S0 => mk S0 DL StC | StB, S1 => mk S0 DR StA
  | StC, S0 => mk S0 DL StD | StC, S1 => mk S0 DR StC
  | StD, S0 => mk S1 DR StA | StD, S1 => mk S1 DL StD end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_0RB1RB_0LC0RA_0LD0RC_1RA1LD : list Instr := [].
Definition tmw_0RB1RB_0LC0RA_0LD0RC_1RA1LD : TM := tm_wrap_trs tm_0RB1RB_0LC0RA_0LD0RC_1RA1LD pins_0RB1RB_0LC0RA_0LD0RC_1RA1LD.
Local Notation tm := tmw_0RB1RB_0LC0RA_0LD0RC_1RA1LD.

Definition Cc_0RB1RB_0LC0RA_0LD0RC_1RA1LD (p : positive) : cconf := (StA, (Ap_Alph_10_11_11 p ++ [S0], S0, [])).
Local Notation Cc := Cc_0RB1RB_0LC0RA_0LD0RC_1RA1LD.

(** ** The certificate *)

Definition A0_0RB1RB_0LC0RA_0LD0RC_1RA1LD : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition A1_0RB1RB_0LC0RA_0LD0RC_1RA1LD : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S0] [] 0 0 []).
Definition chi_0RB1RB_0LC0RA_0LD0RC_1RA1LD : list lstep := [SWinR 2; SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 5; SUnrotL 1].

Lemma run_int_0RB1RB_0LC0RA_0LD0RC_1RA1LD : srun tm false true chi_0RB1RB_0LC0RA_0LD0RC_1RA1LD A0_0RB1RB_0LC0RA_0LD0RC_1RA1LD = Some (A1_0RB1RB_0LC0RA_0LD0RC_1RA1LD, 4, 10).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB1RB_0LC0RA_0LD0RC_1RA1LD : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_0RB1RB_0LC0RA_0LD0RC_1RA1LD : sconf := mkC StA (mkS [] [S1;S0] 1 1 [S1;S1]) S0 (mkS [S0] [] 0 0 []).
(** ** The INNER anchor family -- Ip at StD *)
Definition Cin_0RB1RB_0LC0RA_0LD0RC_1RA1LD (v : positive) : cconf := (StD, (Ip v ++ [S1], S0, [])).
Local Notation Cin := Cin_0RB1RB_0LC0RA_0LD0RC_1RA1LD.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow2_0RB1RB_0LC0RA_0LD0RC_1RA1LD : forall n, Ip (pow2 n) = rep [S1;S0] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap -- ordinary and affine.  Iterating it to the fill is
    where a [Theta(2^j)] lives, and [inner_to_fill_lift] keeps it inside an
    existential. *)
Definition AI0_0RB1RB_0LC0RA_0LD0RC_1RA1LD : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition AI1_0RB1RB_0LC0RA_0LD0RC_1RA1LD : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S0;S0] [] 0 0 []).
Definition chn_0RB1RB_0LC0RA_0LD0RC_1RA1LD : list lstep := [SWinR 4; SCycL 2 0; SWin 4; SCycR 2; SWin 4].

Lemma run_inner_0RB1RB_0LC0RA_0LD0RC_1RA1LD : srun tm false true chn_0RB1RB_0LC0RA_0LD0RC_1RA1LD AI0_0RB1RB_0LC0RA_0LD0RC_1RA1LD = Some (AI1_0RB1RB_0LC0RA_0LD0RC_1RA1LD, 4, 12).
Proof. vm_compute. reflexivity. Qed.

(** *** boot: the outer overflow anchor -> the first inner anchor at [pow2 j] *)
Definition BB1_0RB1RB_0LC0RA_0LD0RC_1RA1LD : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S0;S0] [] 0 0 []).
Definition chb_0RB1RB_0LC0RA_0LD0RC_1RA1LD : list lstep := [SWinR 2; SRotL 1; SWin 1; SCycL 2 0; SWin 4; SCycR 2; SWin 4].

Lemma run_boot_0RB1RB_0LC0RA_0LD0RC_1RA1LD : srun tm true true chb_0RB1RB_0LC0RA_0LD0RC_1RA1LD B0_0RB1RB_0LC0RA_0LD0RC_1RA1LD = Some (BB1_0RB1RB_0LC0RA_0LD0RC_1RA1LD, 4, 11).
Proof. vm_compute. reflexivity. Qed.

(** *** exit: the last inner all-ones fill -> the outer successor *)
Definition BE0_0RB1RB_0LC0RA_0LD0RC_1RA1LD : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition che_0RB1RB_0LC0RA_0LD0RC_1RA1LD : list lstep := [SWinR 4; SCycL 2 0; SWin 2; SWinL 4; SCycR 2; SWin 5; SRotL 1; SFoldL 1].

Lemma run_exit_0RB1RB_0LC0RA_0LD0RC_1RA1LD : srun tm true true che_0RB1RB_0LC0RA_0LD0RC_1RA1LD BE0_0RB1RB_0LC0RA_0LD0RC_1RA1LD = Some (B1_0RB1RB_0LC0RA_0LD0RC_1RA1LD, 4, 15).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_0RB1RB_0LC0RA_0LD0RC_1RA1LD : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Ap_Alph_10_11_11 q0 ++ [S0]) [] j A0_0RB1RB_0LC0RA_0LD0RC_1RA1LD.
Proof.
  intros p j q0 E. destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (H1 & _).
  unfold Cc_0RB1RB_0LC0RA_0LD0RC_1RA1LD, cden, A0_0RB1RB_0LC0RA_0LD0RC_1RA1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

(** The lap ends on [S0] where the anchor has [] -- one trailing blank,
    which [lift] cannot see. *)
Lemma gei_0RB1RB_0LC0RA_0LD0RC_1RA1LD : forall p j q0, cview p = (j, Some q0) ->
  lift (cden (Ap_Alph_10_11_11 q0 ++ [S0]) [] j A1_0RB1RB_0LC0RA_0LD0RC_1RA1LD) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (_ & H2).
  unfold Cc_0RB1RB_0LC0RA_0LD0RC_1RA1LD, cden, A1_0RB1RB_0LC0RA_0LD0RC_1RA1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S0]) with (([]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_0RB1RB_0LC0RA_0LD0RC_1RA1LD : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  exists (4 * j + 10), (cden (Ap_Alph_10_11_11 q0 ++ [S0]) [] j A1_0RB1RB_0LC0RA_0LD0RC_1RA1LD).
  split; [lia|]. split; [| exact (gei_0RB1RB_0LC0RA_0LD0RC_1RA1LD p j q0 E)].
  rewrite (gsi_0RB1RB_0LC0RA_0LD0RC_1RA1LD p j q0 E).
  exact (srun_sound tm false true chi_0RB1RB_0LC0RA_0LD0RC_1RA1LD A0_0RB1RB_0LC0RA_0LD0RC_1RA1LD A1_0RB1RB_0LC0RA_0LD0RC_1RA1LD 4 10
           run_int_0RB1RB_0LC0RA_0LD0RC_1RA1LD (Ap_Alph_10_11_11 q0 ++ [S0]) [] j
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma gso_0RB1RB_0LC0RA_0LD0RC_1RA1LD : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_0RB1RB_0LC0RA_0LD0RC_1RA1LD.
Proof.
  intros p j E. destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p j E) as (H1 & _).
  unfold Cc_0RB1RB_0LC0RA_0LD0RC_1RA1LD, cden, B0_0RB1RB_0LC0RA_0LD0RC_1RA1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_0RB1RB_0LC0RA_0LD0RC_1RA1LD : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_0RB1RB_0LC0RA_0LD0RC_1RA1LD : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB1RB_0LC0RA_0LD0RC_1RA1LD) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_0RB1RB_0LC0RA_0LD0RC_1RA1LD
             = (StA, (rep [S1;S0] (S j) ++ [S1;S1], S0, ([]) ++ [S0]))).
  { unfold cden, B1_0RB1RB_0LC0RA_0LD0RC_1RA1LD, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StA, ((rep [S1;S0] (S j) ++ [S1;S1]) ++ [S0], S0, []))).
  { unfold Cc_0RB1RB_0LC0RA_0LD0RC_1RA1LD. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lift_app_blank. rewrite !lbl_0RB1RB_0LC0RA_0LD0RC_1RA1LD. reflexivity.
Qed.

Lemma gsn_0RB1RB_0LC0RA_0LD0RC_1RA1LD : forall v i q0, cview v = (i, Some q0) ->
  Cin v = cden (Ip q0 ++ [S1]) [] i AI0_0RB1RB_0LC0RA_0LD0RC_1RA1LD.
Proof.
  intros v i q0 E. destruct (ILCounter.cview_some_I v i q0 E) as (H1 & _).
  unfold Cin_0RB1RB_0LC0RA_0LD0RC_1RA1LD, cden, AI0_0RB1RB_0LC0RA_0LD0RC_1RA1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen_0RB1RB_0LC0RA_0LD0RC_1RA1LD : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Ip q0 ++ [S1]) [] i AI1_0RB1RB_0LC0RA_0LD0RC_1RA1LD) = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (ILCounter.cview_some_I v i q0 E) as (_ & H2).
  unfold Cin_0RB1RB_0LC0RA_0LD0RC_1RA1LD, cden, AI1_0RB1RB_0LC0RA_0LD0RC_1RA1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S0;S0]) with ((([]) ++ [S0]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S0] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin_0RB1RB_0LC0RA_0LD0RC_1RA1LD : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 12), (cden (Ip q0 ++ [S1]) [] i AI1_0RB1RB_0LC0RA_0LD0RC_1RA1LD).
  split; [lia|]. split; [| exact (gen_0RB1RB_0LC0RA_0LD0RC_1RA1LD v i q0 E)].
  rewrite (gsn_0RB1RB_0LC0RA_0LD0RC_1RA1LD v i q0 E).
  exact (srun_sound tm false true chn_0RB1RB_0LC0RA_0LD0RC_1RA1LD AI0_0RB1RB_0LC0RA_0LD0RC_1RA1LD AI1_0RB1RB_0LC0RA_0LD0RC_1RA1LD 4 12
           run_inner_0RB1RB_0LC0RA_0LD0RC_1RA1LD (Ip q0 ++ [S1]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The chain into this family lands on its anchor up to 0/2
    trailing blanks. *)
Lemma gbo_0RB1RB_0LC0RA_0LD0RC_1RA1LD : forall j, lift (cden [] [] j BB1_0RB1RB_0LC0RA_0LD0RC_1RA1LD) = lift (Cin (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_0RB1RB_0LC0RA_0LD0RC_1RA1LD = (StD, (rep [S1;S0] j ++ [S1;S1], S0, (([]) ++ [S0]) ++ [S0]))).
  { unfold cden, BB1_0RB1RB_0LC0RA_0LD0RC_1RA1LD, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin (pow2 j) = (StD, (rep [S1;S0] j ++ [S1;S1], S0, []))).
  { unfold Cin_0RB1RB_0LC0RA_0LD0RC_1RA1LD. rewrite epow2_0RB1RB_0LC0RA_0LD0RC_1RA1LD.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_0RB1RB_0LC0RA_0LD0RC_1RA1LD. rewrite ?lift_app_blank. reflexivity.
Qed.

(** This family's all-ones fill IS the next chain's start.  [cview (fill
    (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    family's own overflow decomposition names the word. *)
Lemma gxi_0RB1RB_0LC0RA_0LD0RC_1RA1LD : forall j, Cin (fill (pow2 j)) = cden [] [] j BE0_0RB1RB_0LC0RA_0LD0RC_1RA1LD.
Proof.
  intro j.
  destruct (ILCounter.cview_none_I (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin_0RB1RB_0LC0RA_0LD0RC_1RA1LD, cden, BE0_0RB1RB_0LC0RA_0LD0RC_1RA1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

(** The interior lap, restated up to [lift] -- what [vis_via_ovf_lift] and
    [vis_via_fill] consume. *)
Lemma lapil_0RB1RB_0LC0RA_0LD0RC_1RA1LD : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof. exact lapi_0RB1RB_0LC0RA_0LD0RC_1RA1LD. Qed.

(** The outer OVERFLOW branch, composed.  The exponential cost is the
    [exists n] inside [inner_to_fill_lift]; no formula for it is ever
    written. *)
Lemma lapo_0RB1RB_0LC0RA_0LD0RC_1RA1LD : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E.
  apply (nested_overflow_lift tm Cc Cin lapin_0RB1RB_0LC0RA_0LD0RC_1RA1LD p (pow2 j)).
  - exists (4 * j + 11), (cden [] [] j BB1_0RB1RB_0LC0RA_0LD0RC_1RA1LD).
    split; [lia|]. split; [| exact (gbo_0RB1RB_0LC0RA_0LD0RC_1RA1LD j)].
    rewrite (gso_0RB1RB_0LC0RA_0LD0RC_1RA1LD p j E).
    exact (srun_sound tm true true chb_0RB1RB_0LC0RA_0LD0RC_1RA1LD B0_0RB1RB_0LC0RA_0LD0RC_1RA1LD BB1_0RB1RB_0LC0RA_0LD0RC_1RA1LD 4 11
             run_boot_0RB1RB_0LC0RA_0LD0RC_1RA1LD [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  - exists (4 * j + 15), (cden [] [] j B1_0RB1RB_0LC0RA_0LD0RC_1RA1LD).
    split; [| exact (geo_0RB1RB_0LC0RA_0LD0RC_1RA1LD p j E)].
    rewrite (gxi_0RB1RB_0LC0RA_0LD0RC_1RA1LD j).
    exact (srun_sound tm true true che_0RB1RB_0LC0RA_0LD0RC_1RA1LD BE0_0RB1RB_0LC0RA_0LD0RC_1RA1LD B1_0RB1RB_0LC0RA_0LD0RC_1RA1LD 4 15
             run_exit_0RB1RB_0LC0RA_0LD0RC_1RA1LD [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.



(** ** The lap *)

Lemma lap_0RB1RB_0LC0RA_0LD0RC_1RA1LD : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB1RB_0LC0RA_0LD0RC_1RA1LD p j q0 E) as (n & c' & Hn & Hrun & Hlift).
    exists n, c'. split; [exact Hrun | split; [exact Hlift | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->). exact (lapo_0RB1RB_0LC0RA_0LD0RC_1RA1LD p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_0RB1RB_0LC0RA_0LD0RC_1RA1LD : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 14.
  assert (H : match csteps tm 14 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 14 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_0RB1RB_0LC0RA_0LD0RC_1RA1LD : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_0RB1RB_0LC0RA_0LD0RC_1RA1LD = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_0RB1RB_0LC0RA_0LD0RC_1RA1LD p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB1RB_0LC0RA_0LD0RC_1RA1LD p j E)].
Qed.


(** An instruction that fires ONLY inside the interior lap: [vis_via_ovf] runs to an
    OVERFLOW anchor, so it cannot see one.  This is the interior witness, and
    [LapCertGlueLift.fire_via_int_lift] carries it to every anchor. *)
Lemma firei_0RB1RB_0LC0RA_0LD0RC_1RA1LD : forall (l : list lstep) (t : Instr),
  srun_instr tm false true l A0_0RB1RB_0LC0RA_0LD0RC_1RA1LD = Some t ->
  forall p j q0, cview p = (j, Some q0) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j q0 E.
  apply (fire_of_run_instr tm Cc false true l A0_0RB1RB_0LC0RA_0LD0RC_1RA1LD p j (Ap_Alph_10_11_11 q0 ++ [S0]) []);
    [exact Hst | discriminate | reflexivity | exact (gsi_0RB1RB_0LC0RA_0LD0RC_1RA1LD p j q0 E)].
Qed.

(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_0RB1RB_0LC0RA_0LD0RC_1RA1LD : forall t, ~ In t pins_0RB1RB_0LC0RA_0LD0RC_1RA1LD ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n c', 0 < n /\ csteps tm n (Cc p0) = Some c'
                         /\ lift c' = lift (Cc (Pos.succ p0)))
    by exact lapi_0RB1RB_0LC0RA_0LD0RC_1RA1LD.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StA, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1RB_0LC0RA_0LD0RC_1RA1LD [] (StA, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* A1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StA, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1RB_0LC0RA_0LD0RC_1RA1LD [SWinR 2; SRotL 1; SWin 1; SCycL 2 0; SWin 3] (StA, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* B0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StB, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1RB_0LC0RA_0LD0RC_1RA1LD [SWinR 1] (StB, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* B1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StB, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1RB_0LC0RA_0LD0RC_1RA1LD [SWinR 2; SRotL 1; SWin 1; SCycL 2 0; SWin 4] (StB, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* C0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StC, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1RB_0LC0RA_0LD0RC_1RA1LD [SWinR 2] (StC, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* C1: fires only in the interior lap *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_int_lift tm Cc lap_0RB1RB_0LC0RA_0LD0RC_1RA1LD (StC, S1)).
    intros p1 j1 r1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (firei_0RB1RB_0LC0RA_0LD0RC_1RA1LD [SWinR 2; SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 2] (StC, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 r1 E1).
  - (* D0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StD, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1RB_0LC0RA_0LD0RC_1RA1LD [SWinR 2; SRotL 1; SWin 1; SCycL 2 0; SWin 2] (StD, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* D1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StD, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1RB_0LC0RA_0LD0RC_1RA1LD [SWinR 2; SRotL 1; SWin 1] (StD, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
Qed.

Theorem nqhtr_0RB1RB_0LC0RA_0LD0RC_1RA1LD : NeverQuasiHaltsTr tm_0RB1RB_0LC0RA_0LD0RC_1RA1LD.
Proof.
  apply (glue_neverqhtr tm_0RB1RB_0LC0RA_0LD0RC_1RA1LD pins_0RB1RB_0LC0RA_0LD0RC_1RA1LD Cc 1).
  - exact boot_0RB1RB_0LC0RA_0LD0RC_1RA1LD.
  - intros p _. apply lap_0RB1RB_0LC0RA_0LD0RC_1RA1LD.
  - intros t Ht p _. apply fire_0RB1RB_0LC0RA_0LD0RC_1RA1LD. exact Ht.
Qed.

Theorem nonhalt_0RB1RB_0LC0RA_0LD0RC_1RA1LD : NonHalt tm_0RB1RB_0LC0RA_0LD0RC_1RA1LD.
Proof. apply never_qh_tr_nonhalt, nqhtr_0RB1RB_0LC0RA_0LD0RC_1RA1LD. Qed.
