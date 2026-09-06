(** * LAPT_1RB1RA_1LC1RD_0RB0LC_1RA0LA: TRANSITION-LEVEL board for machine 1RB1RA_1LC1RD_0RB0LC_1RA0LA, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Ap_Alph_000_001_1 digit alphabet (Alph_000_001_1.v), anchored at

      Cc p = (StB, (Ap_Alph_000_001_1 p ++ [S0], S0, [S1;S1;S1]))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  6*j+26 steps
      overflow  (cview p = (S j, None)):   boot 6*j+21, then the inner counter's own laps to the
                                           all-ones fill, then exit 6*j+23

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 192 interior anchors (interior); 6 overflow phases, j = 2..7 (492 inner laps, 2 counts each) (nested overflow).
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter Alph_000_001_1 LapCertGlue LapCertGlueLift IXPGadgets NestedLap NestedLapLift NestedLap2 Alph_000_001_00.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
From BBB4 Require Import BBBT4_Statement.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr.
Import ListNotations.

Definition mk_1RB1RA_1LC1RD_0RB0LC_1RA0LA (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1RA_1LC1RD_0RB0LC_1RA0LA.

(** 1RB1RA_1LC1RD_0RB0LC_1RA0LA *)
(** 1RB1RA_1LC1RD_0RB0LC_1RA0LA -- the real machine (its counter grows RIGHT). *)
Definition tm_1RB1RA_1LC1RD_0RB0LC_1RA0LA : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DR StA
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S0 DR StB | StC, S1 => mk S0 DL StC
  | StD, S0 => mk S1 DR StA | StD, S1 => mk S0 DL StA end.

(** Its mirror 1LB1LA_1RC1LD_0LB0RC_1LA0RA: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_1RB1RA_1LC1RD_0RB0LC_1RA0LA : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => mk S1 DL StA
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DL StD
  | StC, S0 => mk S0 DL StB | StC, S1 => mk S0 DR StC
  | StD, S0 => mk S1 DL StA | StD, S1 => mk S0 DR StA end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_1RB1RA_1LC1RD_0RB0LC_1RA0LA : list Instr := [].
Definition tmw_1RB1RA_1LC1RD_0RB0LC_1RA0LA : TM := tm_wrap_trs tmm_1RB1RA_1LC1RD_0RB0LC_1RA0LA pins_1RB1RA_1LC1RD_0RB0LC_1RA0LA.
Local Notation tm := tmw_1RB1RA_1LC1RD_0RB0LC_1RA0LA.

Lemma mirror_ok_1RB1RA_1LC1RD_0RB0LC_1RA0LA : mirror_tm tm_1RB1RA_1LC1RD_0RB0LC_1RA0LA = tmm_1RB1RA_1LC1RD_0RB0LC_1RA0LA.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_1RB1RA_1LC1RD_0RB0LC_1RA0LA (p : positive) : cconf := (StB, (Ap_Alph_000_001_1 p ++ [S0], S0, [S1;S1;S1])).
Local Notation Cc := Cc_1RB1RA_1LC1RD_0RB0LC_1RA0LA.

(** ** The certificate *)

Definition A0_1RB1RA_1LC1RD_0RB0LC_1RA0LA : sconf := mkC StB (mkS [] [S0;S0;S1] 1 0 [S0;S0;S0]) S0 (mkS [S1;S1;S1] [] 0 0 []).
Definition A1_1RB1RA_1LC1RD_0RB0LC_1RA0LA : sconf := mkC StB (mkS [] [S0;S0;S0] 1 0 [S0;S0;S1]) S0 (mkS [S1;S1;S1;S0] [] 0 0 []).
Definition chi_1RB1RA_1LC1RD_0RB0LC_1RA0LA : list lstep := [SWin 3; SWinR 7; SCycL 3 0; SWin 6; SCycR 3; SWin 10].

Lemma run_int_1RB1RA_1LC1RD_0RB0LC_1RA0LA : srun tm false true chi_1RB1RA_1LC1RD_0RB0LC_1RA0LA A0_1RB1RA_1LC1RD_0RB0LC_1RA0LA = Some (A1_1RB1RA_1LC1RD_0RB0LC_1RA0LA, 6, 26).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB1RA_1LC1RD_0RB0LC_1RA0LA : sconf := mkC StB (mkS [] [S0;S0;S1] 1 0 [S1;S0]) S0 (mkS [S1;S1;S1] [] 0 0 []).
Definition B1_1RB1RA_1LC1RD_0RB0LC_1RA0LA : sconf := mkC StB (mkS [] [S0;S0;S0] 1 1 [S1]) S0 (mkS [S1;S1;S1;S0] [] 0 0 []).
(** ** The FIRST INNER anchor family -- Ap_Alph_000_001_00 at StB *)
Definition Cin_1RB1RA_1LC1RD_0RB0LC_1RA0LA (v : positive) : cconf := (StB, (Ap_Alph_000_001_00 v ++ [S0;S0;S1], S0, [])).
Local Notation Cin := Cin_1RB1RA_1LC1RD_0RB0LC_1RA0LA.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow2_1RB1RA_1LC1RD_0RB0LC_1RA0LA : forall n, Ap_Alph_000_001_00 (pow2 n) = rep [S0;S0;S0] n ++ [S0;S0].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap -- ordinary and affine.  Iterating it to the fill is
    where a [Theta(2^j)] lives, and [inner_to_fill_lift] keeps it inside an
    existential. *)
Definition AI0_1RB1RA_1LC1RD_0RB0LC_1RA0LA : sconf := mkC StB (mkS [] [S0;S0;S1] 1 0 [S0;S0;S0]) S0 (mkS [] [] 0 0 []).
Definition AI1_1RB1RA_1LC1RD_0RB0LC_1RA0LA : sconf := mkC StB (mkS [] [S0;S0;S0] 1 0 [S0;S0;S1]) S0 (mkS [S0] [] 0 0 []).
Definition chn_1RB1RA_1LC1RD_0RB0LC_1RA0LA : list lstep := [SWinR 2; SCycL 3 0; SWin 6; SCycR 3; SWin 2].

Lemma run_inner_1RB1RA_1LC1RD_0RB0LC_1RA0LA : srun tm false true chn_1RB1RA_1LC1RD_0RB0LC_1RA0LA AI0_1RB1RA_1LC1RD_0RB0LC_1RA0LA = Some (AI1_1RB1RA_1LC1RD_0RB0LC_1RA0LA, 6, 10).
Proof. vm_compute. reflexivity. Qed.

(** ** The SECOND INNER anchor family -- Ap_Alph_000_001_00 at StB *)
Definition Cin2_1RB1RA_1LC1RD_0RB0LC_1RA0LA (v : positive) : cconf := (StB, (Ap_Alph_000_001_00 v ++ [S1;S0;S1], S0, [])).
Local Notation Cin2 := Cin2_1RB1RA_1LC1RD_0RB0LC_1RA0LA.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow22_1RB1RA_1LC1RD_0RB0LC_1RA0LA : forall n, Ap_Alph_000_001_00 (pow2 n) = rep [S0;S0;S0] n ++ [S0;S0].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap -- ordinary and affine.  Iterating it to the fill is
    where a [Theta(2^j)] lives, and [inner_to_fill_lift] keeps it inside an
    existential. *)
Definition AI20_1RB1RA_1LC1RD_0RB0LC_1RA0LA : sconf := mkC StB (mkS [] [S0;S0;S1] 1 0 [S0;S0;S0]) S0 (mkS [] [] 0 0 []).
Definition AI21_1RB1RA_1LC1RD_0RB0LC_1RA0LA : sconf := mkC StB (mkS [] [S0;S0;S0] 1 0 [S0;S0;S1]) S0 (mkS [S0] [] 0 0 []).
Definition chn2_1RB1RA_1LC1RD_0RB0LC_1RA0LA : list lstep := [SWinR 2; SCycL 3 0; SWin 6; SCycR 3; SWin 2].

Lemma run_inner2_1RB1RA_1LC1RD_0RB0LC_1RA0LA : srun tm false true chn2_1RB1RA_1LC1RD_0RB0LC_1RA0LA AI20_1RB1RA_1LC1RD_0RB0LC_1RA0LA = Some (AI21_1RB1RA_1LC1RD_0RB0LC_1RA0LA, 6, 10).
Proof. vm_compute. reflexivity. Qed.

(** *** boot: the outer overflow anchor -> the first inner anchor at [pow2 j] *)
Definition BB1_1RB1RA_1LC1RD_0RB0LC_1RA0LA : sconf := mkC StB (mkS [] [S0;S0;S0] 1 0 [S0;S0;S0;S0;S1]) S0 (mkS [S0] [] 0 0 []).
Definition chb_1RB1RA_1LC1RD_0RB0LC_1RA0LA : list lstep := [SWin 3; SWinR 7; SCycL 3 0; SWin 6; SCycR 3; SWin 5; SUnrotL 3].

Lemma run_boot_1RB1RA_1LC1RD_0RB0LC_1RA0LA : srun tm true true chb_1RB1RA_1LC1RD_0RB0LC_1RA0LA B0_1RB1RA_1LC1RD_0RB0LC_1RA0LA = Some (BB1_1RB1RA_1LC1RD_0RB0LC_1RA0LA, 6, 21).
Proof. vm_compute. reflexivity. Qed.

(** *** shift: count 1's all-ones fill -> count 2's anchor.
    WAVE18 section 4c -- "count 8->15, shift, count 8->15 again". *)
Definition BM0_1RB1RA_1LC1RD_0RB0LC_1RA0LA : sconf := mkC StB (mkS [] [S0;S0;S1] 1 0 [S0;S0;S0;S0;S1]) S0 (mkS [] [] 0 0 []).
Definition BM1_1RB1RA_1LC1RD_0RB0LC_1RA0LA : sconf := mkC StB (mkS [] [S0;S0;S0] 1 0 [S0;S0;S1;S0;S1]) S0 (mkS [S0] [] 0 0 []).
Definition chm_1RB1RA_1LC1RD_0RB0LC_1RA0LA : list lstep := [SWinR 2; SCycL 3 0; SWin 6; SCycR 3; SWin 2].

Lemma run_shift_1RB1RA_1LC1RD_0RB0LC_1RA0LA : srun tm true true chm_1RB1RA_1LC1RD_0RB0LC_1RA0LA BM0_1RB1RA_1LC1RD_0RB0LC_1RA0LA = Some (BM1_1RB1RA_1LC1RD_0RB0LC_1RA0LA, 6, 10).
Proof. vm_compute. reflexivity. Qed.

(** *** exit: the last inner all-ones fill -> the outer successor *)
Definition BE0_1RB1RA_1LC1RD_0RB0LC_1RA0LA : sconf := mkC StB (mkS [] [S0;S0;S1] 1 0 [S0;S0;S1;S0;S1]) S0 (mkS [] [] 0 0 []).
Definition che_1RB1RA_1LC1RD_0RB0LC_1RA0LA : list lstep := [SWinR 2; SCycL 3 0; SWin 5; SWinL 9; SCycR 3; SWin 4; SRotL 1; SWin 1; SRotL 1; SWin 1; SRotL 1; SWin 1; SRotL 3; SFoldL 1].

Lemma run_exit_1RB1RA_1LC1RD_0RB0LC_1RA0LA : srun tm true true che_1RB1RA_1LC1RD_0RB0LC_1RA0LA BE0_1RB1RA_1LC1RD_0RB0LC_1RA0LA = Some (B1_1RB1RA_1LC1RD_0RB0LC_1RA0LA, 6, 23).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_1RB1RA_1LC1RD_0RB0LC_1RA0LA : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Ap_Alph_000_001_1 q0 ++ [S0]) [] j A0_1RB1RA_1LC1RD_0RB0LC_1RA0LA.
Proof.
  intros p j q0 E. destruct (Alph_000_001_1.cview_some_Alph_000_001_1 p j q0 E) as (H1 & _).
  unfold Cc_1RB1RA_1LC1RD_0RB0LC_1RA0LA, cden, A0_1RB1RA_1LC1RD_0RB0LC_1RA0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S0;S0;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

(** The lap ends on [S1;S1;S1;S0] where the anchor has [S1;S1;S1] -- one trailing blank,
    which [lift] cannot see. *)
Lemma gei_1RB1RA_1LC1RD_0RB0LC_1RA0LA : forall p j q0, cview p = (j, Some q0) ->
  lift (cden (Ap_Alph_000_001_1 q0 ++ [S0]) [] j A1_1RB1RA_1LC1RD_0RB0LC_1RA0LA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (Alph_000_001_1.cview_some_Alph_000_001_1 p j q0 E) as (_ & H2).
  unfold Cc_1RB1RA_1LC1RD_0RB0LC_1RA0LA, cden, A1_1RB1RA_1LC1RD_0RB0LC_1RA0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S1;S1;S1;S0]) with (([S1;S1;S1]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S0;S0;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB1RA_1LC1RD_0RB0LC_1RA0LA : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  exists (6 * j + 26), (cden (Ap_Alph_000_001_1 q0 ++ [S0]) [] j A1_1RB1RA_1LC1RD_0RB0LC_1RA0LA).
  split; [lia|]. split; [| exact (gei_1RB1RA_1LC1RD_0RB0LC_1RA0LA p j q0 E)].
  rewrite (gsi_1RB1RA_1LC1RD_0RB0LC_1RA0LA p j q0 E).
  exact (srun_sound tm false true chi_1RB1RA_1LC1RD_0RB0LC_1RA0LA A0_1RB1RA_1LC1RD_0RB0LC_1RA0LA A1_1RB1RA_1LC1RD_0RB0LC_1RA0LA 6 26
           run_int_1RB1RA_1LC1RD_0RB0LC_1RA0LA (Ap_Alph_000_001_1 q0 ++ [S0]) [] j
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma gso_1RB1RA_1LC1RD_0RB0LC_1RA0LA : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_1RB1RA_1LC1RD_0RB0LC_1RA0LA.
Proof.
  intros p j E. destruct (Alph_000_001_1.cview_none_Alph_000_001_1 p j E) as (H1 & _).
  unfold Cc_1RB1RA_1LC1RD_0RB0LC_1RA0LA, cden, B0_1RB1RA_1LC1RD_0RB0LC_1RA0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB1RA_1LC1RD_0RB0LC_1RA0LA : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB1RA_1LC1RD_0RB0LC_1RA0LA : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB1RA_1LC1RD_0RB0LC_1RA0LA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (Alph_000_001_1.cview_none_Alph_000_001_1 p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB1RA_1LC1RD_0RB0LC_1RA0LA
             = (StB, (rep [S0;S0;S0] (S j) ++ [S1], S0, ([S1;S1;S1]) ++ [S0]))).
  { unfold cden, B1_1RB1RA_1LC1RD_0RB0LC_1RA0LA, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StB, ((rep [S0;S0;S0] (S j) ++ [S1]) ++ [S0], S0, [S1;S1;S1]))).
  { unfold Cc_1RB1RA_1LC1RD_0RB0LC_1RA0LA. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lift_app_blank. rewrite !lbl_1RB1RA_1LC1RD_0RB0LC_1RA0LA. reflexivity.
Qed.

Lemma gsn_1RB1RA_1LC1RD_0RB0LC_1RA0LA : forall v i q0, cview v = (i, Some q0) ->
  Cin v = cden (Ap_Alph_000_001_00 q0 ++ [S0;S0;S1]) [] i AI0_1RB1RA_1LC1RD_0RB0LC_1RA0LA.
Proof.
  intros v i q0 E. destruct (Alph_000_001_00.cview_some_Alph_000_001_00 v i q0 E) as (H1 & _).
  unfold Cin_1RB1RA_1LC1RD_0RB0LC_1RA0LA, cden, AI0_1RB1RA_1LC1RD_0RB0LC_1RA0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S0;S0;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen_1RB1RA_1LC1RD_0RB0LC_1RA0LA : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Ap_Alph_000_001_00 q0 ++ [S0;S0;S1]) [] i AI1_1RB1RA_1LC1RD_0RB0LC_1RA0LA) = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (Alph_000_001_00.cview_some_Alph_000_001_00 v i q0 E) as (_ & H2).
  unfold Cin_1RB1RA_1LC1RD_0RB0LC_1RA0LA, cden, AI1_1RB1RA_1LC1RD_0RB0LC_1RA0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S0]) with (([]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S0;S0;S0] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin_1RB1RA_1LC1RD_0RB0LC_1RA0LA : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (6 * i + 10), (cden (Ap_Alph_000_001_00 q0 ++ [S0;S0;S1]) [] i AI1_1RB1RA_1LC1RD_0RB0LC_1RA0LA).
  split; [lia|]. split; [| exact (gen_1RB1RA_1LC1RD_0RB0LC_1RA0LA v i q0 E)].
  rewrite (gsn_1RB1RA_1LC1RD_0RB0LC_1RA0LA v i q0 E).
  exact (srun_sound tm false true chn_1RB1RA_1LC1RD_0RB0LC_1RA0LA AI0_1RB1RA_1LC1RD_0RB0LC_1RA0LA AI1_1RB1RA_1LC1RD_0RB0LC_1RA0LA 6 10
           run_inner_1RB1RA_1LC1RD_0RB0LC_1RA0LA (Ap_Alph_000_001_00 q0 ++ [S0;S0;S1]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The chain into this family lands on its anchor up to 0/1
    trailing blanks. *)
Lemma gbo_1RB1RA_1LC1RD_0RB0LC_1RA0LA : forall j, lift (cden [] [] j BB1_1RB1RA_1LC1RD_0RB0LC_1RA0LA) = lift (Cin (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_1RB1RA_1LC1RD_0RB0LC_1RA0LA = (StB, (rep [S0;S0;S0] j ++ [S0;S0;S0;S0;S1], S0, ([]) ++ [S0]))).
  { unfold cden, BB1_1RB1RA_1LC1RD_0RB0LC_1RA0LA, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin (pow2 j) = (StB, (rep [S0;S0;S0] j ++ [S0;S0;S0;S0;S1], S0, []))).
  { unfold Cin_1RB1RA_1LC1RD_0RB0LC_1RA0LA. rewrite epow2_1RB1RA_1LC1RD_0RB0LC_1RA0LA.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_1RB1RA_1LC1RD_0RB0LC_1RA0LA. rewrite ?lift_app_blank. reflexivity.
Qed.

(** This family's all-ones fill IS the next chain's start.  [cview (fill
    (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    family's own overflow decomposition names the word. *)
Lemma gxi_1RB1RA_1LC1RD_0RB0LC_1RA0LA : forall j, Cin (fill (pow2 j)) = cden [] [] j BM0_1RB1RA_1LC1RD_0RB0LC_1RA0LA.
Proof.
  intro j.
  destruct (Alph_000_001_00.cview_none_Alph_000_001_00 (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin_1RB1RA_1LC1RD_0RB0LC_1RA0LA, cden, BM0_1RB1RA_1LC1RD_0RB0LC_1RA0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

Lemma gsn2_1RB1RA_1LC1RD_0RB0LC_1RA0LA : forall v i q0, cview v = (i, Some q0) ->
  Cin2 v = cden (Ap_Alph_000_001_00 q0 ++ [S1;S0;S1]) [] i AI20_1RB1RA_1LC1RD_0RB0LC_1RA0LA.
Proof.
  intros v i q0 E. destruct (Alph_000_001_00.cview_some_Alph_000_001_00 v i q0 E) as (H1 & _).
  unfold Cin2_1RB1RA_1LC1RD_0RB0LC_1RA0LA, cden, AI20_1RB1RA_1LC1RD_0RB0LC_1RA0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S0;S0;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen2_1RB1RA_1LC1RD_0RB0LC_1RA0LA : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Ap_Alph_000_001_00 q0 ++ [S1;S0;S1]) [] i AI21_1RB1RA_1LC1RD_0RB0LC_1RA0LA) = lift (Cin2 (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (Alph_000_001_00.cview_some_Alph_000_001_00 v i q0 E) as (_ & H2).
  unfold Cin2_1RB1RA_1LC1RD_0RB0LC_1RA0LA, cden, AI21_1RB1RA_1LC1RD_0RB0LC_1RA0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S0]) with (([]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S0;S0;S0] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin2_1RB1RA_1LC1RD_0RB0LC_1RA0LA : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin2 v) = Some c'
               /\ lift c' = lift (Cin2 (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (6 * i + 10), (cden (Ap_Alph_000_001_00 q0 ++ [S1;S0;S1]) [] i AI21_1RB1RA_1LC1RD_0RB0LC_1RA0LA).
  split; [lia|]. split; [| exact (gen2_1RB1RA_1LC1RD_0RB0LC_1RA0LA v i q0 E)].
  rewrite (gsn2_1RB1RA_1LC1RD_0RB0LC_1RA0LA v i q0 E).
  exact (srun_sound tm false true chn2_1RB1RA_1LC1RD_0RB0LC_1RA0LA AI20_1RB1RA_1LC1RD_0RB0LC_1RA0LA AI21_1RB1RA_1LC1RD_0RB0LC_1RA0LA 6 10
           run_inner2_1RB1RA_1LC1RD_0RB0LC_1RA0LA (Ap_Alph_000_001_00 q0 ++ [S1;S0;S1]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The chain into this family lands on its anchor up to 0/1
    trailing blanks. *)
Lemma gbo2_1RB1RA_1LC1RD_0RB0LC_1RA0LA : forall j, lift (cden [] [] j BM1_1RB1RA_1LC1RD_0RB0LC_1RA0LA) = lift (Cin2 (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BM1_1RB1RA_1LC1RD_0RB0LC_1RA0LA = (StB, (rep [S0;S0;S0] j ++ [S0;S0;S1;S0;S1], S0, ([]) ++ [S0]))).
  { unfold cden, BM1_1RB1RA_1LC1RD_0RB0LC_1RA0LA, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin2 (pow2 j) = (StB, (rep [S0;S0;S0] j ++ [S0;S0;S1;S0;S1], S0, []))).
  { unfold Cin2_1RB1RA_1LC1RD_0RB0LC_1RA0LA. rewrite epow22_1RB1RA_1LC1RD_0RB0LC_1RA0LA.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_1RB1RA_1LC1RD_0RB0LC_1RA0LA. rewrite ?lift_app_blank. reflexivity.
Qed.

(** This family's all-ones fill IS the next chain's start.  [cview (fill
    (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    family's own overflow decomposition names the word. *)
Lemma gxi2_1RB1RA_1LC1RD_0RB0LC_1RA0LA : forall j, Cin2 (fill (pow2 j)) = cden [] [] j BE0_1RB1RA_1LC1RD_0RB0LC_1RA0LA.
Proof.
  intro j.
  destruct (Alph_000_001_00.cview_none_Alph_000_001_00 (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin2_1RB1RA_1LC1RD_0RB0LC_1RA0LA, cden, BE0_1RB1RA_1LC1RD_0RB0LC_1RA0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

(** The interior lap, restated up to [lift] -- what [vis_via_ovf_lift] and
    [vis_via_fill] consume. *)
Lemma lapil_1RB1RA_1LC1RD_0RB0LC_1RA0LA : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof. exact lapi_1RB1RA_1LC1RD_0RB0LC_1RA0LA. Qed.

(** The outer OVERFLOW branch, composed.  The exponential cost is the
    [exists n] inside [inner_to_fill_lift]; no formula for it is ever
    written. *)
Lemma lapo_1RB1RA_1LC1RD_0RB0LC_1RA0LA : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E.
  apply (nested_overflow_lift tm Cc Cin2 lapin2_1RB1RA_1LC1RD_0RB0LC_1RA0LA p (pow2 j)).
  - assert (HB1 : exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
                  /\ lift c = lift (Cin (pow2 j))).
    { exists (6 * j + 21), (cden [] [] j BB1_1RB1RA_1LC1RD_0RB0LC_1RA0LA).
      split; [lia|]. split; [| exact (gbo_1RB1RA_1LC1RD_0RB0LC_1RA0LA j)].
      rewrite (gso_1RB1RA_1LC1RD_0RB0LC_1RA0LA p j E).
      exact (srun_sound tm true true chb_1RB1RA_1LC1RD_0RB0LC_1RA0LA B0_1RB1RA_1LC1RD_0RB0LC_1RA0LA BB1_1RB1RA_1LC1RD_0RB0LC_1RA0LA 6 21
               run_boot_1RB1RA_1LC1RD_0RB0LC_1RA0LA [] [] j ltac:(reflexivity) ltac:(reflexivity)). }
    assert (HB2 : exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
                  /\ lift c = lift (Cin2 (pow2 j))).
    { apply (boot_via_fill tm Cc Cin Cin2 lapin_1RB1RA_1LC1RD_0RB0LC_1RA0LA p (pow2 j) (pow2 j));
        [exact HB1|].
      exists (6 * j + 10), (cden [] [] j BM1_1RB1RA_1LC1RD_0RB0LC_1RA0LA).
      split; [| exact (gbo2_1RB1RA_1LC1RD_0RB0LC_1RA0LA j)].
      rewrite (gxi_1RB1RA_1LC1RD_0RB0LC_1RA0LA j).
      exact (srun_sound tm true true chm_1RB1RA_1LC1RD_0RB0LC_1RA0LA BM0_1RB1RA_1LC1RD_0RB0LC_1RA0LA BM1_1RB1RA_1LC1RD_0RB0LC_1RA0LA 6 10
               run_shift_1RB1RA_1LC1RD_0RB0LC_1RA0LA [] [] j ltac:(reflexivity) ltac:(reflexivity)). }
    exact HB2.
  - exists (6 * j + 23), (cden [] [] j B1_1RB1RA_1LC1RD_0RB0LC_1RA0LA).
    split; [| exact (geo_1RB1RA_1LC1RD_0RB0LC_1RA0LA p j E)].
    rewrite (gxi2_1RB1RA_1LC1RD_0RB0LC_1RA0LA j).
    exact (srun_sound tm true true che_1RB1RA_1LC1RD_0RB0LC_1RA0LA BE0_1RB1RA_1LC1RD_0RB0LC_1RA0LA B1_1RB1RA_1LC1RD_0RB0LC_1RA0LA 6 23
             run_exit_1RB1RA_1LC1RD_0RB0LC_1RA0LA [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.



(** ** The lap *)

Lemma lap_1RB1RA_1LC1RD_0RB0LC_1RA0LA : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB1RA_1LC1RD_0RB0LC_1RA0LA p j q0 E) as (n & c' & Hn & Hrun & Hlift).
    exists n, c'. split; [exact Hrun | split; [exact Hlift | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->). exact (lapo_1RB1RA_1LC1RD_0RB0LC_1RA0LA p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_1RB1RA_1LC1RD_0RB0LC_1RA0LA : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 31.
  assert (H : match csteps tm 31 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 31 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_1RB1RA_1LC1RD_0RB0LC_1RA0LA : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_1RB1RA_1LC1RD_0RB0LC_1RA0LA = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_1RB1RA_1LC1RD_0RB0LC_1RA0LA p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB1RA_1LC1RD_0RB0LC_1RA0LA p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_1RB1RA_1LC1RD_0RB0LC_1RA0LA : forall t, ~ In t pins_1RB1RA_1LC1RD_0RB0LC_1RA0LA ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n c', 0 < n /\ csteps tm n (Cc p0) = Some c'
                         /\ lift c' = lift (Cc (Pos.succ p0)))
    by exact lapi_1RB1RA_1LC1RD_0RB0LC_1RA0LA.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StA, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB1RA_1LC1RD_0RB0LC_1RA0LA [SWin 3; SWinR 6] (StA, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* A1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StA, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB1RA_1LC1RD_0RB0LC_1RA0LA [SWin 3; SWinR 7; SCycL 3 0; SWin 2] (StA, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* B0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StB, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB1RA_1LC1RD_0RB0LC_1RA0LA [] (StB, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* B1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StB, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB1RA_1LC1RD_0RB0LC_1RA0LA [SWin 3; SWinR 4] (StB, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* C0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StC, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB1RA_1LC1RD_0RB0LC_1RA0LA [SWin 3; SWinR 1] (StC, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* C1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StC, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB1RA_1LC1RD_0RB0LC_1RA0LA [SWin 1] (StC, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* D0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StD, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB1RA_1LC1RD_0RB0LC_1RA0LA [SWin 3; SWinR 5] (StD, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* D1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StD, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB1RA_1LC1RD_0RB0LC_1RA0LA [SWin 3; SWinR 7; SCycL 3 0; SWin 1] (StD, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
Qed.

Theorem nqhtrm_1RB1RA_1LC1RD_0RB0LC_1RA0LA : NeverQuasiHaltsTr tmm_1RB1RA_1LC1RD_0RB0LC_1RA0LA.
Proof.
  apply (glue_neverqhtr tmm_1RB1RA_1LC1RD_0RB0LC_1RA0LA pins_1RB1RA_1LC1RD_0RB0LC_1RA0LA Cc 1).
  - exact boot_1RB1RA_1LC1RD_0RB0LC_1RA0LA.
  - intros p _. apply lap_1RB1RA_1LC1RD_0RB0LC_1RA0LA.
  - intros t Ht p _. apply fire_1RB1RA_1LC1RD_0RB0LC_1RA0LA. exact Ht.
Qed.

Theorem nqhtr_1RB1RA_1LC1RD_0RB0LC_1RA0LA : NeverQuasiHaltsTr tm_1RB1RA_1LC1RD_0RB0LC_1RA0LA.
Proof. apply (neverqhtr_mirror tm_1RB1RA_1LC1RD_0RB0LC_1RA0LA). rewrite mirror_ok_1RB1RA_1LC1RD_0RB0LC_1RA0LA. exact nqhtrm_1RB1RA_1LC1RD_0RB0LC_1RA0LA. Qed.

Theorem nonhalt_1RB1RA_1LC1RD_0RB0LC_1RA0LA : NonHalt tm_1RB1RA_1LC1RD_0RB0LC_1RA0LA.
Proof. apply never_qh_tr_nonhalt, nqhtr_1RB1RA_1LC1RD_0RB0LC_1RA0LA. Qed.
