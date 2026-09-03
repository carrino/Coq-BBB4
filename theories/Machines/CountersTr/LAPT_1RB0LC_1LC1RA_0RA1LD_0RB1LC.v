(** * LAPT_1RB0LC_1LC1RA_0RA1LD_0RB1LC: TRANSITION-LEVEL board for machine 1RB0LC_1LC1RA_0RA1LD_0RB1LC, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Jp digit alphabet (JpCounter.v), anchored at

      Cc p = (StD, (Jp p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  4*j+4 steps
      overflow  (cview p = (S j, None)):   boot 4*j+9, then the inner counter's own laps to the
                                           all-ones fill, then exit 4*j+8

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 192 interior anchors (interior); 6 overflow phases, j = 2..7 (984 inner laps, 4 counts each) (nested overflow).
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter JpCounter LapCertGlue LapCertGlueLift IXPGadgets NestedLap NestedLapLift NestedLap2.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
From BBB4 Require Import BBBT4_Statement.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr.
Import ListNotations.

Definition mk_1RB0LC_1LC1RA_0RA1LD_0RB1LC (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB0LC_1LC1RA_0RA1LD_0RB1LC.

(** 1RB0LC_1LC1RA_0RA1LD_0RB1LC *)
(** 1RB0LC_1LC1RA_0RA1LD_0RB1LC -- the real machine (its counter grows RIGHT). *)
Definition tm_1RB0LC_1LC1RA_0RA1LD_0RB1LC : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StC
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StA
  | StC, S0 => mk S0 DR StA | StC, S1 => mk S1 DL StD
  | StD, S0 => mk S0 DR StB | StD, S1 => mk S1 DL StC end.

(** Its mirror 1LB0RC_1RC1LA_0LA1RD_0LB1RC: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_1RB0LC_1LC1RA_0RA1LD_0RB1LC : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => mk S0 DR StC
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DL StA
  | StC, S0 => mk S0 DL StA | StC, S1 => mk S1 DR StD
  | StD, S0 => mk S0 DL StB | StD, S1 => mk S1 DR StC end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_1RB0LC_1LC1RA_0RA1LD_0RB1LC : list Instr := [].
Definition tmw_1RB0LC_1LC1RA_0RA1LD_0RB1LC : TM := tm_wrap_trs tmm_1RB0LC_1LC1RA_0RA1LD_0RB1LC pins_1RB0LC_1LC1RA_0RA1LD_0RB1LC.
Local Notation tm := tmw_1RB0LC_1LC1RA_0RA1LD_0RB1LC.

Lemma mirror_ok_1RB0LC_1LC1RA_0RA1LD_0RB1LC : mirror_tm tm_1RB0LC_1LC1RA_0RA1LD_0RB1LC = tmm_1RB0LC_1LC1RA_0RA1LD_0RB1LC.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_1RB0LC_1LC1RA_0RA1LD_0RB1LC (p : positive) : cconf := (StD, (Jp p ++ [S0], S0, [])).
Local Notation Cc := Cc_1RB0LC_1LC1RA_0RA1LD_0RB1LC.

(** ** The certificate *)

Definition A0_1RB0LC_1LC1RA_0RA1LD_0RB1LC : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition A1_1RB0LC_1LC1RA_0RA1LD_0RB1LC : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chi_1RB0LC_1LC1RA_0RA1LD_0RB1LC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_int_1RB0LC_1LC1RA_0RA1LD_0RB1LC : srun tm false true chi_1RB0LC_1LC1RA_0RA1LD_0RB1LC A0_1RB0LC_1LC1RA_0RA1LD_0RB1LC = Some (A1_1RB0LC_1LC1RA_0RA1LD_0RB1LC, 4, 4).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB0LC_1LC1RA_0RA1LD_0RB1LC : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_1RB0LC_1LC1RA_0RA1LD_0RB1LC : sconf := mkC StD (mkS [] [S1;S1] 1 1 [S1;S0]) S0 (mkS [] [] 0 0 []).
(** ** The FIRST INNER anchor family -- Jp at StA *)
Definition Cin_1RB0LC_1LC1RA_0RA1LD_0RB1LC (v : positive) : cconf := (StA, (Jp v ++ [S1], S0, [])).
Local Notation Cin := Cin_1RB0LC_1LC1RA_0RA1LD_0RB1LC.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow2_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall n, Jp (pow2 n) = rep [S1;S1] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap -- ordinary and affine.  Iterating it to the fill is
    where a [Theta(2^j)] lives, and [inner_to_fill_lift] keeps it inside an
    existential. *)
Definition AI0_1RB0LC_1LC1RA_0RA1LD_0RB1LC : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition AI1_1RB0LC_1LC1RA_0RA1LD_0RB1LC : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S0] [] 0 0 []).
Definition chn_1RB0LC_1LC1RA_0RA1LD_0RB1LC : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWinR 4].

Lemma run_inner_1RB0LC_1LC1RA_0RA1LD_0RB1LC : srun tm false true chn_1RB0LC_1LC1RA_0RA1LD_0RB1LC AI0_1RB0LC_1LC1RA_0RA1LD_0RB1LC = Some (AI1_1RB0LC_1LC1RA_0RA1LD_0RB1LC, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** ** The SECOND INNER anchor family -- Jp at StA *)
Definition Cin2_1RB0LC_1LC1RA_0RA1LD_0RB1LC (v : positive) : cconf := (StA, (Jp v ++ [], S0, [])).
Local Notation Cin2 := Cin2_1RB0LC_1LC1RA_0RA1LD_0RB1LC.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow22_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall n, Jp (pow2 n) = rep [S1;S1] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap -- ordinary and affine.  Iterating it to the fill is
    where a [Theta(2^j)] lives, and [inner_to_fill_lift] keeps it inside an
    existential. *)
Definition AI20_1RB0LC_1LC1RA_0RA1LD_0RB1LC : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition AI21_1RB0LC_1LC1RA_0RA1LD_0RB1LC : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S0] [] 0 0 []).
Definition chn2_1RB0LC_1LC1RA_0RA1LD_0RB1LC : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWinR 4].

Lemma run_inner2_1RB0LC_1LC1RA_0RA1LD_0RB1LC : srun tm false true chn2_1RB0LC_1LC1RA_0RA1LD_0RB1LC AI20_1RB0LC_1LC1RA_0RA1LD_0RB1LC = Some (AI21_1RB0LC_1LC1RA_0RA1LD_0RB1LC, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** ** The THIRD INNER anchor family -- Jp at StD *)
Definition Cin3_1RB0LC_1LC1RA_0RA1LD_0RB1LC (v : positive) : cconf := (StD, (Jp v ++ [S1;S1;S1], S0, [])).
Local Notation Cin3 := Cin3_1RB0LC_1LC1RA_0RA1LD_0RB1LC.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow23_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall n, Jp (pow2 n) = rep [S1;S1] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap -- ordinary and affine.  Iterating it to the fill is
    where a [Theta(2^j)] lives, and [inner_to_fill_lift] keeps it inside an
    existential. *)
Definition AI30_1RB0LC_1LC1RA_0RA1LD_0RB1LC : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition AI31_1RB0LC_1LC1RA_0RA1LD_0RB1LC : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chn3_1RB0LC_1LC1RA_0RA1LD_0RB1LC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_inner3_1RB0LC_1LC1RA_0RA1LD_0RB1LC : srun tm false true chn3_1RB0LC_1LC1RA_0RA1LD_0RB1LC AI30_1RB0LC_1LC1RA_0RA1LD_0RB1LC = Some (AI31_1RB0LC_1LC1RA_0RA1LD_0RB1LC, 4, 4).
Proof. vm_compute. reflexivity. Qed.

(** ** The FOURTH INNER anchor family -- Jp at StD *)
Definition Cin4_1RB0LC_1LC1RA_0RA1LD_0RB1LC (v : positive) : cconf := (StD, (Jp v ++ [S0;S1;S1], S0, [])).
Local Notation Cin4 := Cin4_1RB0LC_1LC1RA_0RA1LD_0RB1LC.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow24_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall n, Jp (pow2 n) = rep [S1;S1] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap -- ordinary and affine.  Iterating it to the fill is
    where a [Theta(2^j)] lives, and [inner_to_fill_lift] keeps it inside an
    existential. *)
Definition AI40_1RB0LC_1LC1RA_0RA1LD_0RB1LC : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition AI41_1RB0LC_1LC1RA_0RA1LD_0RB1LC : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chn4_1RB0LC_1LC1RA_0RA1LD_0RB1LC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_inner4_1RB0LC_1LC1RA_0RA1LD_0RB1LC : srun tm false true chn4_1RB0LC_1LC1RA_0RA1LD_0RB1LC AI40_1RB0LC_1LC1RA_0RA1LD_0RB1LC = Some (AI41_1RB0LC_1LC1RA_0RA1LD_0RB1LC, 4, 4).
Proof. vm_compute. reflexivity. Qed.

(** *** boot: the outer overflow anchor -> the first inner anchor at [pow2 j] *)
Definition BB1_1RB0LC_1LC1RA_0RA1LD_0RB1LC : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S1]) S0 (mkS [S0] [] 0 0 []).
Definition chb_1RB0LC_1LC1RA_0RA1LD_0RB1LC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 3; SCycR 2; SWin 4].

Lemma run_boot_1RB0LC_1LC1RA_0RA1LD_0RB1LC : srun tm true true chb_1RB0LC_1LC1RA_0RA1LD_0RB1LC B0_1RB0LC_1LC1RA_0RA1LD_0RB1LC = Some (BB1_1RB0LC_1LC1RA_0RA1LD_0RB1LC, 4, 9).
Proof. vm_compute. reflexivity. Qed.

(** *** shift: count 1's all-ones fill -> count 2's anchor.
    WAVE18 section 4c -- "count 8->15, shift, count 8->15 again". *)
Definition BM0_1RB0LC_1LC1RA_0RA1LD_0RB1LC : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition BM1_1RB0LC_1LC1RA_0RA1LD_0RB1LC : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S0] [] 0 0 []).
Definition chm_1RB0LC_1LC1RA_0RA1LD_0RB1LC : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWinR 4].

Lemma run_shift_1RB0LC_1LC1RA_0RA1LD_0RB1LC : srun tm true true chm_1RB0LC_1LC1RA_0RA1LD_0RB1LC BM0_1RB0LC_1LC1RA_0RA1LD_0RB1LC = Some (BM1_1RB0LC_1LC1RA_0RA1LD_0RB1LC, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** *** shift: count 2's all-ones fill -> count 3's anchor.
    WAVE18 section 4c -- "count 8->15, shift, count 8->15 again". *)
Definition BM30_1RB0LC_1LC1RA_0RA1LD_0RB1LC : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1]) S0 (mkS [] [] 0 0 []).
Definition BM31_1RB0LC_1LC1RA_0RA1LD_0RB1LC : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S1;S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chm3_1RB0LC_1LC1RA_0RA1LD_0RB1LC : list lstep := [SCycL 2 0; SWin 1; SWinL 5; SCycR 2; SWinR 1; SUnrotL 1].

Lemma run_shift3_1RB0LC_1LC1RA_0RA1LD_0RB1LC : srun tm true true chm3_1RB0LC_1LC1RA_0RA1LD_0RB1LC BM30_1RB0LC_1LC1RA_0RA1LD_0RB1LC = Some (BM31_1RB0LC_1LC1RA_0RA1LD_0RB1LC, 4, 7).
Proof. vm_compute. reflexivity. Qed.

(** *** shift: count 3's all-ones fill -> count 4's anchor.
    WAVE18 section 4c -- "count 8->15, shift, count 8->15 again". *)
Definition BM40_1RB0LC_1LC1RA_0RA1LD_0RB1LC : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1;S1;S1]) S0 (mkS [] [] 0 0 []).
Definition BM41_1RB0LC_1LC1RA_0RA1LD_0RB1LC : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0;S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chm4_1RB0LC_1LC1RA_0RA1LD_0RB1LC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_shift4_1RB0LC_1LC1RA_0RA1LD_0RB1LC : srun tm true true chm4_1RB0LC_1LC1RA_0RA1LD_0RB1LC BM40_1RB0LC_1LC1RA_0RA1LD_0RB1LC = Some (BM41_1RB0LC_1LC1RA_0RA1LD_0RB1LC, 4, 4).
Proof. vm_compute. reflexivity. Qed.

(** *** exit: the last inner all-ones fill -> the outer successor *)
Definition BE0_1RB0LC_1LC1RA_0RA1LD_0RB1LC : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S0;S1;S1]) S0 (mkS [] [] 0 0 []).
Definition che_1RB0LC_1LC1RA_0RA1LD_0RB1LC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 6; SCycR 2; SWin 1; SRotL 1; SFoldL 1].

Lemma run_exit_1RB0LC_1LC1RA_0RA1LD_0RB1LC : srun tm true true che_1RB0LC_1LC1RA_0RA1LD_0RB1LC BE0_1RB0LC_1LC1RA_0RA1LD_0RB1LC = Some (B1_1RB0LC_1LC1RA_0RA1LD_0RB1LC, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Jp q0 ++ [S0]) [] j A0_1RB0LC_1LC1RA_0RA1LD_0RB1LC.
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (H1 & _).
  unfold Cc_1RB0LC_1LC1RA_0RA1LD_0RB1LC, cden, A0_1RB0LC_1LC1RA_0RA1LD_0RB1LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gei_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall p j q0, cview p = (j, Some q0) ->
  cden (Jp q0 ++ [S0]) [] j A1_1RB0LC_1LC1RA_0RA1LD_0RB1LC = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (_ & H2).
  unfold Cc_1RB0LC_1LC1RA_0RA1LD_0RB1LC, cden, A1_1RB0LC_1LC1RA_0RA1LD_0RB1LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (4 * j + 4). split; [lia|].
  rewrite (gsi_1RB0LC_1LC1RA_0RA1LD_0RB1LC p j q0 E).
  rewrite (srun_sound tm false true chi_1RB0LC_1LC1RA_0RA1LD_0RB1LC A0_1RB0LC_1LC1RA_0RA1LD_0RB1LC A1_1RB0LC_1LC1RA_0RA1LD_0RB1LC 4 4
             run_int_1RB0LC_1LC1RA_0RA1LD_0RB1LC (Jp q0 ++ [S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_1RB0LC_1LC1RA_0RA1LD_0RB1LC p j q0 E).
Qed.

Lemma gso_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_1RB0LC_1LC1RA_0RA1LD_0RB1LC.
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (H1 & _).
  unfold Cc_1RB0LC_1LC1RA_0RA1LD_0RB1LC, cden, B0_1RB0LC_1LC1RA_0RA1LD_0RB1LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB0LC_1LC1RA_0RA1LD_0RB1LC) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB0LC_1LC1RA_0RA1LD_0RB1LC
             = (StD, (rep [S1;S1] (S j) ++ [S1;S0], S0, []))).
  { unfold cden, B1_1RB0LC_1LC1RA_0RA1LD_0RB1LC, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StD, (rep [S1;S1] (S j) ++ [S1;S0], S0, []))).
  { unfold Cc_1RB0LC_1LC1RA_0RA1LD_0RB1LC. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. reflexivity.
Qed.

Lemma gsn_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall v i q0, cview v = (i, Some q0) ->
  Cin v = cden (Jp q0 ++ [S1]) [] i AI0_1RB0LC_1LC1RA_0RA1LD_0RB1LC.
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (H1 & _).
  unfold Cin_1RB0LC_1LC1RA_0RA1LD_0RB1LC, cden, AI0_1RB0LC_1LC1RA_0RA1LD_0RB1LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Jp q0 ++ [S1]) [] i AI1_1RB0LC_1LC1RA_0RA1LD_0RB1LC) = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (_ & H2).
  unfold Cin_1RB0LC_1LC1RA_0RA1LD_0RB1LC, cden, AI1_1RB0LC_1LC1RA_0RA1LD_0RB1LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S0]) with (([]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 8), (cden (Jp q0 ++ [S1]) [] i AI1_1RB0LC_1LC1RA_0RA1LD_0RB1LC).
  split; [lia|]. split; [| exact (gen_1RB0LC_1LC1RA_0RA1LD_0RB1LC v i q0 E)].
  rewrite (gsn_1RB0LC_1LC1RA_0RA1LD_0RB1LC v i q0 E).
  exact (srun_sound tm false true chn_1RB0LC_1LC1RA_0RA1LD_0RB1LC AI0_1RB0LC_1LC1RA_0RA1LD_0RB1LC AI1_1RB0LC_1LC1RA_0RA1LD_0RB1LC 4 8
           run_inner_1RB0LC_1LC1RA_0RA1LD_0RB1LC (Jp q0 ++ [S1]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The chain into this family lands on its anchor up to 0/1
    trailing blanks. *)
Lemma gbo_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall j, lift (cden [] [] j BB1_1RB0LC_1LC1RA_0RA1LD_0RB1LC) = lift (Cin (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_1RB0LC_1LC1RA_0RA1LD_0RB1LC = (StA, (rep [S1;S1] j ++ [S1;S1], S0, ([]) ++ [S0]))).
  { unfold cden, BB1_1RB0LC_1LC1RA_0RA1LD_0RB1LC, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin (pow2 j) = (StA, (rep [S1;S1] j ++ [S1;S1], S0, []))).
  { unfold Cin_1RB0LC_1LC1RA_0RA1LD_0RB1LC. rewrite epow2_1RB0LC_1LC1RA_0RA1LD_0RB1LC.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_1RB0LC_1LC1RA_0RA1LD_0RB1LC. rewrite ?lift_app_blank. reflexivity.
Qed.

(** This family's all-ones fill IS the next chain's start.  [cview (fill
    (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    family's own overflow decomposition names the word. *)
Lemma gxi_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall j, Cin (fill (pow2 j)) = cden [] [] j BM0_1RB0LC_1LC1RA_0RA1LD_0RB1LC.
Proof.
  intro j.
  destruct (JpCounter.cview_none_J (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin_1RB0LC_1LC1RA_0RA1LD_0RB1LC, cden, BM0_1RB0LC_1LC1RA_0RA1LD_0RB1LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

Lemma gsn2_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall v i q0, cview v = (i, Some q0) ->
  Cin2 v = cden (Jp q0 ++ []) [] i AI20_1RB0LC_1LC1RA_0RA1LD_0RB1LC.
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (H1 & _).
  unfold Cin2_1RB0LC_1LC1RA_0RA1LD_0RB1LC, cden, AI20_1RB0LC_1LC1RA_0RA1LD_0RB1LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen2_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Jp q0 ++ []) [] i AI21_1RB0LC_1LC1RA_0RA1LD_0RB1LC) = lift (Cin2 (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (_ & H2).
  unfold Cin2_1RB0LC_1LC1RA_0RA1LD_0RB1LC, cden, AI21_1RB0LC_1LC1RA_0RA1LD_0RB1LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S0]) with (([]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin2_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin2 v) = Some c'
               /\ lift c' = lift (Cin2 (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 8), (cden (Jp q0 ++ []) [] i AI21_1RB0LC_1LC1RA_0RA1LD_0RB1LC).
  split; [lia|]. split; [| exact (gen2_1RB0LC_1LC1RA_0RA1LD_0RB1LC v i q0 E)].
  rewrite (gsn2_1RB0LC_1LC1RA_0RA1LD_0RB1LC v i q0 E).
  exact (srun_sound tm false true chn2_1RB0LC_1LC1RA_0RA1LD_0RB1LC AI20_1RB0LC_1LC1RA_0RA1LD_0RB1LC AI21_1RB0LC_1LC1RA_0RA1LD_0RB1LC 4 8
           run_inner2_1RB0LC_1LC1RA_0RA1LD_0RB1LC (Jp q0 ++ []) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The chain into this family lands on its anchor up to 1/1
    trailing blanks. *)
Lemma gbo2_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall j, lift (cden [] [] j BM1_1RB0LC_1LC1RA_0RA1LD_0RB1LC) = lift (Cin2 (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BM1_1RB0LC_1LC1RA_0RA1LD_0RB1LC = (StA, ((rep [S1;S1] j ++ [S1]) ++ [S0], S0, ([]) ++ [S0]))).
  { unfold cden, BM1_1RB0LC_1LC1RA_0RA1LD_0RB1LC, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin2 (pow2 j) = (StA, (rep [S1;S1] j ++ [S1], S0, []))).
  { unfold Cin2_1RB0LC_1LC1RA_0RA1LD_0RB1LC. rewrite epow22_1RB0LC_1LC1RA_0RA1LD_0RB1LC.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_1RB0LC_1LC1RA_0RA1LD_0RB1LC. rewrite ?lift_app_blank. reflexivity.
Qed.

(** This family's all-ones fill IS the next chain's start.  [cview (fill
    (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    family's own overflow decomposition names the word. *)
Lemma gxi2_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall j, Cin2 (fill (pow2 j)) = cden [] [] j BM30_1RB0LC_1LC1RA_0RA1LD_0RB1LC.
Proof.
  intro j.
  destruct (JpCounter.cview_none_J (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin2_1RB0LC_1LC1RA_0RA1LD_0RB1LC, cden, BM30_1RB0LC_1LC1RA_0RA1LD_0RB1LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

Lemma gsn3_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall v i q0, cview v = (i, Some q0) ->
  Cin3 v = cden (Jp q0 ++ [S1;S1;S1]) [] i AI30_1RB0LC_1LC1RA_0RA1LD_0RB1LC.
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (H1 & _).
  unfold Cin3_1RB0LC_1LC1RA_0RA1LD_0RB1LC, cden, AI30_1RB0LC_1LC1RA_0RA1LD_0RB1LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen3_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Jp q0 ++ [S1;S1;S1]) [] i AI31_1RB0LC_1LC1RA_0RA1LD_0RB1LC) = lift (Cin3 (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (_ & H2).
  unfold Cin3_1RB0LC_1LC1RA_0RA1LD_0RB1LC, cden, AI31_1RB0LC_1LC1RA_0RA1LD_0RB1LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin3_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin3 v) = Some c'
               /\ lift c' = lift (Cin3 (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 4), (cden (Jp q0 ++ [S1;S1;S1]) [] i AI31_1RB0LC_1LC1RA_0RA1LD_0RB1LC).
  split; [lia|]. split; [| exact (gen3_1RB0LC_1LC1RA_0RA1LD_0RB1LC v i q0 E)].
  rewrite (gsn3_1RB0LC_1LC1RA_0RA1LD_0RB1LC v i q0 E).
  exact (srun_sound tm false true chn3_1RB0LC_1LC1RA_0RA1LD_0RB1LC AI30_1RB0LC_1LC1RA_0RA1LD_0RB1LC AI31_1RB0LC_1LC1RA_0RA1LD_0RB1LC 4 4
           run_inner3_1RB0LC_1LC1RA_0RA1LD_0RB1LC (Jp q0 ++ [S1;S1;S1]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The chain into this family lands on its anchor up to 0/0
    trailing blanks. *)
Lemma gbo3_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall j, lift (cden [] [] j BM31_1RB0LC_1LC1RA_0RA1LD_0RB1LC) = lift (Cin3 (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BM31_1RB0LC_1LC1RA_0RA1LD_0RB1LC = (StD, (rep [S1;S1] j ++ [S1;S1;S1;S1], S0, []))).
  { unfold cden, BM31_1RB0LC_1LC1RA_0RA1LD_0RB1LC, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin3 (pow2 j) = (StD, (rep [S1;S1] j ++ [S1;S1;S1;S1], S0, []))).
  { unfold Cin3_1RB0LC_1LC1RA_0RA1LD_0RB1LC. rewrite epow23_1RB0LC_1LC1RA_0RA1LD_0RB1LC.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_1RB0LC_1LC1RA_0RA1LD_0RB1LC. rewrite ?lift_app_blank. reflexivity.
Qed.

(** This family's all-ones fill IS the next chain's start.  [cview (fill
    (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    family's own overflow decomposition names the word. *)
Lemma gxi3_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall j, Cin3 (fill (pow2 j)) = cden [] [] j BM40_1RB0LC_1LC1RA_0RA1LD_0RB1LC.
Proof.
  intro j.
  destruct (JpCounter.cview_none_J (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin3_1RB0LC_1LC1RA_0RA1LD_0RB1LC, cden, BM40_1RB0LC_1LC1RA_0RA1LD_0RB1LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

Lemma gsn4_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall v i q0, cview v = (i, Some q0) ->
  Cin4 v = cden (Jp q0 ++ [S0;S1;S1]) [] i AI40_1RB0LC_1LC1RA_0RA1LD_0RB1LC.
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (H1 & _).
  unfold Cin4_1RB0LC_1LC1RA_0RA1LD_0RB1LC, cden, AI40_1RB0LC_1LC1RA_0RA1LD_0RB1LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen4_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Jp q0 ++ [S0;S1;S1]) [] i AI41_1RB0LC_1LC1RA_0RA1LD_0RB1LC) = lift (Cin4 (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (_ & H2).
  unfold Cin4_1RB0LC_1LC1RA_0RA1LD_0RB1LC, cden, AI41_1RB0LC_1LC1RA_0RA1LD_0RB1LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin4_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin4 v) = Some c'
               /\ lift c' = lift (Cin4 (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 4), (cden (Jp q0 ++ [S0;S1;S1]) [] i AI41_1RB0LC_1LC1RA_0RA1LD_0RB1LC).
  split; [lia|]. split; [| exact (gen4_1RB0LC_1LC1RA_0RA1LD_0RB1LC v i q0 E)].
  rewrite (gsn4_1RB0LC_1LC1RA_0RA1LD_0RB1LC v i q0 E).
  exact (srun_sound tm false true chn4_1RB0LC_1LC1RA_0RA1LD_0RB1LC AI40_1RB0LC_1LC1RA_0RA1LD_0RB1LC AI41_1RB0LC_1LC1RA_0RA1LD_0RB1LC 4 4
           run_inner4_1RB0LC_1LC1RA_0RA1LD_0RB1LC (Jp q0 ++ [S0;S1;S1]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The chain into this family lands on its anchor up to 0/0
    trailing blanks. *)
Lemma gbo4_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall j, lift (cden [] [] j BM41_1RB0LC_1LC1RA_0RA1LD_0RB1LC) = lift (Cin4 (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BM41_1RB0LC_1LC1RA_0RA1LD_0RB1LC = (StD, (rep [S1;S1] j ++ [S1;S0;S1;S1], S0, []))).
  { unfold cden, BM41_1RB0LC_1LC1RA_0RA1LD_0RB1LC, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin4 (pow2 j) = (StD, (rep [S1;S1] j ++ [S1;S0;S1;S1], S0, []))).
  { unfold Cin4_1RB0LC_1LC1RA_0RA1LD_0RB1LC. rewrite epow24_1RB0LC_1LC1RA_0RA1LD_0RB1LC.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_1RB0LC_1LC1RA_0RA1LD_0RB1LC. rewrite ?lift_app_blank. reflexivity.
Qed.

(** This family's all-ones fill IS the next chain's start.  [cview (fill
    (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    family's own overflow decomposition names the word. *)
Lemma gxi4_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall j, Cin4 (fill (pow2 j)) = cden [] [] j BE0_1RB0LC_1LC1RA_0RA1LD_0RB1LC.
Proof.
  intro j.
  destruct (JpCounter.cview_none_J (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin4_1RB0LC_1LC1RA_0RA1LD_0RB1LC, cden, BE0_1RB0LC_1LC1RA_0RA1LD_0RB1LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

(** The interior lap, restated up to [lift] -- what [vis_via_ovf_lift] and
    [vis_via_fill] consume. *)
Lemma lapil_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof. intros p j q0 E. destruct (lapi_1RB0LC_1LC1RA_0RA1LD_0RB1LC p j q0 E) as (n & Hn & Hr).
  exists n, (Cc (Pos.succ p)).
  split; [exact Hn | split; [exact Hr | reflexivity]]. Qed.

(** The outer OVERFLOW branch, composed.  The exponential cost is the
    [exists n] inside [inner_to_fill_lift]; no formula for it is ever
    written. *)
Lemma lapo_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E.
  apply (nested_overflow_lift tm Cc Cin4 lapin4_1RB0LC_1LC1RA_0RA1LD_0RB1LC p (pow2 j)).
  - assert (HB1 : exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
                  /\ lift c = lift (Cin (pow2 j))).
    { exists (4 * j + 9), (cden [] [] j BB1_1RB0LC_1LC1RA_0RA1LD_0RB1LC).
      split; [lia|]. split; [| exact (gbo_1RB0LC_1LC1RA_0RA1LD_0RB1LC j)].
      rewrite (gso_1RB0LC_1LC1RA_0RA1LD_0RB1LC p j E).
      exact (srun_sound tm true true chb_1RB0LC_1LC1RA_0RA1LD_0RB1LC B0_1RB0LC_1LC1RA_0RA1LD_0RB1LC BB1_1RB0LC_1LC1RA_0RA1LD_0RB1LC 4 9
               run_boot_1RB0LC_1LC1RA_0RA1LD_0RB1LC [] [] j ltac:(reflexivity) ltac:(reflexivity)). }
    assert (HB2 : exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
                  /\ lift c = lift (Cin2 (pow2 j))).
    { apply (boot_via_fill tm Cc Cin Cin2 lapin_1RB0LC_1LC1RA_0RA1LD_0RB1LC p (pow2 j) (pow2 j));
        [exact HB1|].
      exists (4 * j + 8), (cden [] [] j BM1_1RB0LC_1LC1RA_0RA1LD_0RB1LC).
      split; [| exact (gbo2_1RB0LC_1LC1RA_0RA1LD_0RB1LC j)].
      rewrite (gxi_1RB0LC_1LC1RA_0RA1LD_0RB1LC j).
      exact (srun_sound tm true true chm_1RB0LC_1LC1RA_0RA1LD_0RB1LC BM0_1RB0LC_1LC1RA_0RA1LD_0RB1LC BM1_1RB0LC_1LC1RA_0RA1LD_0RB1LC 4 8
               run_shift_1RB0LC_1LC1RA_0RA1LD_0RB1LC [] [] j ltac:(reflexivity) ltac:(reflexivity)). }
    assert (HB3 : exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
                  /\ lift c = lift (Cin3 (pow2 j))).
    { apply (boot_via_fill tm Cc Cin2 Cin3 lapin2_1RB0LC_1LC1RA_0RA1LD_0RB1LC p (pow2 j) (pow2 j));
        [exact HB2|].
      exists (4 * j + 7), (cden [] [] j BM31_1RB0LC_1LC1RA_0RA1LD_0RB1LC).
      split; [| exact (gbo3_1RB0LC_1LC1RA_0RA1LD_0RB1LC j)].
      rewrite (gxi2_1RB0LC_1LC1RA_0RA1LD_0RB1LC j).
      exact (srun_sound tm true true chm3_1RB0LC_1LC1RA_0RA1LD_0RB1LC BM30_1RB0LC_1LC1RA_0RA1LD_0RB1LC BM31_1RB0LC_1LC1RA_0RA1LD_0RB1LC 4 7
               run_shift3_1RB0LC_1LC1RA_0RA1LD_0RB1LC [] [] j ltac:(reflexivity) ltac:(reflexivity)). }
    assert (HB4 : exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
                  /\ lift c = lift (Cin4 (pow2 j))).
    { apply (boot_via_fill tm Cc Cin3 Cin4 lapin3_1RB0LC_1LC1RA_0RA1LD_0RB1LC p (pow2 j) (pow2 j));
        [exact HB3|].
      exists (4 * j + 4), (cden [] [] j BM41_1RB0LC_1LC1RA_0RA1LD_0RB1LC).
      split; [| exact (gbo4_1RB0LC_1LC1RA_0RA1LD_0RB1LC j)].
      rewrite (gxi3_1RB0LC_1LC1RA_0RA1LD_0RB1LC j).
      exact (srun_sound tm true true chm4_1RB0LC_1LC1RA_0RA1LD_0RB1LC BM40_1RB0LC_1LC1RA_0RA1LD_0RB1LC BM41_1RB0LC_1LC1RA_0RA1LD_0RB1LC 4 4
               run_shift4_1RB0LC_1LC1RA_0RA1LD_0RB1LC [] [] j ltac:(reflexivity) ltac:(reflexivity)). }
    exact HB4.
  - exists (4 * j + 8), (cden [] [] j B1_1RB0LC_1LC1RA_0RA1LD_0RB1LC).
    split; [| exact (geo_1RB0LC_1LC1RA_0RA1LD_0RB1LC p j E)].
    rewrite (gxi4_1RB0LC_1LC1RA_0RA1LD_0RB1LC j).
    exact (srun_sound tm true true che_1RB0LC_1LC1RA_0RA1LD_0RB1LC BE0_1RB0LC_1LC1RA_0RA1LD_0RB1LC B1_1RB0LC_1LC1RA_0RA1LD_0RB1LC 4 8
             run_exit_1RB0LC_1LC1RA_0RA1LD_0RB1LC [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.



(** ** The lap *)

Lemma lap_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB0LC_1LC1RA_0RA1LD_0RB1LC p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->). exact (lapo_1RB0LC_1LC1RA_0RA1LD_0RB1LC p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_1RB0LC_1LC1RA_0RA1LD_0RB1LC : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 7.
  assert (H : match csteps tm 7 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 7 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_1RB0LC_1LC1RA_0RA1LD_0RB1LC = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_1RB0LC_1LC1RA_0RA1LD_0RB1LC p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB0LC_1LC1RA_0RA1LD_0RB1LC p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_1RB0LC_1LC1RA_0RA1LD_0RB1LC : forall t, ~ In t pins_1RB0LC_1LC1RA_0RA1LD_0RB1LC ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_1RB0LC_1LC1RA_0RA1LD_0RB1LC.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_via_ovf tm Cc Hi (StA, S0)), fireo_1RB0LC_1LC1RA_0RA1LD_0RB1LC
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1]).
    vm_compute; reflexivity.
  - (* A1 *)
    apply (fire_via_ovf tm Cc Hi (StA, S1)), fireo_1RB0LC_1LC1RA_0RA1LD_0RB1LC
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 3; SCycR 2; SWin 2]).
    vm_compute; reflexivity.
  - (* B0 *)
    apply (fire_via_ovf tm Cc Hi (StB, S0)), fireo_1RB0LC_1LC1RA_0RA1LD_0RB1LC
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 1]).
    vm_compute; reflexivity.
  - (* B1 *)
    apply (fire_via_ovf tm Cc Hi (StB, S1)), fireo_1RB0LC_1LC1RA_0RA1LD_0RB1LC
      with (l := [SRotL 1; SWin 1]).
    vm_compute; reflexivity.
  - (* C0 *)
    apply (fire_via_ovf tm Cc Hi (StC, S0)), fireo_1RB0LC_1LC1RA_0RA1LD_0RB1LC
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 3; SCycR 2; SWin 1]).
    vm_compute; reflexivity.
  - (* C1 *)
    apply (fire_via_ovf tm Cc Hi (StC, S1)), fireo_1RB0LC_1LC1RA_0RA1LD_0RB1LC
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 2]).
    vm_compute; reflexivity.
  - (* D0 *)
    apply (fire_via_ovf tm Cc Hi (StD, S0)), fireo_1RB0LC_1LC1RA_0RA1LD_0RB1LC
      with (l := []).
    vm_compute; reflexivity.
  - (* D1 *)
    apply (fire_via_ovf tm Cc Hi (StD, S1)), fireo_1RB0LC_1LC1RA_0RA1LD_0RB1LC
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 3]).
    vm_compute; reflexivity.
Qed.

Theorem nqhtrm_1RB0LC_1LC1RA_0RA1LD_0RB1LC : NeverQuasiHaltsTr tmm_1RB0LC_1LC1RA_0RA1LD_0RB1LC.
Proof.
  apply (glue_neverqhtr tmm_1RB0LC_1LC1RA_0RA1LD_0RB1LC pins_1RB0LC_1LC1RA_0RA1LD_0RB1LC Cc 1).
  - exact boot_1RB0LC_1LC1RA_0RA1LD_0RB1LC.
  - intros p _. apply lap_1RB0LC_1LC1RA_0RA1LD_0RB1LC.
  - intros t Ht p _. apply fire_1RB0LC_1LC1RA_0RA1LD_0RB1LC. exact Ht.
Qed.

Theorem nqhtr_1RB0LC_1LC1RA_0RA1LD_0RB1LC : NeverQuasiHaltsTr tm_1RB0LC_1LC1RA_0RA1LD_0RB1LC.
Proof. apply (neverqhtr_mirror tm_1RB0LC_1LC1RA_0RA1LD_0RB1LC). rewrite mirror_ok_1RB0LC_1LC1RA_0RA1LD_0RB1LC. exact nqhtrm_1RB0LC_1LC1RA_0RA1LD_0RB1LC. Qed.

Theorem nonhalt_1RB0LC_1LC1RA_0RA1LD_0RB1LC : NonHalt tm_1RB0LC_1LC1RA_0RA1LD_0RB1LC.
Proof. apply never_qh_tr_nonhalt, nqhtr_1RB0LC_1LC1RA_0RA1LD_0RB1LC. Qed.
