(** * LAPT_1RB1LC_0LC1RA_1RA0LD_1LB0RA: TRANSITION-LEVEL board for machine 1RB1LC_0LC1RA_1RA0LD_1LB0RA, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Jp digit alphabet (JpCounter.v), anchored at

      Cc p = (StB, (Jp p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  6*j+4 steps
      overflow  (cview p = (S j, None)):   boot 6*j+8, then the inner counter's own laps to the
                                           all-ones fill, then exit 6*j+10

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 192 interior anchors (interior); 6 overflow phases, j = 2..7 (492 inner laps, 2 counts each) (nested overflow).
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter JpCounter LapCertGlue LapCertGlueLift IXPGadgets NestedLap NestedLapLift NestedLap2.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
From BBB4 Require Import BBBT4_Statement.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
Import ListNotations.

Definition mk_1RB1LC_0LC1RA_1RA0LD_1LB0RA (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1LC_0LC1RA_1RA0LD_1LB0RA.

(** 1RB1LC_0LC1RA_1RA0LD_1LB0RA *)
Definition tm_1RB1LC_0LC1RA_1RA0LD_1LB0RA : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StC
  | StB, S0 => mk S0 DL StC | StB, S1 => mk S1 DR StA
  | StC, S0 => mk S1 DR StA | StC, S1 => mk S0 DL StD
  | StD, S0 => mk S1 DL StB | StD, S1 => mk S0 DR StA end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_1RB1LC_0LC1RA_1RA0LD_1LB0RA : list Instr := [].
Definition tmw_1RB1LC_0LC1RA_1RA0LD_1LB0RA : TM := tm_wrap_trs tm_1RB1LC_0LC1RA_1RA0LD_1LB0RA pins_1RB1LC_0LC1RA_1RA0LD_1LB0RA.
Local Notation tm := tmw_1RB1LC_0LC1RA_1RA0LD_1LB0RA.

Definition Cc_1RB1LC_0LC1RA_1RA0LD_1LB0RA (p : positive) : cconf := (StB, (Jp p ++ [S0], S0, [])).
Local Notation Cc := Cc_1RB1LC_0LC1RA_1RA0LD_1LB0RA.

(** ** The certificate *)

Definition A0_1RB1LC_0LC1RA_1RA0LD_1LB0RA : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition A1_1RB1LC_0LC1RA_1RA0LD_1LB0RA : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chi_1RB1LC_0LC1RA_1RA0LD_1LB0RA : list lstep := [SRotL 1; SWin 1; SCycL 4 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_int_1RB1LC_0LC1RA_1RA0LD_1LB0RA : srun tm false true chi_1RB1LC_0LC1RA_1RA0LD_1LB0RA A0_1RB1LC_0LC1RA_1RA0LD_1LB0RA = Some (A1_1RB1LC_0LC1RA_1RA0LD_1LB0RA, 6, 4).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB1LC_0LC1RA_1RA0LD_1LB0RA : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_1RB1LC_0LC1RA_1RA0LD_1LB0RA : sconf := mkC StB (mkS [] [S1;S1] 1 1 [S1;S0]) S0 (mkS [] [] 0 0 []).
(** ** The FIRST INNER anchor family -- Jp at StB *)
Definition Cin_1RB1LC_0LC1RA_1RA0LD_1LB0RA (v : positive) : cconf := (StB, (Jp v ++ [S1;S1;S1], S0, [])).
Local Notation Cin := Cin_1RB1LC_0LC1RA_1RA0LD_1LB0RA.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow2_1RB1LC_0LC1RA_1RA0LD_1LB0RA : forall n, Jp (pow2 n) = rep [S1;S1] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap -- ordinary and affine.  Iterating it to the fill is
    where a [Theta(2^j)] lives, and [inner_to_fill_lift] keeps it inside an
    existential. *)
Definition AI0_1RB1LC_0LC1RA_1RA0LD_1LB0RA : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition AI1_1RB1LC_0LC1RA_1RA0LD_1LB0RA : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chn_1RB1LC_0LC1RA_1RA0LD_1LB0RA : list lstep := [SRotL 1; SWin 1; SCycL 4 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_inner_1RB1LC_0LC1RA_1RA0LD_1LB0RA : srun tm false true chn_1RB1LC_0LC1RA_1RA0LD_1LB0RA AI0_1RB1LC_0LC1RA_1RA0LD_1LB0RA = Some (AI1_1RB1LC_0LC1RA_1RA0LD_1LB0RA, 6, 4).
Proof. vm_compute. reflexivity. Qed.

(** ** The SECOND INNER anchor family -- Jp at StB *)
Definition Cin2_1RB1LC_0LC1RA_1RA0LD_1LB0RA (v : positive) : cconf := (StB, (Jp v ++ [S0;S1;S1], S0, [])).
Local Notation Cin2 := Cin2_1RB1LC_0LC1RA_1RA0LD_1LB0RA.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow22_1RB1LC_0LC1RA_1RA0LD_1LB0RA : forall n, Jp (pow2 n) = rep [S1;S1] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap -- ordinary and affine.  Iterating it to the fill is
    where a [Theta(2^j)] lives, and [inner_to_fill_lift] keeps it inside an
    existential. *)
Definition AI20_1RB1LC_0LC1RA_1RA0LD_1LB0RA : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition AI21_1RB1LC_0LC1RA_1RA0LD_1LB0RA : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chn2_1RB1LC_0LC1RA_1RA0LD_1LB0RA : list lstep := [SRotL 1; SWin 1; SCycL 4 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_inner2_1RB1LC_0LC1RA_1RA0LD_1LB0RA : srun tm false true chn2_1RB1LC_0LC1RA_1RA0LD_1LB0RA AI20_1RB1LC_0LC1RA_1RA0LD_1LB0RA = Some (AI21_1RB1LC_0LC1RA_1RA0LD_1LB0RA, 6, 4).
Proof. vm_compute. reflexivity. Qed.

(** *** boot: the outer overflow anchor -> the first inner anchor at [pow2 j] *)
Definition BB1_1RB1LC_0LC1RA_1RA0LD_1LB0RA : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S1;S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chb_1RB1LC_0LC1RA_1RA0LD_1LB0RA : list lstep := [SRotL 1; SWin 1; SCycL 4 0; SWin 1; SWinL 5; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_boot_1RB1LC_0LC1RA_1RA0LD_1LB0RA : srun tm true true chb_1RB1LC_0LC1RA_1RA0LD_1LB0RA B0_1RB1LC_0LC1RA_1RA0LD_1LB0RA = Some (BB1_1RB1LC_0LC1RA_1RA0LD_1LB0RA, 6, 8).
Proof. vm_compute. reflexivity. Qed.

(** *** shift: count 1's all-ones fill -> count 2's anchor.
    WAVE18 section 4c -- "count 8->15, shift, count 8->15 again". *)
Definition BM0_1RB1LC_0LC1RA_1RA0LD_1LB0RA : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S1;S1;S1]) S0 (mkS [] [] 0 0 []).
Definition BM1_1RB1LC_0LC1RA_1RA0LD_1LB0RA : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S0;S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chm_1RB1LC_0LC1RA_1RA0LD_1LB0RA : list lstep := [SRotL 1; SWin 1; SCycL 4 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_shift_1RB1LC_0LC1RA_1RA0LD_1LB0RA : srun tm true true chm_1RB1LC_0LC1RA_1RA0LD_1LB0RA BM0_1RB1LC_0LC1RA_1RA0LD_1LB0RA = Some (BM1_1RB1LC_0LC1RA_1RA0LD_1LB0RA, 6, 4).
Proof. vm_compute. reflexivity. Qed.

(** *** exit: the last inner all-ones fill -> the outer successor *)
Definition BE0_1RB1LC_0LC1RA_1RA0LD_1LB0RA : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S0;S1;S1]) S0 (mkS [] [] 0 0 []).
Definition che_1RB1LC_0LC1RA_1RA0LD_1LB0RA : list lstep := [SRotL 1; SWin 1; SCycL 4 0; SWin 8; SCycR 2; SWin 1; SRotL 1; SFoldL 1].

Lemma run_exit_1RB1LC_0LC1RA_1RA0LD_1LB0RA : srun tm true true che_1RB1LC_0LC1RA_1RA0LD_1LB0RA BE0_1RB1LC_0LC1RA_1RA0LD_1LB0RA = Some (B1_1RB1LC_0LC1RA_1RA0LD_1LB0RA, 6, 10).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_1RB1LC_0LC1RA_1RA0LD_1LB0RA : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Jp q0 ++ [S0]) [] j A0_1RB1LC_0LC1RA_1RA0LD_1LB0RA.
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (H1 & _).
  unfold Cc_1RB1LC_0LC1RA_1RA0LD_1LB0RA, cden, A0_1RB1LC_0LC1RA_1RA0LD_1LB0RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gei_1RB1LC_0LC1RA_1RA0LD_1LB0RA : forall p j q0, cview p = (j, Some q0) ->
  cden (Jp q0 ++ [S0]) [] j A1_1RB1LC_0LC1RA_1RA0LD_1LB0RA = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (_ & H2).
  unfold Cc_1RB1LC_0LC1RA_1RA0LD_1LB0RA, cden, A1_1RB1LC_0LC1RA_1RA0LD_1LB0RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB1LC_0LC1RA_1RA0LD_1LB0RA : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (6 * j + 4). split; [lia|].
  rewrite (gsi_1RB1LC_0LC1RA_1RA0LD_1LB0RA p j q0 E).
  rewrite (srun_sound tm false true chi_1RB1LC_0LC1RA_1RA0LD_1LB0RA A0_1RB1LC_0LC1RA_1RA0LD_1LB0RA A1_1RB1LC_0LC1RA_1RA0LD_1LB0RA 6 4
             run_int_1RB1LC_0LC1RA_1RA0LD_1LB0RA (Jp q0 ++ [S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_1RB1LC_0LC1RA_1RA0LD_1LB0RA p j q0 E).
Qed.

Lemma gso_1RB1LC_0LC1RA_1RA0LD_1LB0RA : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_1RB1LC_0LC1RA_1RA0LD_1LB0RA.
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (H1 & _).
  unfold Cc_1RB1LC_0LC1RA_1RA0LD_1LB0RA, cden, B0_1RB1LC_0LC1RA_1RA0LD_1LB0RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB1LC_0LC1RA_1RA0LD_1LB0RA : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB1LC_0LC1RA_1RA0LD_1LB0RA : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB1LC_0LC1RA_1RA0LD_1LB0RA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB1LC_0LC1RA_1RA0LD_1LB0RA
             = (StB, (rep [S1;S1] (S j) ++ [S1;S0], S0, []))).
  { unfold cden, B1_1RB1LC_0LC1RA_1RA0LD_1LB0RA, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StB, (rep [S1;S1] (S j) ++ [S1;S0], S0, []))).
  { unfold Cc_1RB1LC_0LC1RA_1RA0LD_1LB0RA. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. reflexivity.
Qed.

Lemma gsn_1RB1LC_0LC1RA_1RA0LD_1LB0RA : forall v i q0, cview v = (i, Some q0) ->
  Cin v = cden (Jp q0 ++ [S1;S1;S1]) [] i AI0_1RB1LC_0LC1RA_1RA0LD_1LB0RA.
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (H1 & _).
  unfold Cin_1RB1LC_0LC1RA_1RA0LD_1LB0RA, cden, AI0_1RB1LC_0LC1RA_1RA0LD_1LB0RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen_1RB1LC_0LC1RA_1RA0LD_1LB0RA : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Jp q0 ++ [S1;S1;S1]) [] i AI1_1RB1LC_0LC1RA_1RA0LD_1LB0RA) = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (_ & H2).
  unfold Cin_1RB1LC_0LC1RA_1RA0LD_1LB0RA, cden, AI1_1RB1LC_0LC1RA_1RA0LD_1LB0RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin_1RB1LC_0LC1RA_1RA0LD_1LB0RA : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (6 * i + 4), (cden (Jp q0 ++ [S1;S1;S1]) [] i AI1_1RB1LC_0LC1RA_1RA0LD_1LB0RA).
  split; [lia|]. split; [| exact (gen_1RB1LC_0LC1RA_1RA0LD_1LB0RA v i q0 E)].
  rewrite (gsn_1RB1LC_0LC1RA_1RA0LD_1LB0RA v i q0 E).
  exact (srun_sound tm false true chn_1RB1LC_0LC1RA_1RA0LD_1LB0RA AI0_1RB1LC_0LC1RA_1RA0LD_1LB0RA AI1_1RB1LC_0LC1RA_1RA0LD_1LB0RA 6 4
           run_inner_1RB1LC_0LC1RA_1RA0LD_1LB0RA (Jp q0 ++ [S1;S1;S1]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The chain into this family lands on its anchor up to 0/0
    trailing blanks. *)
Lemma gbo_1RB1LC_0LC1RA_1RA0LD_1LB0RA : forall j, lift (cden [] [] j BB1_1RB1LC_0LC1RA_1RA0LD_1LB0RA) = lift (Cin (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_1RB1LC_0LC1RA_1RA0LD_1LB0RA = (StB, (rep [S1;S1] j ++ [S1;S1;S1;S1], S0, []))).
  { unfold cden, BB1_1RB1LC_0LC1RA_1RA0LD_1LB0RA, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin (pow2 j) = (StB, (rep [S1;S1] j ++ [S1;S1;S1;S1], S0, []))).
  { unfold Cin_1RB1LC_0LC1RA_1RA0LD_1LB0RA. rewrite epow2_1RB1LC_0LC1RA_1RA0LD_1LB0RA.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_1RB1LC_0LC1RA_1RA0LD_1LB0RA. rewrite ?lift_app_blank. reflexivity.
Qed.

(** This family's all-ones fill IS the next chain's start.  [cview (fill
    (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    family's own overflow decomposition names the word. *)
Lemma gxi_1RB1LC_0LC1RA_1RA0LD_1LB0RA : forall j, Cin (fill (pow2 j)) = cden [] [] j BM0_1RB1LC_0LC1RA_1RA0LD_1LB0RA.
Proof.
  intro j.
  destruct (JpCounter.cview_none_J (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin_1RB1LC_0LC1RA_1RA0LD_1LB0RA, cden, BM0_1RB1LC_0LC1RA_1RA0LD_1LB0RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

Lemma gsn2_1RB1LC_0LC1RA_1RA0LD_1LB0RA : forall v i q0, cview v = (i, Some q0) ->
  Cin2 v = cden (Jp q0 ++ [S0;S1;S1]) [] i AI20_1RB1LC_0LC1RA_1RA0LD_1LB0RA.
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (H1 & _).
  unfold Cin2_1RB1LC_0LC1RA_1RA0LD_1LB0RA, cden, AI20_1RB1LC_0LC1RA_1RA0LD_1LB0RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen2_1RB1LC_0LC1RA_1RA0LD_1LB0RA : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Jp q0 ++ [S0;S1;S1]) [] i AI21_1RB1LC_0LC1RA_1RA0LD_1LB0RA) = lift (Cin2 (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (_ & H2).
  unfold Cin2_1RB1LC_0LC1RA_1RA0LD_1LB0RA, cden, AI21_1RB1LC_0LC1RA_1RA0LD_1LB0RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin2_1RB1LC_0LC1RA_1RA0LD_1LB0RA : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin2 v) = Some c'
               /\ lift c' = lift (Cin2 (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (6 * i + 4), (cden (Jp q0 ++ [S0;S1;S1]) [] i AI21_1RB1LC_0LC1RA_1RA0LD_1LB0RA).
  split; [lia|]. split; [| exact (gen2_1RB1LC_0LC1RA_1RA0LD_1LB0RA v i q0 E)].
  rewrite (gsn2_1RB1LC_0LC1RA_1RA0LD_1LB0RA v i q0 E).
  exact (srun_sound tm false true chn2_1RB1LC_0LC1RA_1RA0LD_1LB0RA AI20_1RB1LC_0LC1RA_1RA0LD_1LB0RA AI21_1RB1LC_0LC1RA_1RA0LD_1LB0RA 6 4
           run_inner2_1RB1LC_0LC1RA_1RA0LD_1LB0RA (Jp q0 ++ [S0;S1;S1]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The chain into this family lands on its anchor up to 0/0
    trailing blanks. *)
Lemma gbo2_1RB1LC_0LC1RA_1RA0LD_1LB0RA : forall j, lift (cden [] [] j BM1_1RB1LC_0LC1RA_1RA0LD_1LB0RA) = lift (Cin2 (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BM1_1RB1LC_0LC1RA_1RA0LD_1LB0RA = (StB, (rep [S1;S1] j ++ [S1;S0;S1;S1], S0, []))).
  { unfold cden, BM1_1RB1LC_0LC1RA_1RA0LD_1LB0RA, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin2 (pow2 j) = (StB, (rep [S1;S1] j ++ [S1;S0;S1;S1], S0, []))).
  { unfold Cin2_1RB1LC_0LC1RA_1RA0LD_1LB0RA. rewrite epow22_1RB1LC_0LC1RA_1RA0LD_1LB0RA.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_1RB1LC_0LC1RA_1RA0LD_1LB0RA. rewrite ?lift_app_blank. reflexivity.
Qed.

(** This family's all-ones fill IS the next chain's start.  [cview (fill
    (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    family's own overflow decomposition names the word. *)
Lemma gxi2_1RB1LC_0LC1RA_1RA0LD_1LB0RA : forall j, Cin2 (fill (pow2 j)) = cden [] [] j BE0_1RB1LC_0LC1RA_1RA0LD_1LB0RA.
Proof.
  intro j.
  destruct (JpCounter.cview_none_J (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin2_1RB1LC_0LC1RA_1RA0LD_1LB0RA, cden, BE0_1RB1LC_0LC1RA_1RA0LD_1LB0RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

(** The interior lap, restated up to [lift] -- what [vis_via_ovf_lift] and
    [vis_via_fill] consume. *)
Lemma lapil_1RB1LC_0LC1RA_1RA0LD_1LB0RA : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof. intros p j q0 E. destruct (lapi_1RB1LC_0LC1RA_1RA0LD_1LB0RA p j q0 E) as (n & Hn & Hr).
  exists n, (Cc (Pos.succ p)).
  split; [exact Hn | split; [exact Hr | reflexivity]]. Qed.

(** The outer OVERFLOW branch, composed.  The exponential cost is the
    [exists n] inside [inner_to_fill_lift]; no formula for it is ever
    written. *)
Lemma lapo_1RB1LC_0LC1RA_1RA0LD_1LB0RA : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E.
  apply (nested_overflow_lift tm Cc Cin2 lapin2_1RB1LC_0LC1RA_1RA0LD_1LB0RA p (pow2 j)).
  - assert (HB1 : exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
                  /\ lift c = lift (Cin (pow2 j))).
    { exists (6 * j + 8), (cden [] [] j BB1_1RB1LC_0LC1RA_1RA0LD_1LB0RA).
      split; [lia|]. split; [| exact (gbo_1RB1LC_0LC1RA_1RA0LD_1LB0RA j)].
      rewrite (gso_1RB1LC_0LC1RA_1RA0LD_1LB0RA p j E).
      exact (srun_sound tm true true chb_1RB1LC_0LC1RA_1RA0LD_1LB0RA B0_1RB1LC_0LC1RA_1RA0LD_1LB0RA BB1_1RB1LC_0LC1RA_1RA0LD_1LB0RA 6 8
               run_boot_1RB1LC_0LC1RA_1RA0LD_1LB0RA [] [] j ltac:(reflexivity) ltac:(reflexivity)). }
    assert (HB2 : exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
                  /\ lift c = lift (Cin2 (pow2 j))).
    { apply (boot_via_fill tm Cc Cin Cin2 lapin_1RB1LC_0LC1RA_1RA0LD_1LB0RA p (pow2 j) (pow2 j));
        [exact HB1|].
      exists (6 * j + 4), (cden [] [] j BM1_1RB1LC_0LC1RA_1RA0LD_1LB0RA).
      split; [| exact (gbo2_1RB1LC_0LC1RA_1RA0LD_1LB0RA j)].
      rewrite (gxi_1RB1LC_0LC1RA_1RA0LD_1LB0RA j).
      exact (srun_sound tm true true chm_1RB1LC_0LC1RA_1RA0LD_1LB0RA BM0_1RB1LC_0LC1RA_1RA0LD_1LB0RA BM1_1RB1LC_0LC1RA_1RA0LD_1LB0RA 6 4
               run_shift_1RB1LC_0LC1RA_1RA0LD_1LB0RA [] [] j ltac:(reflexivity) ltac:(reflexivity)). }
    exact HB2.
  - exists (6 * j + 10), (cden [] [] j B1_1RB1LC_0LC1RA_1RA0LD_1LB0RA).
    split; [| exact (geo_1RB1LC_0LC1RA_1RA0LD_1LB0RA p j E)].
    rewrite (gxi2_1RB1LC_0LC1RA_1RA0LD_1LB0RA j).
    exact (srun_sound tm true true che_1RB1LC_0LC1RA_1RA0LD_1LB0RA BE0_1RB1LC_0LC1RA_1RA0LD_1LB0RA B1_1RB1LC_0LC1RA_1RA0LD_1LB0RA 6 10
             run_exit_1RB1LC_0LC1RA_1RA0LD_1LB0RA [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.



(** ** The lap *)

Lemma lap_1RB1LC_0LC1RA_1RA0LD_1LB0RA : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB1LC_0LC1RA_1RA0LD_1LB0RA p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->). exact (lapo_1RB1LC_0LC1RA_1RA0LD_1LB0RA p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_1RB1LC_0LC1RA_1RA0LD_1LB0RA : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 1.
  assert (H : match csteps tm 1 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 1 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_1RB1LC_0LC1RA_1RA0LD_1LB0RA : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_1RB1LC_0LC1RA_1RA0LD_1LB0RA = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_1RB1LC_0LC1RA_1RA0LD_1LB0RA p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB1LC_0LC1RA_1RA0LD_1LB0RA p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_1RB1LC_0LC1RA_1RA0LD_1LB0RA : forall t, ~ In t pins_1RB1LC_0LC1RA_1RA0LD_1LB0RA ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_1RB1LC_0LC1RA_1RA0LD_1LB0RA.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_via_ovf tm Cc Hi (StA, S0)), fireo_1RB1LC_0LC1RA_1RA0LD_1LB0RA
      with (l := [SRotL 1; SWin 1; SCycL 4 0; SWin 1; SWinL 3]).
    vm_compute; reflexivity.
  - (* A1 *)
    apply (fire_via_ovf tm Cc Hi (StA, S1)), fireo_1RB1LC_0LC1RA_1RA0LD_1LB0RA
      with (l := [SRotL 1; SWin 1; SCycL 4 0; SWin 1; SWinL 5; SCycR 2; SWin 1; SUnrotL 1; SRotL 1; SWin 1; SRotL 1; SWin 5; SRotL 1; SWin 2]).
    vm_compute; reflexivity.
  - (* B0 *)
    apply (fire_via_ovf tm Cc Hi (StB, S0)), fireo_1RB1LC_0LC1RA_1RA0LD_1LB0RA
      with (l := []).
    vm_compute; reflexivity.
  - (* B1 *)
    apply (fire_via_ovf tm Cc Hi (StB, S1)), fireo_1RB1LC_0LC1RA_1RA0LD_1LB0RA
      with (l := [SRotL 1; SWin 1; SCycL 4 0; SWin 1; SWinL 4]).
    vm_compute; reflexivity.
  - (* C0 *)
    apply (fire_via_ovf tm Cc Hi (StC, S0)), fireo_1RB1LC_0LC1RA_1RA0LD_1LB0RA
      with (l := [SRotL 1; SWin 1; SCycL 4 0; SWin 1; SWinL 2]).
    vm_compute; reflexivity.
  - (* C1 *)
    apply (fire_via_ovf tm Cc Hi (StC, S1)), fireo_1RB1LC_0LC1RA_1RA0LD_1LB0RA
      with (l := [SRotL 1; SWin 1]).
    vm_compute; reflexivity.
  - (* D0 *)
    apply (fire_via_ovf tm Cc Hi (StD, S0)), fireo_1RB1LC_0LC1RA_1RA0LD_1LB0RA
      with (l := [SRotL 1; SWin 1; SCycL 4 0; SWin 1]).
    vm_compute; reflexivity.
  - (* D1 *)
    apply (fire_via_ovf tm Cc Hi (StD, S1)), fireo_1RB1LC_0LC1RA_1RA0LD_1LB0RA
      with (l := [SRotL 1; SWin 1; SCycL 4 0; SWin 1; SWinL 5; SCycR 2; SWin 1; SUnrotL 1; SRotL 1; SWin 1; SRotL 1; SWin 1]).
    vm_compute; reflexivity.
Qed.

Theorem nqhtr_1RB1LC_0LC1RA_1RA0LD_1LB0RA : NeverQuasiHaltsTr tm_1RB1LC_0LC1RA_1RA0LD_1LB0RA.
Proof.
  apply (glue_neverqhtr tm_1RB1LC_0LC1RA_1RA0LD_1LB0RA pins_1RB1LC_0LC1RA_1RA0LD_1LB0RA Cc 1).
  - exact boot_1RB1LC_0LC1RA_1RA0LD_1LB0RA.
  - intros p _. apply lap_1RB1LC_0LC1RA_1RA0LD_1LB0RA.
  - intros t Ht p _. apply fire_1RB1LC_0LC1RA_1RA0LD_1LB0RA. exact Ht.
Qed.

Theorem nonhalt_1RB1LC_0LC1RA_1RA0LD_1LB0RA : NonHalt tm_1RB1LC_0LC1RA_1RA0LD_1LB0RA.
Proof. apply never_qh_tr_nonhalt, nqhtr_1RB1LC_0LC1RA_1RA0LD_1LB0RA. Qed.
