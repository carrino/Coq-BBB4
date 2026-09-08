(** * LAPT_1RB0LD_0LC0RA_1RA1LC_1RA1LA: TRANSITION-LEVEL board for machine 1RB0LD_0LC0RA_1RA1LC_1RA1LA, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Ip digit alphabet (ILCounter.v), anchored at

      Cc p = (StC, (Ip p ++ [S0], S0, [S1]))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  4*j+10 steps
      overflow  (cview p = (S j, None)):   boot 4*j+10, then the inner counter's own laps to the
                                           all-ones fill, then exit 4*j+12

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 192 interior anchors (interior); 6 overflow phases, j = 2..7 (246 inner laps) (nested overflow).
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter ILCounter LapCertGlue LapCertGlueLift IXPGadgets NestedLap NestedLapLift.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
From BBB4 Require Import BBBT4_Statement.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
Import ListNotations.

Definition mk_1RB0LD_0LC0RA_1RA1LC_1RA1LA (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB0LD_0LC0RA_1RA1LC_1RA1LA.

(** 1RB0LD_0LC0RA_1RA1LC_1RA1LA *)
Definition tm_1RB0LD_0LC0RA_1RA1LC_1RA1LA : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StD
  | StB, S0 => mk S0 DL StC | StB, S1 => mk S0 DR StA
  | StC, S0 => mk S1 DR StA | StC, S1 => mk S1 DL StC
  | StD, S0 => mk S1 DR StA | StD, S1 => mk S1 DL StA end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_1RB0LD_0LC0RA_1RA1LC_1RA1LA : list Instr := [].
Definition tmw_1RB0LD_0LC0RA_1RA1LC_1RA1LA : TM := tm_wrap_trs tm_1RB0LD_0LC0RA_1RA1LC_1RA1LA pins_1RB0LD_0LC0RA_1RA1LC_1RA1LA.
Local Notation tm := tmw_1RB0LD_0LC0RA_1RA1LC_1RA1LA.

Definition Cc_1RB0LD_0LC0RA_1RA1LC_1RA1LA (p : positive) : cconf := (StC, (Ip p ++ [S0], S0, [S1])).
Local Notation Cc := Cc_1RB0LD_0LC0RA_1RA1LC_1RA1LA.

(** ** The certificate *)

Definition A0_1RB0LD_0LC0RA_1RA1LC_1RA1LA : sconf := mkC StC (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S1] [] 0 0 []).
Definition A1_1RB0LD_0LC0RA_1RA1LC_1RA1LA : sconf := mkC StC (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1;S0] [] 0 0 []).
Definition chi_1RB0LD_0LC0RA_1RA1LC_1RA1LA : list lstep := [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 1; SWinR 3].

Lemma run_int_1RB0LD_0LC0RA_1RA1LC_1RA1LA : srun tm false true chi_1RB0LD_0LC0RA_1RA1LC_1RA1LA A0_1RB0LD_0LC0RA_1RA1LC_1RA1LA = Some (A1_1RB0LD_0LC0RA_1RA1LC_1RA1LA, 4, 10).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB0LD_0LC0RA_1RA1LC_1RA1LA : sconf := mkC StC (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S1] [] 0 0 []).
Definition B1_1RB0LD_0LC0RA_1RA1LC_1RA1LA : sconf := mkC StC (mkS [] [S1;S0] 1 1 [S1]) S0 (mkS [S1;S0] [] 0 0 []).
(** ** The INNER anchor family -- Ip at StC *)
Definition Cin_1RB0LD_0LC0RA_1RA1LC_1RA1LA (v : positive) : cconf := (StC, (Ip v ++ [S1], S0, [S1])).
Local Notation Cin := Cin_1RB0LD_0LC0RA_1RA1LC_1RA1LA.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow2_1RB0LD_0LC0RA_1RA1LC_1RA1LA : forall n, Ip (pow2 n) = rep [S1;S0] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap -- ordinary and affine.  Iterating it to the fill is
    where a [Theta(2^j)] lives, and [inner_to_fill_lift] keeps it inside an
    existential. *)
Definition AI0_1RB0LD_0LC0RA_1RA1LC_1RA1LA : sconf := mkC StC (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S1] [] 0 0 []).
Definition AI1_1RB0LD_0LC0RA_1RA1LC_1RA1LA : sconf := mkC StC (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1;S0] [] 0 0 []).
Definition chn_1RB0LD_0LC0RA_1RA1LC_1RA1LA : list lstep := [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 1; SWinR 3].

Lemma run_inner_1RB0LD_0LC0RA_1RA1LC_1RA1LA : srun tm false true chn_1RB0LD_0LC0RA_1RA1LC_1RA1LA AI0_1RB0LD_0LC0RA_1RA1LC_1RA1LA = Some (AI1_1RB0LD_0LC0RA_1RA1LC_1RA1LA, 4, 10).
Proof. vm_compute. reflexivity. Qed.

(** *** boot: the outer overflow anchor -> the first inner anchor at [pow2 j] *)
Definition BB1_1RB0LD_0LC0RA_1RA1LC_1RA1LA : sconf := mkC StC (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1;S0] [] 0 0 []).
Definition chb_1RB0LD_0LC0RA_1RA1LC_1RA1LA : list lstep := [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 1; SWinR 3].

Lemma run_boot_1RB0LD_0LC0RA_1RA1LC_1RA1LA : srun tm true true chb_1RB0LD_0LC0RA_1RA1LC_1RA1LA B0_1RB0LD_0LC0RA_1RA1LC_1RA1LA = Some (BB1_1RB0LD_0LC0RA_1RA1LC_1RA1LA, 4, 10).
Proof. vm_compute. reflexivity. Qed.

(** *** exit: the last inner all-ones fill -> the outer successor *)
Definition BE0_1RB0LD_0LC0RA_1RA1LC_1RA1LA : sconf := mkC StC (mkS [] [S1;S1] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition che_1RB0LD_0LC0RA_1RA1LC_1RA1LA : list lstep := [SWin 2; SCycL 2 0; SWin 2; SWinL 4; SCycR 2; SWin 1; SWinR 3; SRotL 2; SFoldL 1].

Lemma run_exit_1RB0LD_0LC0RA_1RA1LC_1RA1LA : srun tm true true che_1RB0LD_0LC0RA_1RA1LC_1RA1LA BE0_1RB0LD_0LC0RA_1RA1LC_1RA1LA = Some (B1_1RB0LD_0LC0RA_1RA1LC_1RA1LA, 4, 12).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_1RB0LD_0LC0RA_1RA1LC_1RA1LA : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Ip q0 ++ [S0]) [] j A0_1RB0LD_0LC0RA_1RA1LC_1RA1LA.
Proof.
  intros p j q0 E. destruct (ILCounter.cview_some_I p j q0 E) as (H1 & _).
  unfold Cc_1RB0LD_0LC0RA_1RA1LC_1RA1LA, cden, A0_1RB0LD_0LC0RA_1RA1LC_1RA1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

(** The lap ends on [S1;S0] where the anchor has [S1] -- one trailing blank,
    which [lift] cannot see. *)
Lemma gei_1RB0LD_0LC0RA_1RA1LC_1RA1LA : forall p j q0, cview p = (j, Some q0) ->
  lift (cden (Ip q0 ++ [S0]) [] j A1_1RB0LD_0LC0RA_1RA1LC_1RA1LA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (ILCounter.cview_some_I p j q0 E) as (_ & H2).
  unfold Cc_1RB0LD_0LC0RA_1RA1LC_1RA1LA, cden, A1_1RB0LD_0LC0RA_1RA1LC_1RA1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S1;S0]) with (([S1]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB0LD_0LC0RA_1RA1LC_1RA1LA : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  exists (4 * j + 10), (cden (Ip q0 ++ [S0]) [] j A1_1RB0LD_0LC0RA_1RA1LC_1RA1LA).
  split; [lia|]. split; [| exact (gei_1RB0LD_0LC0RA_1RA1LC_1RA1LA p j q0 E)].
  rewrite (gsi_1RB0LD_0LC0RA_1RA1LC_1RA1LA p j q0 E).
  exact (srun_sound tm false true chi_1RB0LD_0LC0RA_1RA1LC_1RA1LA A0_1RB0LD_0LC0RA_1RA1LC_1RA1LA A1_1RB0LD_0LC0RA_1RA1LC_1RA1LA 4 10
           run_int_1RB0LD_0LC0RA_1RA1LC_1RA1LA (Ip q0 ++ [S0]) [] j
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma gso_1RB0LD_0LC0RA_1RA1LC_1RA1LA : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_1RB0LD_0LC0RA_1RA1LC_1RA1LA.
Proof.
  intros p j E. destruct (ILCounter.cview_none_I p j E) as (H1 & _).
  unfold Cc_1RB0LD_0LC0RA_1RA1LC_1RA1LA, cden, B0_1RB0LD_0LC0RA_1RA1LC_1RA1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB0LD_0LC0RA_1RA1LC_1RA1LA : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB0LD_0LC0RA_1RA1LC_1RA1LA : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB0LD_0LC0RA_1RA1LC_1RA1LA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (ILCounter.cview_none_I p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB0LD_0LC0RA_1RA1LC_1RA1LA
             = (StC, (rep [S1;S0] (S j) ++ [S1], S0, ([S1]) ++ [S0]))).
  { unfold cden, B1_1RB0LD_0LC0RA_1RA1LC_1RA1LA, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StC, ((rep [S1;S0] (S j) ++ [S1]) ++ [S0], S0, [S1]))).
  { unfold Cc_1RB0LD_0LC0RA_1RA1LC_1RA1LA. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lift_app_blank. rewrite !lbl_1RB0LD_0LC0RA_1RA1LC_1RA1LA. reflexivity.
Qed.

Lemma gsn_1RB0LD_0LC0RA_1RA1LC_1RA1LA : forall v i q0, cview v = (i, Some q0) ->
  Cin v = cden (Ip q0 ++ [S1]) [] i AI0_1RB0LD_0LC0RA_1RA1LC_1RA1LA.
Proof.
  intros v i q0 E. destruct (ILCounter.cview_some_I v i q0 E) as (H1 & _).
  unfold Cin_1RB0LD_0LC0RA_1RA1LC_1RA1LA, cden, AI0_1RB0LD_0LC0RA_1RA1LC_1RA1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen_1RB0LD_0LC0RA_1RA1LC_1RA1LA : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Ip q0 ++ [S1]) [] i AI1_1RB0LD_0LC0RA_1RA1LC_1RA1LA) = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (ILCounter.cview_some_I v i q0 E) as (_ & H2).
  unfold Cin_1RB0LD_0LC0RA_1RA1LC_1RA1LA, cden, AI1_1RB0LD_0LC0RA_1RA1LC_1RA1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S1;S0]) with (([S1]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S0] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin_1RB0LD_0LC0RA_1RA1LC_1RA1LA : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 10), (cden (Ip q0 ++ [S1]) [] i AI1_1RB0LD_0LC0RA_1RA1LC_1RA1LA).
  split; [lia|]. split; [| exact (gen_1RB0LD_0LC0RA_1RA1LC_1RA1LA v i q0 E)].
  rewrite (gsn_1RB0LD_0LC0RA_1RA1LC_1RA1LA v i q0 E).
  exact (srun_sound tm false true chn_1RB0LD_0LC0RA_1RA1LC_1RA1LA AI0_1RB0LD_0LC0RA_1RA1LC_1RA1LA AI1_1RB0LD_0LC0RA_1RA1LC_1RA1LA 4 10
           run_inner_1RB0LD_0LC0RA_1RA1LC_1RA1LA (Ip q0 ++ [S1]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The chain into this family lands on its anchor up to 0/1
    trailing blanks. *)
Lemma gbo_1RB0LD_0LC0RA_1RA1LC_1RA1LA : forall j, lift (cden [] [] j BB1_1RB0LD_0LC0RA_1RA1LC_1RA1LA) = lift (Cin (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_1RB0LD_0LC0RA_1RA1LC_1RA1LA = (StC, (rep [S1;S0] j ++ [S1;S1], S0, ([S1]) ++ [S0]))).
  { unfold cden, BB1_1RB0LD_0LC0RA_1RA1LC_1RA1LA, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin (pow2 j) = (StC, (rep [S1;S0] j ++ [S1;S1], S0, [S1]))).
  { unfold Cin_1RB0LD_0LC0RA_1RA1LC_1RA1LA. rewrite epow2_1RB0LD_0LC0RA_1RA1LC_1RA1LA.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_1RB0LD_0LC0RA_1RA1LC_1RA1LA. rewrite ?lift_app_blank. reflexivity.
Qed.

(** This family's all-ones fill IS the next chain's start.  [cview (fill
    (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    family's own overflow decomposition names the word. *)
Lemma gxi_1RB0LD_0LC0RA_1RA1LC_1RA1LA : forall j, Cin (fill (pow2 j)) = cden [] [] j BE0_1RB0LD_0LC0RA_1RA1LC_1RA1LA.
Proof.
  intro j.
  destruct (ILCounter.cview_none_I (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin_1RB0LD_0LC0RA_1RA1LC_1RA1LA, cden, BE0_1RB0LD_0LC0RA_1RA1LC_1RA1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

(** The interior lap, restated up to [lift] -- what [vis_via_ovf_lift] and
    [vis_via_fill] consume. *)
Lemma lapil_1RB0LD_0LC0RA_1RA1LC_1RA1LA : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof. exact lapi_1RB0LD_0LC0RA_1RA1LC_1RA1LA. Qed.

(** The outer OVERFLOW branch, composed.  The exponential cost is the
    [exists n] inside [inner_to_fill_lift]; no formula for it is ever
    written. *)
Lemma lapo_1RB0LD_0LC0RA_1RA1LC_1RA1LA : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E.
  apply (nested_overflow_lift tm Cc Cin lapin_1RB0LD_0LC0RA_1RA1LC_1RA1LA p (pow2 j)).
  - exists (4 * j + 10), (cden [] [] j BB1_1RB0LD_0LC0RA_1RA1LC_1RA1LA).
    split; [lia|]. split; [| exact (gbo_1RB0LD_0LC0RA_1RA1LC_1RA1LA j)].
    rewrite (gso_1RB0LD_0LC0RA_1RA1LC_1RA1LA p j E).
    exact (srun_sound tm true true chb_1RB0LD_0LC0RA_1RA1LC_1RA1LA B0_1RB0LD_0LC0RA_1RA1LC_1RA1LA BB1_1RB0LD_0LC0RA_1RA1LC_1RA1LA 4 10
             run_boot_1RB0LD_0LC0RA_1RA1LC_1RA1LA [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  - exists (4 * j + 12), (cden [] [] j B1_1RB0LD_0LC0RA_1RA1LC_1RA1LA).
    split; [| exact (geo_1RB0LD_0LC0RA_1RA1LC_1RA1LA p j E)].
    rewrite (gxi_1RB0LD_0LC0RA_1RA1LC_1RA1LA j).
    exact (srun_sound tm true true che_1RB0LD_0LC0RA_1RA1LC_1RA1LA BE0_1RB0LD_0LC0RA_1RA1LC_1RA1LA B1_1RB0LD_0LC0RA_1RA1LC_1RA1LA 4 12
             run_exit_1RB0LD_0LC0RA_1RA1LC_1RA1LA [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.



(** ** The lap *)

Lemma lap_1RB0LD_0LC0RA_1RA1LC_1RA1LA : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB0LD_0LC0RA_1RA1LC_1RA1LA p j q0 E) as (n & c' & Hn & Hrun & Hlift).
    exists n, c'. split; [exact Hrun | split; [exact Hlift | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->). exact (lapo_1RB0LD_0LC0RA_1RA1LC_1RA1LA p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_1RB0LD_0LC0RA_1RA1LC_1RA1LA : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 11.
  assert (H : match csteps tm 11 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 11 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_1RB0LD_0LC0RA_1RA1LC_1RA1LA : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_1RB0LD_0LC0RA_1RA1LC_1RA1LA = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_1RB0LD_0LC0RA_1RA1LC_1RA1LA p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB0LD_0LC0RA_1RA1LC_1RA1LA p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_1RB0LD_0LC0RA_1RA1LC_1RA1LA : forall t, ~ In t pins_1RB0LD_0LC0RA_1RA1LC_1RA1LA ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n c', 0 < n /\ csteps tm n (Cc p0) = Some c'
                         /\ lift c' = lift (Cc (Pos.succ p0)))
    by exact lapi_1RB0LD_0LC0RA_1RA1LC_1RA1LA.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StA, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB0LD_0LC0RA_1RA1LC_1RA1LA [SWin 2; SCycL 2 0; SWin 3] (StA, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* A1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StA, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB0LD_0LC0RA_1RA1LC_1RA1LA [SWin 1] (StA, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* B0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StB, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB0LD_0LC0RA_1RA1LC_1RA1LA [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 1; SWinR 1] (StB, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* B1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StB, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB0LD_0LC0RA_1RA1LC_1RA1LA [SWin 2; SCycL 2 0; SWin 4] (StB, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* C0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StC, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB0LD_0LC0RA_1RA1LC_1RA1LA [] (StC, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* C1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StC, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB0LD_0LC0RA_1RA1LC_1RA1LA [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 1; SWinR 2] (StC, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* D0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StD, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB0LD_0LC0RA_1RA1LC_1RA1LA [SWin 2; SCycL 2 0; SWin 2] (StD, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* D1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StD, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB0LD_0LC0RA_1RA1LC_1RA1LA [SWin 2] (StD, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
Qed.

Theorem nqhtr_1RB0LD_0LC0RA_1RA1LC_1RA1LA : NeverQuasiHaltsTr tm_1RB0LD_0LC0RA_1RA1LC_1RA1LA.
Proof.
  apply (glue_neverqhtr tm_1RB0LD_0LC0RA_1RA1LC_1RA1LA pins_1RB0LD_0LC0RA_1RA1LC_1RA1LA Cc 1).
  - exact boot_1RB0LD_0LC0RA_1RA1LC_1RA1LA.
  - intros p _. apply lap_1RB0LD_0LC0RA_1RA1LC_1RA1LA.
  - intros t Ht p _. apply fire_1RB0LD_0LC0RA_1RA1LC_1RA1LA. exact Ht.
Qed.

Theorem nonhalt_1RB0LD_0LC0RA_1RA1LC_1RA1LA : NonHalt tm_1RB0LD_0LC0RA_1RA1LC_1RA1LA.
Proof. apply never_qh_tr_nonhalt, nqhtr_1RB0LD_0LC0RA_1RA1LC_1RA1LA. Qed.
