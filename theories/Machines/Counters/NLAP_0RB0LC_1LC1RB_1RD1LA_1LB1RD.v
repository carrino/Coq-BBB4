(** * NLAP_0RB0LC_1LC1RB_1RD1LA_1LB1RD: machine 0RB0LC_1LC1RB_1RD1LA_1LB1RD, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Ap_Alph_10_11_11 digit alphabet (Alph_10_11_11.v), anchored at

      Cc p = (StA, (Ap_Alph_10_11_11 p ++ [S1;S1;S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  4*j+4 steps
      overflow  (cview p = (S j, None)):   boot 4*j+23, then the inner counter's own laps to the
                                           all-ones fill, then exit 4*j+12

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
                                  MonoCounter JpCounter Alph_10_11_11 LapCertGlue LapCertGlueLift IXPGadgets NestedLap NestedLapLift ILCounter.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_0RB0LC_1LC1RB_1RD1LA_1LB1RD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB0LC_1LC1RB_1RD1LA_1LB1RD.

(** 0RB0LC_1LC1RB_1RD1LA_1LB1RD *)
(** 0RB0LC_1LC1RB_1RD1LA_1LB1RD -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB0LC_1LC1RB_1RD1LA_1LB1RD : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S0 DL StC
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S1 DL StB | StD, S1 => mk S1 DR StD end.

(** Its mirror 0LB0RC_1RC1LB_1LD1RA_1RB1LD: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB0LC_1LC1RB_1RD1LA_1LB1RD : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S0 DR StC
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S1 DL StD | StC, S1 => mk S1 DR StA
  | StD, S0 => mk S1 DR StB | StD, S1 => mk S1 DL StD end.
Local Notation tm := tmm_0RB0LC_1LC1RB_1RD1LA_1LB1RD.

Lemma mirror_ok_0RB0LC_1LC1RB_1RD1LA_1LB1RD : mirror_tm tm_0RB0LC_1LC1RB_1RD1LA_1LB1RD = tmm_0RB0LC_1LC1RB_1RD1LA_1LB1RD.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_0RB0LC_1LC1RB_1RD1LA_1LB1RD (p : positive) : cconf := (StA, (Ap_Alph_10_11_11 p ++ [S1;S1;S0], S0, [])).
Local Notation Cc := Cc_0RB0LC_1LC1RB_1RD1LA_1LB1RD.

(** ** The certificate *)

Definition A0_0RB0LC_1LC1RB_1RD1LA_1LB1RD : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition A1_0RB0LC_1LC1RB_1RD1LA_1LB1RD : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chi_0RB0LC_1LC1RB_1RD1LA_1LB1RD : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_int_0RB0LC_1LC1RB_1RD1LA_1LB1RD : srun tm false true chi_0RB0LC_1LC1RB_1RD1LA_1LB1RD A0_0RB0LC_1LC1RB_1RD1LA_1LB1RD = Some (A1_0RB0LC_1LC1RB_1RD1LA_1LB1RD, 4, 4).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB0LC_1LC1RB_1RD1LA_1LB1RD : sconf := mkC StA (mkS [] [S1;S1] 1 1 [S1;S1;S1;S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_0RB0LC_1LC1RB_1RD1LA_1LB1RD : sconf := mkC StA (mkS [] [S1;S0] 1 2 [S1;S1;S1;S1]) S0 (mkS [] [] 0 0 []).
(** ** The INNER anchor family -- Ip at StA *)
Definition Cin_0RB0LC_1LC1RB_1RD1LA_1LB1RD (v : positive) : cconf := (StA, (Ip v ++ [S0;S1;S1], S0, [])).
Local Notation Cin := Cin_0RB0LC_1LC1RB_1RD1LA_1LB1RD.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow2_0RB0LC_1LC1RB_1RD1LA_1LB1RD : forall n, Ip (pow2 n) = rep [S1;S0] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap -- ordinary and affine.  Iterating it to the fill is
    where a [Theta(2^j)] lives, and [inner_to_fill_lift] keeps it inside an
    existential. *)
Definition AI0_0RB0LC_1LC1RB_1RD1LA_1LB1RD : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition AI1_0RB0LC_1LC1RB_1RD1LA_1LB1RD : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chn_0RB0LC_1LC1RB_1RD1LA_1LB1RD : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_inner_0RB0LC_1LC1RB_1RD1LA_1LB1RD : srun tm false true chn_0RB0LC_1LC1RB_1RD1LA_1LB1RD AI0_0RB0LC_1LC1RB_1RD1LA_1LB1RD = Some (AI1_0RB0LC_1LC1RB_1RD1LA_1LB1RD, 4, 4).
Proof. vm_compute. reflexivity. Qed.

(** The OFFSET start: [E (2^(n+2)+2)] is fixed digit blocks, then the rep.
    Its block count is one short of the outer index, which is why [lapo_]
    below REINDEXES at [j = S j']. *)
Lemma epre_0RB0LC_1LC1RB_1RD1LA_1LB1RD : forall n, Ip (xO (xI (pow2 n))) = [S1;S0;S1;S1] ++ rep [S1;S0] n ++ [S1].
Proof.
  intro n. cbn [Ip]. rewrite epow2_0RB0LC_1LC1RB_1RD1LA_1LB1RD.
  cbn [app]. rewrite <- ?app_assoc. cbn [app]. reflexivity.
Qed.

(** *** boot: the outer overflow anchor -> the first inner anchor at [pow2 j] *)
Definition BB1_0RB0LC_1LC1RB_1RD1LA_1LB1RD : sconf := mkC StA (mkS [S1;S0;S1;S1] [S1;S0] 1 1 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chb_0RB0LC_1LC1RB_1RD1LA_1LB1RD : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 8; SCycR 2; SWin 4; SRotL 1; SWin 1; SRotL 1; SWin 4; SWinR 1].

Lemma run_boot_0RB0LC_1LC1RB_1RD1LA_1LB1RD : srun tm true true chb_0RB0LC_1LC1RB_1RD1LA_1LB1RD B0_0RB0LC_1LC1RB_1RD1LA_1LB1RD = Some (BB1_0RB0LC_1LC1RB_1RD1LA_1LB1RD, 4, 23).
Proof. vm_compute. reflexivity. Qed.

(** *** exit: the last inner all-ones fill -> the outer successor *)
Definition BE0_0RB0LC_1LC1RB_1RD1LA_1LB1RD : sconf := mkC StA (mkS [] [S1;S1] 1 2 [S1;S0;S1;S1]) S0 (mkS [] [] 0 0 []).
Definition che_0RB0LC_1LC1RB_1RD1LA_1LB1RD : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_exit_0RB0LC_1LC1RB_1RD1LA_1LB1RD : srun tm true true che_0RB0LC_1LC1RB_1RD1LA_1LB1RD BE0_0RB0LC_1LC1RB_1RD1LA_1LB1RD = Some (B1_0RB0LC_1LC1RB_1RD1LA_1LB1RD, 4, 12).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_0RB0LC_1LC1RB_1RD1LA_1LB1RD : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Ap_Alph_10_11_11 q0 ++ [S1;S1;S0]) [] j A0_0RB0LC_1LC1RB_1RD1LA_1LB1RD.
Proof.
  intros p j q0 E. destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (H1 & _).
  unfold Cc_0RB0LC_1LC1RB_1RD1LA_1LB1RD, cden, A0_0RB0LC_1LC1RB_1RD1LA_1LB1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gei_0RB0LC_1LC1RB_1RD1LA_1LB1RD : forall p j q0, cview p = (j, Some q0) ->
  cden (Ap_Alph_10_11_11 q0 ++ [S1;S1;S0]) [] j A1_0RB0LC_1LC1RB_1RD1LA_1LB1RD = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (_ & H2).
  unfold Cc_0RB0LC_1LC1RB_1RD1LA_1LB1RD, cden, A1_0RB0LC_1LC1RB_1RD1LA_1LB1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_0RB0LC_1LC1RB_1RD1LA_1LB1RD : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (4 * j + 4). split; [lia|].
  rewrite (gsi_0RB0LC_1LC1RB_1RD1LA_1LB1RD p j q0 E).
  rewrite (srun_sound tm false true chi_0RB0LC_1LC1RB_1RD1LA_1LB1RD A0_0RB0LC_1LC1RB_1RD1LA_1LB1RD A1_0RB0LC_1LC1RB_1RD1LA_1LB1RD 4 4
             run_int_0RB0LC_1LC1RB_1RD1LA_1LB1RD (Ap_Alph_10_11_11 q0 ++ [S1;S1;S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_0RB0LC_1LC1RB_1RD1LA_1LB1RD p j q0 E).
Qed.

Lemma gso_0RB0LC_1LC1RB_1RD1LA_1LB1RD : forall p j, cview p = (S (S j), None) ->
  Cc p = cden [] [] j B0_0RB0LC_1LC1RB_1RD1LA_1LB1RD.
Proof.
  intros p j E. destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p (S j) E) as (H1 & _).
  unfold Cc_0RB0LC_1LC1RB_1RD1LA_1LB1RD, cden, B0_0RB0LC_1LC1RB_1RD1LA_1LB1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 1) with ((S j)) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_0RB0LC_1LC1RB_1RD1LA_1LB1RD : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_0RB0LC_1LC1RB_1RD1LA_1LB1RD : forall p j, cview p = (S (S j), None) ->
  lift (cden [] [] j B1_0RB0LC_1LC1RB_1RD1LA_1LB1RD) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p (S j) E) as (_ & H2).
  assert (HD : cden [] [] j B1_0RB0LC_1LC1RB_1RD1LA_1LB1RD
             = (StA, (rep [S1;S0] (S (S j)) ++ [S1;S1;S1;S1], S0, []))).
  { unfold cden, B1_0RB0LC_1LC1RB_1RD1LA_1LB1RD, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 2) with (S (S j)) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StA, ((rep [S1;S0] (S (S j)) ++ [S1;S1;S1;S1]) ++ [S0], S0, []))).
  { unfold Cc_0RB0LC_1LC1RB_1RD1LA_1LB1RD. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_0RB0LC_1LC1RB_1RD1LA_1LB1RD. reflexivity.
Qed.

Lemma gsn_0RB0LC_1LC1RB_1RD1LA_1LB1RD : forall v i q0, cview v = (i, Some q0) ->
  Cin v = cden (Ip q0 ++ [S0;S1;S1]) [] i AI0_0RB0LC_1LC1RB_1RD1LA_1LB1RD.
Proof.
  intros v i q0 E. destruct (ILCounter.cview_some_I v i q0 E) as (H1 & _).
  unfold Cin_0RB0LC_1LC1RB_1RD1LA_1LB1RD, cden, AI0_0RB0LC_1LC1RB_1RD1LA_1LB1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen_0RB0LC_1LC1RB_1RD1LA_1LB1RD : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Ip q0 ++ [S0;S1;S1]) [] i AI1_0RB0LC_1LC1RB_1RD1LA_1LB1RD) = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (ILCounter.cview_some_I v i q0 E) as (_ & H2).
  unfold Cin_0RB0LC_1LC1RB_1RD1LA_1LB1RD, cden, AI1_0RB0LC_1LC1RB_1RD1LA_1LB1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S0] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin_0RB0LC_1LC1RB_1RD1LA_1LB1RD : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 4), (cden (Ip q0 ++ [S0;S1;S1]) [] i AI1_0RB0LC_1LC1RB_1RD1LA_1LB1RD).
  split; [lia|]. split; [| exact (gen_0RB0LC_1LC1RB_1RD1LA_1LB1RD v i q0 E)].
  rewrite (gsn_0RB0LC_1LC1RB_1RD1LA_1LB1RD v i q0 E).
  exact (srun_sound tm false true chn_0RB0LC_1LC1RB_1RD1LA_1LB1RD AI0_0RB0LC_1LC1RB_1RD1LA_1LB1RD AI1_0RB0LC_1LC1RB_1RD1LA_1LB1RD 4 4
           run_inner_0RB0LC_1LC1RB_1RD1LA_1LB1RD (Ip q0 ++ [S0;S1;S1]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The boot lands on the OFFSET inner anchor up to 0/0 trailing
    blanks. *)
Lemma gbo_0RB0LC_1LC1RB_1RD1LA_1LB1RD : forall j, lift (cden [] [] j BB1_0RB0LC_1LC1RB_1RD1LA_1LB1RD) = lift (Cin (xO (xI (pow2 j)))).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_0RB0LC_1LC1RB_1RD1LA_1LB1RD = (StA, ([S1;S0;S1;S1] ++ rep [S1;S0] j ++ [S1;S0;S1;S1], S0, []))).
  { unfold cden, BB1_0RB0LC_1LC1RB_1RD1LA_1LB1RD, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (j + 1) by lia.
    rewrite rep_add. cbn [rep app]. rewrite ?app_nil_r.
    rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin (xO (xI (pow2 j))) = (StA, ([S1;S0;S1;S1] ++ rep [S1;S0] j ++ [S1;S0;S1;S1], S0, []))).
  { unfold Cin_0RB0LC_1LC1RB_1RD1LA_1LB1RD. rewrite epre_0RB0LC_1LC1RB_1RD1LA_1LB1RD.
    first [ rewrite <- ?app_assoc; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  (* The offset boot can land one written blank past the anchor on EITHER
     side, and [lift] sees neither.  Strip it FIRST: [cbn [app]] flattens
     `w ++ [S0]` into one literal and destroys the shape
     [WTape.lift_app_blank_l] matches on. *)
  rewrite HD, HC. rewrite ?lift_app_blank_l.
  cbn [app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?lbl_0RB0LC_1LC1RB_1RD1LA_1LB1RD. rewrite ?lift_app_blank. reflexivity.
Qed.

(** The offset family's all-ones fill is the ordinary one two octaves up:
    [fill (xO (xI (pow2 j))) = fill (pow2 (S (S j)))] by computation, so
    [cview_fill_pow2] still names the exit chain's start word. *)
Lemma gxi_0RB0LC_1LC1RB_1RD1LA_1LB1RD : forall j, Cin (fill (xO (xI (pow2 j)))) = cden [] [] j BE0_0RB0LC_1LC1RB_1RD1LA_1LB1RD.
Proof.
  intro j.
  assert (Hf : fill (xO (xI (pow2 j))) = fill (pow2 (S (S j))))
    by (cbn [pow2 fill]; reflexivity).
  rewrite Hf.
  destruct (ILCounter.cview_none_I (fill (pow2 (S (S j)))) (S (S j))
              (cview_fill_pow2 (S (S j)))) as (H1 & _).
  unfold Cin_0RB0LC_1LC1RB_1RD1LA_1LB1RD, cden, BE0_0RB0LC_1LC1RB_1RD1LA_1LB1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 2) with (S (S j)) by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

(** The interior lap, restated up to [lift] -- what [vis_via_ovf_lift] and
    [vis_via_fill] consume. *)
Lemma lapil_0RB0LC_1LC1RB_1RD1LA_1LB1RD : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof. intros p j q0 E. destruct (lapi_0RB0LC_1LC1RB_1RD1LA_1LB1RD p j q0 E) as (n & Hn & Hr).
  exists n, (Cc (Pos.succ p)).
  split; [exact Hn | split; [exact Hr | reflexivity]]. Qed.

(** [cview p = (1, None)] forces [p = 1], where the offset family's count is
    empty: the overflow lap at p = 1 is ONE CONCRETE run, checked the way the
    bootstrap lemma is. *)
Lemma lapo0_0RB0LC_1LC1RB_1RD1LA_1LB1RD : exists n c', csteps tm n (Cc 1) = Some c'
    /\ lift c' = lift (Cc 2) /\ 0 < n.
Proof.
  exists 19.
  assert (H : match csteps tm 19 (Cc 1) with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 19 (Cc 1)) as [c|] eqn:E0; [|discriminate].
  exists c. split; [reflexivity|]. split; [apply ceqb_lift; exact H | lia].
Qed.

(** The outer OVERFLOW branch.  The offset family's block count is one short
    of the outer index, so the branch REINDEXES: the generic route runs at
    [j = S j'] and [j = 0] is the concrete lap above. *)
Lemma lapo_0RB0LC_1LC1RB_1RD1LA_1LB1RD : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E.
  destruct j as [|j'].
  - rewrite (cview_none_shape p 0 E). exact lapo0_0RB0LC_1LC1RB_1RD1LA_1LB1RD.
  - apply (nested_overflow_lift tm Cc Cin lapin_0RB0LC_1LC1RB_1RD1LA_1LB1RD p (xO (xI (pow2 j')))).
    + exists (4 * j' + 23), (cden [] [] j' BB1_0RB0LC_1LC1RB_1RD1LA_1LB1RD).
      split; [lia|]. split; [| exact (gbo_0RB0LC_1LC1RB_1RD1LA_1LB1RD j')].
      rewrite (gso_0RB0LC_1LC1RB_1RD1LA_1LB1RD p j' E).
      exact (srun_sound tm true true chb_0RB0LC_1LC1RB_1RD1LA_1LB1RD B0_0RB0LC_1LC1RB_1RD1LA_1LB1RD BB1_0RB0LC_1LC1RB_1RD1LA_1LB1RD 4 23
               run_boot_0RB0LC_1LC1RB_1RD1LA_1LB1RD [] [] j' ltac:(reflexivity) ltac:(reflexivity)).
    + exists (4 * j' + 12), (cden [] [] j' B1_0RB0LC_1LC1RB_1RD1LA_1LB1RD).
      split; [| exact (geo_0RB0LC_1LC1RB_1RD1LA_1LB1RD p j' E)].
      rewrite (gxi_0RB0LC_1LC1RB_1RD1LA_1LB1RD j').
      exact (srun_sound tm true true che_0RB0LC_1LC1RB_1RD1LA_1LB1RD BE0_0RB0LC_1LC1RB_1RD1LA_1LB1RD B1_0RB0LC_1LC1RB_1RD1LA_1LB1RD 4 12
               run_exit_0RB0LC_1LC1RB_1RD1LA_1LB1RD [] [] j' ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** State StA's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StA_0RB0LC_1LC1RB_1RD1LA_1LB1RD : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StA.
Proof. exists 0. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StB's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StB_0RB0LC_1LC1RB_1RD1LA_1LB1RD : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StB.
Proof. exists 1. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StC's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StC_0RB0LC_1LC1RB_1RD1LA_1LB1RD : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StC.
Proof. exists 6. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StD's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StD_0RB0LC_1LC1RB_1RD1LA_1LB1RD : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StD.
Proof. exists 11. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.



(** ** The lap *)

Lemma lap_0RB0LC_1LC1RB_1RD1LA_1LB1RD : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB0LC_1LC1RB_1RD1LA_1LB1RD p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->). exact (lapo_0RB0LC_1LC1RB_1RD1LA_1LB1RD p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_0RB0LC_1LC1RB_1RD1LA_1LB1RD : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 15.
  assert (H : match csteps tm 15 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 15 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma viso_0RB0LC_1LC1RB_1RD1LA_1LB1RD : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_0RB0LC_1LC1RB_1RD1LA_1LB1RD = Some q ->
  forall p j, cview p = (S (S j), None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_0RB0LC_1LC1RB_1RD1LA_1LB1RD p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB0LC_1LC1RB_1RD1LA_1LB1RD p j E)].
Qed.

Lemma vis_0RB0LC_1LC1RB_1RD1LA_1LB1RD : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_0RB0LC_1LC1RB_1RD1LA_1LB1RD.
  destruct q.

  - (* StA: the anchor state *)
    exists 0. eexists. split; reflexivity.
  - (* StB *)
    apply (vis_via_ovf tm Cc Hi StB).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1). exact visz_StB_0RB0LC_1LC1RB_1RD1LA_1LB1RD.
    + exact (viso_0RB0LC_1LC1RB_1RD1LA_1LB1RD [SRotL 1; SWin 1] StB ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* StC *)
    apply (vis_via_ovf tm Cc Hi StC).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1). exact visz_StC_0RB0LC_1LC1RB_1RD1LA_1LB1RD.
    + exact (viso_0RB0LC_1LC1RB_1RD1LA_1LB1RD [SRotL 1; SWin 1; SCycL 2 0; SWin 5] StC ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* StD *)
    apply (vis_via_ovf tm Cc Hi StD).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1). exact visz_StD_0RB0LC_1LC1RB_1RD1LA_1LB1RD.
    + exact (viso_0RB0LC_1LC1RB_1RD1LA_1LB1RD [SRotL 1; SWin 1; SCycL 2 0; SWin 8; SCycR 2; SWin 2] StD ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
Qed.

Theorem nqhm_0RB0LC_1LC1RB_1RD1LA_1LB1RD : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 1). - exact boot_0RB0LC_1LC1RB_1RD1LA_1LB1RD. - intros p _. apply lap_0RB0LC_1LC1RB_1RD1LA_1LB1RD. - intros p q _. apply vis_0RB0LC_1LC1RB_1RD1LA_1LB1RD. Qed.

Theorem nqh_0RB0LC_1LC1RB_1RD1LA_1LB1RD : NeverQuasiHaltsSt tm_0RB0LC_1LC1RB_1RD1LA_1LB1RD.
Proof. apply (mirror_never_qh tm_0RB0LC_1LC1RB_1RD1LA_1LB1RD). rewrite mirror_ok_0RB0LC_1LC1RB_1RD1LA_1LB1RD. exact nqhm_0RB0LC_1LC1RB_1RD1LA_1LB1RD. Qed.

Theorem nonhalt_0RB0LC_1LC1RB_1RD1LA_1LB1RD : NonHalt tm_0RB0LC_1LC1RB_1RD1LA_1LB1RD.
Proof. apply never_qh_nonhalt, nqh_0RB0LC_1LC1RB_1RD1LA_1LB1RD. Qed.
