(** * NLAP_1RB1RC_1RC1LB_1LA1RD_0LB0RC: machine 1RB1RC_1RC1LB_1LA1RD_0LB0RC, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Ap_Alph_10_11_11 digit alphabet (Alph_10_11_11.v), anchored at

      Cc p = (StD, (Ap_Alph_10_11_11 p ++ [S1;S1;S0], S0, []))

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
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter Alph_10_11_11 LapCertGlue LapCertGlueLift IXPGadgets NestedLap NestedLapLift ILCounter.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_1RB1RC_1RC1LB_1LA1RD_0LB0RC (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1RC_1RC1LB_1LA1RD_0LB0RC.

(** 1RB1RC_1RC1LB_1LA1RD_0LB0RC *)
Definition tm_1RB1RC_1RC1LB_1LA1RD_0LB0RC : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DR StC
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S1 DL StA | StC, S1 => mk S1 DR StD
  | StD, S0 => mk S0 DL StB | StD, S1 => mk S0 DR StC end.
Local Notation tm := tm_1RB1RC_1RC1LB_1LA1RD_0LB0RC.

Definition Cc_1RB1RC_1RC1LB_1LA1RD_0LB0RC (p : positive) : cconf := (StD, (Ap_Alph_10_11_11 p ++ [S1;S1;S0], S0, [])).
Local Notation Cc := Cc_1RB1RC_1RC1LB_1LA1RD_0LB0RC.

(** ** The certificate *)

Definition A0_1RB1RC_1RC1LB_1LA1RD_0LB0RC : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition A1_1RB1RC_1RC1LB_1LA1RD_0LB0RC : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chi_1RB1RC_1RC1LB_1LA1RD_0LB0RC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_int_1RB1RC_1RC1LB_1LA1RD_0LB0RC : srun tm false true chi_1RB1RC_1RC1LB_1LA1RD_0LB0RC A0_1RB1RC_1RC1LB_1LA1RD_0LB0RC = Some (A1_1RB1RC_1RC1LB_1LA1RD_0LB0RC, 4, 4).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB1RC_1RC1LB_1LA1RD_0LB0RC : sconf := mkC StD (mkS [] [S1;S1] 1 1 [S1;S1;S1;S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_1RB1RC_1RC1LB_1LA1RD_0LB0RC : sconf := mkC StD (mkS [] [S1;S0] 1 2 [S1;S1;S1;S1]) S0 (mkS [] [] 0 0 []).
(** ** The INNER anchor family -- Ip at StD *)
Definition Cin_1RB1RC_1RC1LB_1LA1RD_0LB0RC (v : positive) : cconf := (StD, (Ip v ++ [S0;S1;S1], S0, [])).
Local Notation Cin := Cin_1RB1RC_1RC1LB_1LA1RD_0LB0RC.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow2_1RB1RC_1RC1LB_1LA1RD_0LB0RC : forall n, Ip (pow2 n) = rep [S1;S0] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap -- ordinary and affine.  Iterating it to the fill is
    where a [Theta(2^j)] lives, and [inner_to_fill_lift] keeps it inside an
    existential. *)
Definition AI0_1RB1RC_1RC1LB_1LA1RD_0LB0RC : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition AI1_1RB1RC_1RC1LB_1LA1RD_0LB0RC : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chn_1RB1RC_1RC1LB_1LA1RD_0LB0RC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_inner_1RB1RC_1RC1LB_1LA1RD_0LB0RC : srun tm false true chn_1RB1RC_1RC1LB_1LA1RD_0LB0RC AI0_1RB1RC_1RC1LB_1LA1RD_0LB0RC = Some (AI1_1RB1RC_1RC1LB_1LA1RD_0LB0RC, 4, 4).
Proof. vm_compute. reflexivity. Qed.

(** The OFFSET start: [E (2^(n+2)+2)] is fixed digit blocks, then the rep.
    Its block count is one short of the outer index, which is why [lapo_]
    below REINDEXES at [j = S j']. *)
Lemma epre_1RB1RC_1RC1LB_1LA1RD_0LB0RC : forall n, Ip (xO (xI (pow2 n))) = [S1;S0;S1;S1] ++ rep [S1;S0] n ++ [S1].
Proof.
  intro n. cbn [Ip]. rewrite epow2_1RB1RC_1RC1LB_1LA1RD_0LB0RC.
  cbn [app]. rewrite <- ?app_assoc. cbn [app]. reflexivity.
Qed.

(** *** boot: the outer overflow anchor -> the first inner anchor at [pow2 j] *)
Definition BB1_1RB1RC_1RC1LB_1LA1RD_0LB0RC : sconf := mkC StD (mkS [S1;S0;S1;S1] [S1;S0] 1 1 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chb_1RB1RC_1RC1LB_1LA1RD_0LB0RC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 8; SCycR 2; SWin 4; SRotL 1; SWin 1; SRotL 1; SWin 4; SWinR 1].

Lemma run_boot_1RB1RC_1RC1LB_1LA1RD_0LB0RC : srun tm true true chb_1RB1RC_1RC1LB_1LA1RD_0LB0RC B0_1RB1RC_1RC1LB_1LA1RD_0LB0RC = Some (BB1_1RB1RC_1RC1LB_1LA1RD_0LB0RC, 4, 23).
Proof. vm_compute. reflexivity. Qed.

(** *** exit: the last inner all-ones fill -> the outer successor *)
Definition BE0_1RB1RC_1RC1LB_1LA1RD_0LB0RC : sconf := mkC StD (mkS [] [S1;S1] 1 2 [S1;S0;S1;S1]) S0 (mkS [] [] 0 0 []).
Definition che_1RB1RC_1RC1LB_1LA1RD_0LB0RC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_exit_1RB1RC_1RC1LB_1LA1RD_0LB0RC : srun tm true true che_1RB1RC_1RC1LB_1LA1RD_0LB0RC BE0_1RB1RC_1RC1LB_1LA1RD_0LB0RC = Some (B1_1RB1RC_1RC1LB_1LA1RD_0LB0RC, 4, 12).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_1RB1RC_1RC1LB_1LA1RD_0LB0RC : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Ap_Alph_10_11_11 q0 ++ [S1;S1;S0]) [] j A0_1RB1RC_1RC1LB_1LA1RD_0LB0RC.
Proof.
  intros p j q0 E. destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (H1 & _).
  unfold Cc_1RB1RC_1RC1LB_1LA1RD_0LB0RC, cden, A0_1RB1RC_1RC1LB_1LA1RD_0LB0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gei_1RB1RC_1RC1LB_1LA1RD_0LB0RC : forall p j q0, cview p = (j, Some q0) ->
  cden (Ap_Alph_10_11_11 q0 ++ [S1;S1;S0]) [] j A1_1RB1RC_1RC1LB_1LA1RD_0LB0RC = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (_ & H2).
  unfold Cc_1RB1RC_1RC1LB_1LA1RD_0LB0RC, cden, A1_1RB1RC_1RC1LB_1LA1RD_0LB0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB1RC_1RC1LB_1LA1RD_0LB0RC : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (4 * j + 4). split; [lia|].
  rewrite (gsi_1RB1RC_1RC1LB_1LA1RD_0LB0RC p j q0 E).
  rewrite (srun_sound tm false true chi_1RB1RC_1RC1LB_1LA1RD_0LB0RC A0_1RB1RC_1RC1LB_1LA1RD_0LB0RC A1_1RB1RC_1RC1LB_1LA1RD_0LB0RC 4 4
             run_int_1RB1RC_1RC1LB_1LA1RD_0LB0RC (Ap_Alph_10_11_11 q0 ++ [S1;S1;S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_1RB1RC_1RC1LB_1LA1RD_0LB0RC p j q0 E).
Qed.

Lemma gso_1RB1RC_1RC1LB_1LA1RD_0LB0RC : forall p j, cview p = (S (S j), None) ->
  Cc p = cden [] [] j B0_1RB1RC_1RC1LB_1LA1RD_0LB0RC.
Proof.
  intros p j E. destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p (S j) E) as (H1 & _).
  unfold Cc_1RB1RC_1RC1LB_1LA1RD_0LB0RC, cden, B0_1RB1RC_1RC1LB_1LA1RD_0LB0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 1) with ((S j)) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB1RC_1RC1LB_1LA1RD_0LB0RC : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB1RC_1RC1LB_1LA1RD_0LB0RC : forall p j, cview p = (S (S j), None) ->
  lift (cden [] [] j B1_1RB1RC_1RC1LB_1LA1RD_0LB0RC) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p (S j) E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB1RC_1RC1LB_1LA1RD_0LB0RC
             = (StD, (rep [S1;S0] (S (S j)) ++ [S1;S1;S1;S1], S0, []))).
  { unfold cden, B1_1RB1RC_1RC1LB_1LA1RD_0LB0RC, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 2) with (S (S j)) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StD, ((rep [S1;S0] (S (S j)) ++ [S1;S1;S1;S1]) ++ [S0], S0, []))).
  { unfold Cc_1RB1RC_1RC1LB_1LA1RD_0LB0RC. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_1RB1RC_1RC1LB_1LA1RD_0LB0RC. reflexivity.
Qed.

Lemma gsn_1RB1RC_1RC1LB_1LA1RD_0LB0RC : forall v i q0, cview v = (i, Some q0) ->
  Cin v = cden (Ip q0 ++ [S0;S1;S1]) [] i AI0_1RB1RC_1RC1LB_1LA1RD_0LB0RC.
Proof.
  intros v i q0 E. destruct (ILCounter.cview_some_I v i q0 E) as (H1 & _).
  unfold Cin_1RB1RC_1RC1LB_1LA1RD_0LB0RC, cden, AI0_1RB1RC_1RC1LB_1LA1RD_0LB0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen_1RB1RC_1RC1LB_1LA1RD_0LB0RC : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Ip q0 ++ [S0;S1;S1]) [] i AI1_1RB1RC_1RC1LB_1LA1RD_0LB0RC) = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (ILCounter.cview_some_I v i q0 E) as (_ & H2).
  unfold Cin_1RB1RC_1RC1LB_1LA1RD_0LB0RC, cden, AI1_1RB1RC_1RC1LB_1LA1RD_0LB0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S0] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin_1RB1RC_1RC1LB_1LA1RD_0LB0RC : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 4), (cden (Ip q0 ++ [S0;S1;S1]) [] i AI1_1RB1RC_1RC1LB_1LA1RD_0LB0RC).
  split; [lia|]. split; [| exact (gen_1RB1RC_1RC1LB_1LA1RD_0LB0RC v i q0 E)].
  rewrite (gsn_1RB1RC_1RC1LB_1LA1RD_0LB0RC v i q0 E).
  exact (srun_sound tm false true chn_1RB1RC_1RC1LB_1LA1RD_0LB0RC AI0_1RB1RC_1RC1LB_1LA1RD_0LB0RC AI1_1RB1RC_1RC1LB_1LA1RD_0LB0RC 4 4
           run_inner_1RB1RC_1RC1LB_1LA1RD_0LB0RC (Ip q0 ++ [S0;S1;S1]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The boot lands on the OFFSET inner anchor up to 0/0 trailing
    blanks. *)
Lemma gbo_1RB1RC_1RC1LB_1LA1RD_0LB0RC : forall j, lift (cden [] [] j BB1_1RB1RC_1RC1LB_1LA1RD_0LB0RC) = lift (Cin (xO (xI (pow2 j)))).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_1RB1RC_1RC1LB_1LA1RD_0LB0RC = (StD, ([S1;S0;S1;S1] ++ rep [S1;S0] j ++ [S1;S0;S1;S1], S0, []))).
  { unfold cden, BB1_1RB1RC_1RC1LB_1LA1RD_0LB0RC, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (j + 1) by lia.
    rewrite rep_add. cbn [rep app]. rewrite ?app_nil_r.
    rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin (xO (xI (pow2 j))) = (StD, ([S1;S0;S1;S1] ++ rep [S1;S0] j ++ [S1;S0;S1;S1], S0, []))).
  { unfold Cin_1RB1RC_1RC1LB_1LA1RD_0LB0RC. rewrite epre_1RB1RC_1RC1LB_1LA1RD_0LB0RC.
    first [ rewrite <- ?app_assoc; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  (* The offset boot can land one written blank past the anchor on EITHER
     side, and [lift] sees neither.  Strip it FIRST: [cbn [app]] flattens
     `w ++ [S0]` into one literal and destroys the shape
     [WTape.lift_app_blank_l] matches on. *)
  rewrite HD, HC. rewrite ?lift_app_blank_l.
  cbn [app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?lbl_1RB1RC_1RC1LB_1LA1RD_0LB0RC. rewrite ?lift_app_blank. reflexivity.
Qed.

(** The offset family's all-ones fill is the ordinary one two octaves up:
    [fill (xO (xI (pow2 j))) = fill (pow2 (S (S j)))] by computation, so
    [cview_fill_pow2] still names the exit chain's start word. *)
Lemma gxi_1RB1RC_1RC1LB_1LA1RD_0LB0RC : forall j, Cin (fill (xO (xI (pow2 j)))) = cden [] [] j BE0_1RB1RC_1RC1LB_1LA1RD_0LB0RC.
Proof.
  intro j.
  assert (Hf : fill (xO (xI (pow2 j))) = fill (pow2 (S (S j))))
    by (cbn [pow2 fill]; reflexivity).
  rewrite Hf.
  destruct (ILCounter.cview_none_I (fill (pow2 (S (S j)))) (S (S j))
              (cview_fill_pow2 (S (S j)))) as (H1 & _).
  unfold Cin_1RB1RC_1RC1LB_1LA1RD_0LB0RC, cden, BE0_1RB1RC_1RC1LB_1LA1RD_0LB0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 2) with (S (S j)) by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

(** The interior lap, restated up to [lift] -- what [vis_via_ovf_lift] and
    [vis_via_fill] consume. *)
Lemma lapil_1RB1RC_1RC1LB_1LA1RD_0LB0RC : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof. intros p j q0 E. destruct (lapi_1RB1RC_1RC1LB_1LA1RD_0LB0RC p j q0 E) as (n & Hn & Hr).
  exists n, (Cc (Pos.succ p)).
  split; [exact Hn | split; [exact Hr | reflexivity]]. Qed.

(** [cview p = (1, None)] forces [p = 1], where the offset family's count is
    empty: the overflow lap at p = 1 is ONE CONCRETE run, checked the way the
    bootstrap lemma is. *)
Lemma lapo0_1RB1RC_1RC1LB_1LA1RD_0LB0RC : exists n c', csteps tm n (Cc 1) = Some c'
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
Lemma lapo_1RB1RC_1RC1LB_1LA1RD_0LB0RC : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E.
  destruct j as [|j'].
  - rewrite (cview_none_shape p 0 E). exact lapo0_1RB1RC_1RC1LB_1LA1RD_0LB0RC.
  - apply (nested_overflow_lift tm Cc Cin lapin_1RB1RC_1RC1LB_1LA1RD_0LB0RC p (xO (xI (pow2 j')))).
    + exists (4 * j' + 23), (cden [] [] j' BB1_1RB1RC_1RC1LB_1LA1RD_0LB0RC).
      split; [lia|]. split; [| exact (gbo_1RB1RC_1RC1LB_1LA1RD_0LB0RC j')].
      rewrite (gso_1RB1RC_1RC1LB_1LA1RD_0LB0RC p j' E).
      exact (srun_sound tm true true chb_1RB1RC_1RC1LB_1LA1RD_0LB0RC B0_1RB1RC_1RC1LB_1LA1RD_0LB0RC BB1_1RB1RC_1RC1LB_1LA1RD_0LB0RC 4 23
               run_boot_1RB1RC_1RC1LB_1LA1RD_0LB0RC [] [] j' ltac:(reflexivity) ltac:(reflexivity)).
    + exists (4 * j' + 12), (cden [] [] j' B1_1RB1RC_1RC1LB_1LA1RD_0LB0RC).
      split; [| exact (geo_1RB1RC_1RC1LB_1LA1RD_0LB0RC p j' E)].
      rewrite (gxi_1RB1RC_1RC1LB_1LA1RD_0LB0RC j').
      exact (srun_sound tm true true che_1RB1RC_1RC1LB_1LA1RD_0LB0RC BE0_1RB1RC_1RC1LB_1LA1RD_0LB0RC B1_1RB1RC_1RC1LB_1LA1RD_0LB0RC 4 12
               run_exit_1RB1RC_1RC1LB_1LA1RD_0LB0RC [] [] j' ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** State StA's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StA_1RB1RC_1RC1LB_1LA1RD_0LB0RC : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StA.
Proof. exists 11. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StB's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StB_1RB1RC_1RC1LB_1LA1RD_0LB0RC : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StB.
Proof. exists 1. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StC's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StC_1RB1RC_1RC1LB_1LA1RD_0LB0RC : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StC.
Proof. exists 6. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StD's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StD_1RB1RC_1RC1LB_1LA1RD_0LB0RC : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StD.
Proof. exists 0. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.



(** ** The lap *)

Lemma lap_1RB1RC_1RC1LB_1LA1RD_0LB0RC : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB1RC_1RC1LB_1LA1RD_0LB0RC p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->). exact (lapo_1RB1RC_1RC1LB_1LA1RD_0LB0RC p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_1RB1RC_1RC1LB_1LA1RD_0LB0RC : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 17.
  assert (H : match csteps tm 17 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 17 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma viso_1RB1RC_1RC1LB_1LA1RD_0LB0RC : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_1RB1RC_1RC1LB_1LA1RD_0LB0RC = Some q ->
  forall p j, cview p = (S (S j), None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_1RB1RC_1RC1LB_1LA1RD_0LB0RC p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB1RC_1RC1LB_1LA1RD_0LB0RC p j E)].
Qed.

Lemma vis_1RB1RC_1RC1LB_1LA1RD_0LB0RC : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_1RB1RC_1RC1LB_1LA1RD_0LB0RC.
  destruct q.

  - (* StA *)
    apply (vis_via_ovf tm Cc Hi StA).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1). exact visz_StA_1RB1RC_1RC1LB_1LA1RD_0LB0RC.
    + exact (viso_1RB1RC_1RC1LB_1LA1RD_0LB0RC [SRotL 1; SWin 1; SCycL 2 0; SWin 8; SCycR 2; SWin 2] StA ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* StB *)
    apply (vis_via_ovf tm Cc Hi StB).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1). exact visz_StB_1RB1RC_1RC1LB_1LA1RD_0LB0RC.
    + exact (viso_1RB1RC_1RC1LB_1LA1RD_0LB0RC [SRotL 1; SWin 1] StB ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* StC *)
    apply (vis_via_ovf tm Cc Hi StC).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1). exact visz_StC_1RB1RC_1RC1LB_1LA1RD_0LB0RC.
    + exact (viso_1RB1RC_1RC1LB_1LA1RD_0LB0RC [SRotL 1; SWin 1; SCycL 2 0; SWin 5] StC ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* StD: the anchor state *)
    exists 0. eexists. split; reflexivity.
Qed.

Theorem nqh_1RB1RC_1RC1LB_1LA1RD_0LB0RC : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 1). - exact boot_1RB1RC_1RC1LB_1LA1RD_0LB0RC. - intros p _. apply lap_1RB1RC_1RC1LB_1LA1RD_0LB0RC. - intros p q _. apply vis_1RB1RC_1RC1LB_1LA1RD_0LB0RC. Qed.

Theorem nonhalt_1RB1RC_1RC1LB_1LA1RD_0LB0RC : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_1RB1RC_1RC1LB_1LA1RD_0LB0RC. Qed.
