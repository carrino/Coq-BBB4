(** * LAPT_0RB0LD_1RC1LB_1LB1RA_0RC1LD: TRANSITION-LEVEL board for machine 0RB0LD_1RC1LB_1LB1RA_0RC1LD, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Jp digit alphabet (JpCounter.v), anchored at

      Cc p = (StD, (Jp p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  6*j+4 steps
      overflow  (cview p = (S j, None)):   6*j+12 steps

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 198 anchors.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter JpCounter LapCertGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
From BBB4 Require Import BBBT4_Statement.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr.
Import ListNotations.

Definition mk_0RB0LD_1RC1LB_1LB1RA_0RC1LD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB0LD_1RC1LB_1LB1RA_0RC1LD.

(** 0RB0LD_1RC1LB_1LB1RA_0RC1LD *)
(** 0RB0LD_1RC1LB_1LB1RA_0RC1LD -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB0LD_1RC1LB_1LB1RA_0RC1LD : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S0 DL StD
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S1 DL StB | StC, S1 => mk S1 DR StA
  | StD, S0 => mk S0 DR StC | StD, S1 => mk S1 DL StD end.

(** Its mirror 0LB0RD_1LC1RB_1RB1LA_0LC1RD: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB0LD_1RC1LB_1LB1RA_0RC1LD : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S0 DR StD
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S1 DR StB | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S0 DL StC | StD, S1 => mk S1 DR StD end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_0RB0LD_1RC1LB_1LB1RA_0RC1LD : list Instr := [].
Definition tmw_0RB0LD_1RC1LB_1LB1RA_0RC1LD : TM := tm_wrap_trs tmm_0RB0LD_1RC1LB_1LB1RA_0RC1LD pins_0RB0LD_1RC1LB_1LB1RA_0RC1LD.
Local Notation tm := tmw_0RB0LD_1RC1LB_1LB1RA_0RC1LD.

Lemma mirror_ok_0RB0LD_1RC1LB_1LB1RA_0RC1LD : mirror_tm tm_0RB0LD_1RC1LB_1LB1RA_0RC1LD = tmm_0RB0LD_1RC1LB_1LB1RA_0RC1LD.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_0RB0LD_1RC1LB_1LB1RA_0RC1LD (p : positive) : cconf := (StD, (Jp p ++ [S0], S0, [])).
Local Notation Cc := Cc_0RB0LD_1RC1LB_1LB1RA_0RC1LD.

(** ** The certificate *)

Definition A0_0RB0LD_1RC1LB_1LB1RA_0RC1LD : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition A1_0RB0LD_1RC1LB_1LB1RA_0RC1LD : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chi_0RB0LD_1RC1LB_1LB1RA_0RC1LD : list lstep := [SRotL 1; SWin 1; SCycL 4 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_int_0RB0LD_1RC1LB_1LB1RA_0RC1LD : srun tm false true chi_0RB0LD_1RC1LB_1LB1RA_0RC1LD A0_0RB0LD_1RC1LB_1LB1RA_0RC1LD = Some (A1_0RB0LD_1RC1LB_1LB1RA_0RC1LD, 6, 4).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB0LD_1RC1LB_1LB1RA_0RC1LD : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_0RB0LD_1RC1LB_1LB1RA_0RC1LD : sconf := mkC StD (mkS [] [S1;S1] 1 1 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition cho_0RB0LD_1RC1LB_1LB1RA_0RC1LD : list lstep := [SRotL 1; SWin 1; SCycL 4 0; SWin 1; SWinL 9; SCycR 2; SWin 1; SRotL 1; SFoldL 1].

Lemma run_ovf_0RB0LD_1RC1LB_1LB1RA_0RC1LD : srun tm true true cho_0RB0LD_1RC1LB_1LB1RA_0RC1LD B0_0RB0LD_1RC1LB_1LB1RA_0RC1LD = Some (B1_0RB0LD_1RC1LB_1LB1RA_0RC1LD, 6, 12).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_0RB0LD_1RC1LB_1LB1RA_0RC1LD : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Jp q0 ++ [S0]) [] j A0_0RB0LD_1RC1LB_1LB1RA_0RC1LD.
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (H1 & _).
  unfold Cc_0RB0LD_1RC1LB_1LB1RA_0RC1LD, cden, A0_0RB0LD_1RC1LB_1LB1RA_0RC1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gei_0RB0LD_1RC1LB_1LB1RA_0RC1LD : forall p j q0, cview p = (j, Some q0) ->
  cden (Jp q0 ++ [S0]) [] j A1_0RB0LD_1RC1LB_1LB1RA_0RC1LD = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (_ & H2).
  unfold Cc_0RB0LD_1RC1LB_1LB1RA_0RC1LD, cden, A1_0RB0LD_1RC1LB_1LB1RA_0RC1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_0RB0LD_1RC1LB_1LB1RA_0RC1LD : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (6 * j + 4). split; [lia|].
  rewrite (gsi_0RB0LD_1RC1LB_1LB1RA_0RC1LD p j q0 E).
  rewrite (srun_sound tm false true chi_0RB0LD_1RC1LB_1LB1RA_0RC1LD A0_0RB0LD_1RC1LB_1LB1RA_0RC1LD A1_0RB0LD_1RC1LB_1LB1RA_0RC1LD 6 4
             run_int_0RB0LD_1RC1LB_1LB1RA_0RC1LD (Jp q0 ++ [S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_0RB0LD_1RC1LB_1LB1RA_0RC1LD p j q0 E).
Qed.

Lemma gso_0RB0LD_1RC1LB_1LB1RA_0RC1LD : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_0RB0LD_1RC1LB_1LB1RA_0RC1LD.
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (H1 & _).
  unfold Cc_0RB0LD_1RC1LB_1LB1RA_0RC1LD, cden, B0_0RB0LD_1RC1LB_1LB1RA_0RC1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_0RB0LD_1RC1LB_1LB1RA_0RC1LD : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_0RB0LD_1RC1LB_1LB1RA_0RC1LD : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB0LD_1RC1LB_1LB1RA_0RC1LD) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_0RB0LD_1RC1LB_1LB1RA_0RC1LD
             = (StD, (rep [S1;S1] (S j) ++ [S1;S0], S0, []))).
  { unfold cden, B1_0RB0LD_1RC1LB_1LB1RA_0RC1LD, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StD, (rep [S1;S1] (S j) ++ [S1;S0], S0, []))).
  { unfold Cc_0RB0LD_1RC1LB_1LB1RA_0RC1LD. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_0RB0LD_1RC1LB_1LB1RA_0RC1LD : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB0LD_1RC1LB_1LB1RA_0RC1LD p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_0RB0LD_1RC1LB_1LB1RA_0RC1LD B0_0RB0LD_1RC1LB_1LB1RA_0RC1LD B1_0RB0LD_1RC1LB_1LB1RA_0RC1LD 6 12 p j' [] []).
    + exact run_ovf_0RB0LD_1RC1LB_1LB1RA_0RC1LD.
    + reflexivity.
    + reflexivity.
    + exact (gso_0RB0LD_1RC1LB_1LB1RA_0RC1LD p j' E).
    + exact (geo_0RB0LD_1RC1LB_1LB1RA_0RC1LD p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_0RB0LD_1RC1LB_1LB1RA_0RC1LD : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 13.
  assert (H : match csteps tm 13 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 13 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_0RB0LD_1RC1LB_1LB1RA_0RC1LD : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_0RB0LD_1RC1LB_1LB1RA_0RC1LD = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_0RB0LD_1RC1LB_1LB1RA_0RC1LD p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB0LD_1RC1LB_1LB1RA_0RC1LD p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_0RB0LD_1RC1LB_1LB1RA_0RC1LD : forall t, ~ In t pins_0RB0LD_1RC1LB_1LB1RA_0RC1LD ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_0RB0LD_1RC1LB_1LB1RA_0RC1LD.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_via_ovf tm Cc Hi (StA, S0)), fireo_0RB0LD_1RC1LB_1LB1RA_0RC1LD
      with (l := [SRotL 1; SWin 1; SCycL 4 0; SWin 1]).
    vm_compute; reflexivity.
  - (* A1 *)
    apply (fire_via_ovf tm Cc Hi (StA, S1)), fireo_0RB0LD_1RC1LB_1LB1RA_0RC1LD
      with (l := [SRotL 1; SWin 1; SCycL 4 0; SWin 1; SWinL 6]).
    vm_compute; reflexivity.
  - (* B0 *)
    apply (fire_via_ovf tm Cc Hi (StB, S0)), fireo_0RB0LD_1RC1LB_1LB1RA_0RC1LD
      with (l := [SRotL 1; SWin 1; SCycL 4 0; SWin 1; SWinL 1]).
    vm_compute; reflexivity.
  - (* B1 *)
    apply (fire_via_ovf tm Cc Hi (StB, S1)), fireo_0RB0LD_1RC1LB_1LB1RA_0RC1LD
      with (l := [SRotL 1; SWin 1; SCycL 4 0; SWin 1; SWinL 3]).
    vm_compute; reflexivity.
  - (* C0 *)
    apply (fire_via_ovf tm Cc Hi (StC, S0)), fireo_0RB0LD_1RC1LB_1LB1RA_0RC1LD
      with (l := [SRotL 1; SWin 1; SCycL 4 0; SWin 1; SWinL 2]).
    vm_compute; reflexivity.
  - (* C1 *)
    apply (fire_via_ovf tm Cc Hi (StC, S1)), fireo_0RB0LD_1RC1LB_1LB1RA_0RC1LD
      with (l := [SRotL 1; SWin 1]).
    vm_compute; reflexivity.
  - (* D0 *)
    apply (fire_via_ovf tm Cc Hi (StD, S0)), fireo_0RB0LD_1RC1LB_1LB1RA_0RC1LD
      with (l := []).
    vm_compute; reflexivity.
  - (* D1 *)
    apply (fire_via_ovf tm Cc Hi (StD, S1)), fireo_0RB0LD_1RC1LB_1LB1RA_0RC1LD
      with (l := [SRotL 1; SWin 1; SCycL 4 0; SWin 1; SWinL 7]).
    vm_compute; reflexivity.
Qed.

Theorem nqhtrm_0RB0LD_1RC1LB_1LB1RA_0RC1LD : NeverQuasiHaltsTr tmm_0RB0LD_1RC1LB_1LB1RA_0RC1LD.
Proof.
  apply (glue_neverqhtr tmm_0RB0LD_1RC1LB_1LB1RA_0RC1LD pins_0RB0LD_1RC1LB_1LB1RA_0RC1LD Cc 1).
  - exact boot_0RB0LD_1RC1LB_1LB1RA_0RC1LD.
  - intros p _. apply lap_0RB0LD_1RC1LB_1LB1RA_0RC1LD.
  - intros t Ht p _. apply fire_0RB0LD_1RC1LB_1LB1RA_0RC1LD. exact Ht.
Qed.

Theorem nqhtr_0RB0LD_1RC1LB_1LB1RA_0RC1LD : NeverQuasiHaltsTr tm_0RB0LD_1RC1LB_1LB1RA_0RC1LD.
Proof. apply (neverqhtr_mirror tm_0RB0LD_1RC1LB_1LB1RA_0RC1LD). rewrite mirror_ok_0RB0LD_1RC1LB_1LB1RA_0RC1LD. exact nqhtrm_0RB0LD_1RC1LB_1LB1RA_0RC1LD. Qed.

Theorem nonhalt_0RB0LD_1RC1LB_1LB1RA_0RC1LD : NonHalt tm_0RB0LD_1RC1LB_1LB1RA_0RC1LD.
Proof. apply never_qh_tr_nonhalt, nqhtr_0RB0LD_1RC1LB_1LB1RA_0RC1LD. Qed.
