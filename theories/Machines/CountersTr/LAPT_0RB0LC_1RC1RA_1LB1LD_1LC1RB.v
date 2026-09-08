(** * LAPT_0RB0LC_1RC1RA_1LB1LD_1LC1RB: TRANSITION-LEVEL board for machine 0RB0LC_1RC1RA_1LB1LD_1LC1RB, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Jp digit alphabet (JpCounter.v), anchored at

      Cc p = (StA, (Jp p ++ [S0], S0, [S1;S1]))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  4*j+12 steps
      overflow  (cview p = (S j, None)):   4*j+18 steps

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

Definition mk_0RB0LC_1RC1RA_1LB1LD_1LC1RB (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB0LC_1RC1RA_1LB1LD_1LC1RB.

(** 0RB0LC_1RC1RA_1LB1LD_1LC1RB *)
(** 0RB0LC_1RC1RA_1LB1LD_1LC1RB -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB0LC_1RC1RA_1LB1LD_1LC1RB : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S0 DL StC
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DR StA
  | StC, S0 => mk S1 DL StB | StC, S1 => mk S1 DL StD
  | StD, S0 => mk S1 DL StC | StD, S1 => mk S1 DR StB end.

(** Its mirror 0LB0RC_1LC1LA_1RB1RD_1RC1LB: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB0LC_1RC1RA_1LB1LD_1LC1RB : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S0 DR StC
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DL StA
  | StC, S0 => mk S1 DR StB | StC, S1 => mk S1 DR StD
  | StD, S0 => mk S1 DR StC | StD, S1 => mk S1 DL StB end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_0RB0LC_1RC1RA_1LB1LD_1LC1RB : list Instr := [].
Definition tmw_0RB0LC_1RC1RA_1LB1LD_1LC1RB : TM := tm_wrap_trs tmm_0RB0LC_1RC1RA_1LB1LD_1LC1RB pins_0RB0LC_1RC1RA_1LB1LD_1LC1RB.
Local Notation tm := tmw_0RB0LC_1RC1RA_1LB1LD_1LC1RB.

Lemma mirror_ok_0RB0LC_1RC1RA_1LB1LD_1LC1RB : mirror_tm tm_0RB0LC_1RC1RA_1LB1LD_1LC1RB = tmm_0RB0LC_1RC1RA_1LB1LD_1LC1RB.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_0RB0LC_1RC1RA_1LB1LD_1LC1RB (p : positive) : cconf := (StA, (Jp p ++ [S0], S0, [S1;S1])).
Local Notation Cc := Cc_0RB0LC_1RC1RA_1LB1LD_1LC1RB.

(** ** The certificate *)

Definition A0_0RB0LC_1RC1RA_1LB1LD_1LC1RB : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1;S1] [] 0 0 []).
Definition A1_0RB0LC_1RC1RA_1LB1LD_1LC1RB : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S1;S1] [] 0 0 []).
Definition chi_0RB0LC_1RC1RA_1LB1LD_1LC1RB : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWin 8].

Lemma run_int_0RB0LC_1RC1RA_1LB1LD_1LC1RB : srun tm false true chi_0RB0LC_1RC1RA_1LB1LD_1LC1RB A0_0RB0LC_1RC1RA_1LB1LD_1LC1RB = Some (A1_0RB0LC_1RC1RA_1LB1LD_1LC1RB, 4, 12).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB0LC_1RC1RA_1LB1LD_1LC1RB : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S0]) S0 (mkS [S1;S1] [] 0 0 []).
Definition B1_0RB0LC_1RC1RA_1LB1LD_1LC1RB : sconf := mkC StA (mkS [] [S1;S1] 1 1 [S1;S0]) S0 (mkS [S1;S1] [] 0 0 []).
Definition cho_0RB0LC_1RC1RA_1LB1LD_1LC1RB : list lstep := [SCycL 2 0; SWin 2; SWinL 8; SCycR 2; SWin 8; SRotL 2; SFoldL 1].

Lemma run_ovf_0RB0LC_1RC1RA_1LB1LD_1LC1RB : srun tm true true cho_0RB0LC_1RC1RA_1LB1LD_1LC1RB B0_0RB0LC_1RC1RA_1LB1LD_1LC1RB = Some (B1_0RB0LC_1RC1RA_1LB1LD_1LC1RB, 4, 18).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_0RB0LC_1RC1RA_1LB1LD_1LC1RB : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Jp q0 ++ [S0]) [] j A0_0RB0LC_1RC1RA_1LB1LD_1LC1RB.
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (H1 & _).
  unfold Cc_0RB0LC_1RC1RA_1LB1LD_1LC1RB, cden, A0_0RB0LC_1RC1RA_1LB1LD_1LC1RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gei_0RB0LC_1RC1RA_1LB1LD_1LC1RB : forall p j q0, cview p = (j, Some q0) ->
  cden (Jp q0 ++ [S0]) [] j A1_0RB0LC_1RC1RA_1LB1LD_1LC1RB = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (_ & H2).
  unfold Cc_0RB0LC_1RC1RA_1LB1LD_1LC1RB, cden, A1_0RB0LC_1RC1RA_1LB1LD_1LC1RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_0RB0LC_1RC1RA_1LB1LD_1LC1RB : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (4 * j + 12). split; [lia|].
  rewrite (gsi_0RB0LC_1RC1RA_1LB1LD_1LC1RB p j q0 E).
  rewrite (srun_sound tm false true chi_0RB0LC_1RC1RA_1LB1LD_1LC1RB A0_0RB0LC_1RC1RA_1LB1LD_1LC1RB A1_0RB0LC_1RC1RA_1LB1LD_1LC1RB 4 12
             run_int_0RB0LC_1RC1RA_1LB1LD_1LC1RB (Jp q0 ++ [S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_0RB0LC_1RC1RA_1LB1LD_1LC1RB p j q0 E).
Qed.

Lemma gso_0RB0LC_1RC1RA_1LB1LD_1LC1RB : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_0RB0LC_1RC1RA_1LB1LD_1LC1RB.
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (H1 & _).
  unfold Cc_0RB0LC_1RC1RA_1LB1LD_1LC1RB, cden, B0_0RB0LC_1RC1RA_1LB1LD_1LC1RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_0RB0LC_1RC1RA_1LB1LD_1LC1RB : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_0RB0LC_1RC1RA_1LB1LD_1LC1RB : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB0LC_1RC1RA_1LB1LD_1LC1RB) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_0RB0LC_1RC1RA_1LB1LD_1LC1RB
             = (StA, (rep [S1;S1] (S j) ++ [S1;S0], S0, [S1;S1]))).
  { unfold cden, B1_0RB0LC_1RC1RA_1LB1LD_1LC1RB, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StA, (rep [S1;S1] (S j) ++ [S1;S0], S0, [S1;S1]))).
  { unfold Cc_0RB0LC_1RC1RA_1LB1LD_1LC1RB. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_0RB0LC_1RC1RA_1LB1LD_1LC1RB : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB0LC_1RC1RA_1LB1LD_1LC1RB p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_0RB0LC_1RC1RA_1LB1LD_1LC1RB B0_0RB0LC_1RC1RA_1LB1LD_1LC1RB B1_0RB0LC_1RC1RA_1LB1LD_1LC1RB 4 18 p j' [] []).
    + exact run_ovf_0RB0LC_1RC1RA_1LB1LD_1LC1RB.
    + reflexivity.
    + reflexivity.
    + exact (gso_0RB0LC_1RC1RA_1LB1LD_1LC1RB p j' E).
    + exact (geo_0RB0LC_1RC1RA_1LB1LD_1LC1RB p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_0RB0LC_1RC1RA_1LB1LD_1LC1RB : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 16.
  assert (H : match csteps tm 16 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 16 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_0RB0LC_1RC1RA_1LB1LD_1LC1RB : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_0RB0LC_1RC1RA_1LB1LD_1LC1RB = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_0RB0LC_1RC1RA_1LB1LD_1LC1RB p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB0LC_1RC1RA_1LB1LD_1LC1RB p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_0RB0LC_1RC1RA_1LB1LD_1LC1RB : forall t, ~ In t pins_0RB0LC_1RC1RA_1LB1LD_1LC1RB ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_0RB0LC_1RC1RA_1LB1LD_1LC1RB.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_via_ovf tm Cc Hi (StA, S0)), fireo_0RB0LC_1RC1RA_1LB1LD_1LC1RB
      with (l := []).
    vm_compute; reflexivity.
  - (* A1 *)
    apply (fire_via_ovf tm Cc Hi (StA, S1)), fireo_0RB0LC_1RC1RA_1LB1LD_1LC1RB
      with (l := [SCycL 2 0; SWin 2; SWinL 4]).
    vm_compute; reflexivity.
  - (* B0 *)
    apply (fire_via_ovf tm Cc Hi (StB, S0)), fireo_0RB0LC_1RC1RA_1LB1LD_1LC1RB
      with (l := [SCycL 2 0; SWin 2; SWinL 1]).
    vm_compute; reflexivity.
  - (* B1 *)
    apply (fire_via_ovf tm Cc Hi (StB, S1)), fireo_0RB0LC_1RC1RA_1LB1LD_1LC1RB
      with (l := [SCycL 2 0; SWin 1]).
    vm_compute; reflexivity.
  - (* C0 *)
    apply (fire_via_ovf tm Cc Hi (StC, S0)), fireo_0RB0LC_1RC1RA_1LB1LD_1LC1RB
      with (l := [SCycL 2 0; SWin 2; SWinL 2]).
    vm_compute; reflexivity.
  - (* C1 *)
    apply (fire_via_ovf tm Cc Hi (StC, S1)), fireo_0RB0LC_1RC1RA_1LB1LD_1LC1RB
      with (l := [SCycL 2 0; SWin 2; SWinL 5]).
    vm_compute; reflexivity.
  - (* D0 *)
    apply (fire_via_ovf tm Cc Hi (StD, S0)), fireo_0RB0LC_1RC1RA_1LB1LD_1LC1RB
      with (l := [SCycL 2 0; SWin 2; SWinL 6]).
    vm_compute; reflexivity.
  - (* D1 *)
    apply (fire_via_ovf tm Cc Hi (StD, S1)), fireo_0RB0LC_1RC1RA_1LB1LD_1LC1RB
      with (l := [SCycL 2 0; SWin 2; SWinL 8; SCycR 2; SWin 2]).
    vm_compute; reflexivity.
Qed.

Theorem nqhtrm_0RB0LC_1RC1RA_1LB1LD_1LC1RB : NeverQuasiHaltsTr tmm_0RB0LC_1RC1RA_1LB1LD_1LC1RB.
Proof.
  apply (glue_neverqhtr tmm_0RB0LC_1RC1RA_1LB1LD_1LC1RB pins_0RB0LC_1RC1RA_1LB1LD_1LC1RB Cc 1).
  - exact boot_0RB0LC_1RC1RA_1LB1LD_1LC1RB.
  - intros p _. apply lap_0RB0LC_1RC1RA_1LB1LD_1LC1RB.
  - intros t Ht p _. apply fire_0RB0LC_1RC1RA_1LB1LD_1LC1RB. exact Ht.
Qed.

Theorem nqhtr_0RB0LC_1RC1RA_1LB1LD_1LC1RB : NeverQuasiHaltsTr tm_0RB0LC_1RC1RA_1LB1LD_1LC1RB.
Proof. apply (neverqhtr_mirror tm_0RB0LC_1RC1RA_1LB1LD_1LC1RB). rewrite mirror_ok_0RB0LC_1RC1RA_1LB1LD_1LC1RB. exact nqhtrm_0RB0LC_1RC1RA_1LB1LD_1LC1RB. Qed.

Theorem nonhalt_0RB0LC_1RC1RA_1LB1LD_1LC1RB : NonHalt tm_0RB0LC_1RC1RA_1LB1LD_1LC1RB.
Proof. apply never_qh_tr_nonhalt, nqhtr_0RB0LC_1RC1RA_1LB1LD_1LC1RB. Qed.
