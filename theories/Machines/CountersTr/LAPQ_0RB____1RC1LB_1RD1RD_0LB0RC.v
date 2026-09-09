(** * LAPQ_0RB____1RC1LB_1RD1RD_0LB0RC: TRANSITION-LEVEL QUASIHALTING-side board for machine 0RB---_1RC1LB_1RD1RD_0LB0RC, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Ap_Alph_10_11_11 digit alphabet (Alph_10_11_11.v), anchored at

      Cc p = (StD, (Ap_Alph_10_11_11 p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  4*j+4 steps
      overflow  (cview p = (S j, None)):   4*j+7 steps

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 198 anchors.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter Alph_10_11_11 LapCertGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
From BBB4 Require Import BBBT4_Statement.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4 Require Import ClosureTr.
From BBB4.Counters Require Import LapGlueQHTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

Definition mk_0RB____1RC1LB_1RD1RD_0LB0RC (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB____1RC1LB_1RD1RD_0LB0RC.

(** 0RB---_1RC1LB_1RD1RD_0LB0RC *)
Definition tm_0RB____1RC1LB_1RD1RD_0LB0RC : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => None
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S1 DR StD
  | StD, S0 => mk S0 DL StB | StD, S1 => mk S0 DR StC end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_0RB____1RC1LB_1RD1RD_0LB0RC : list Instr := [(StA, S1); (StA, S0)].
Definition tmw_0RB____1RC1LB_1RD1RD_0LB0RC : TM := tm_wrap_trs tm_0RB____1RC1LB_1RD1RD_0LB0RC pins_0RB____1RC1LB_1RD1RD_0LB0RC.
Local Notation tm := tmw_0RB____1RC1LB_1RD1RD_0LB0RC.

Definition Cc_0RB____1RC1LB_1RD1RD_0LB0RC (p : positive) : cconf := (StD, (Ap_Alph_10_11_11 p ++ [S0], S0, [])).
Local Notation Cc := Cc_0RB____1RC1LB_1RD1RD_0LB0RC.

(** ** The certificate *)

Definition A0_0RB____1RC1LB_1RD1RD_0LB0RC : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition A1_0RB____1RC1LB_1RD1RD_0LB0RC : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chi_0RB____1RC1LB_1RD1RD_0LB0RC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_int_0RB____1RC1LB_1RD1RD_0LB0RC : srun tm false true chi_0RB____1RC1LB_1RD1RD_0LB0RC A0_0RB____1RC1LB_1RD1RD_0LB0RC = Some (A1_0RB____1RC1LB_1RD1RD_0LB0RC, 4, 4).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB____1RC1LB_1RD1RD_0LB0RC : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_0RB____1RC1LB_1RD1RD_0LB0RC : sconf := mkC StD (mkS [] [S1;S0] 1 1 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition cho_0RB____1RC1LB_1RD1RD_0LB0RC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 4; SCycR 2; SWin 1; SWinR 1; SFoldL 1].

Lemma run_ovf_0RB____1RC1LB_1RD1RD_0LB0RC : srun tm true true cho_0RB____1RC1LB_1RD1RD_0LB0RC B0_0RB____1RC1LB_1RD1RD_0LB0RC = Some (B1_0RB____1RC1LB_1RD1RD_0LB0RC, 4, 7).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_0RB____1RC1LB_1RD1RD_0LB0RC : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Ap_Alph_10_11_11 q0 ++ [S0]) [] j A0_0RB____1RC1LB_1RD1RD_0LB0RC.
Proof.
  intros p j q0 E. destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (H1 & _).
  unfold Cc_0RB____1RC1LB_1RD1RD_0LB0RC, cden, A0_0RB____1RC1LB_1RD1RD_0LB0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gei_0RB____1RC1LB_1RD1RD_0LB0RC : forall p j q0, cview p = (j, Some q0) ->
  cden (Ap_Alph_10_11_11 q0 ++ [S0]) [] j A1_0RB____1RC1LB_1RD1RD_0LB0RC = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (_ & H2).
  unfold Cc_0RB____1RC1LB_1RD1RD_0LB0RC, cden, A1_0RB____1RC1LB_1RD1RD_0LB0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_0RB____1RC1LB_1RD1RD_0LB0RC : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (4 * j + 4). split; [lia|].
  rewrite (gsi_0RB____1RC1LB_1RD1RD_0LB0RC p j q0 E).
  rewrite (srun_sound tm false true chi_0RB____1RC1LB_1RD1RD_0LB0RC A0_0RB____1RC1LB_1RD1RD_0LB0RC A1_0RB____1RC1LB_1RD1RD_0LB0RC 4 4
             run_int_0RB____1RC1LB_1RD1RD_0LB0RC (Ap_Alph_10_11_11 q0 ++ [S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_0RB____1RC1LB_1RD1RD_0LB0RC p j q0 E).
Qed.

Lemma gso_0RB____1RC1LB_1RD1RD_0LB0RC : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_0RB____1RC1LB_1RD1RD_0LB0RC.
Proof.
  intros p j E. destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p j E) as (H1 & _).
  unfold Cc_0RB____1RC1LB_1RD1RD_0LB0RC, cden, B0_0RB____1RC1LB_1RD1RD_0LB0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_0RB____1RC1LB_1RD1RD_0LB0RC : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_0RB____1RC1LB_1RD1RD_0LB0RC : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB____1RC1LB_1RD1RD_0LB0RC) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_0RB____1RC1LB_1RD1RD_0LB0RC
             = (StD, (rep [S1;S0] (S j) ++ [S1;S1], S0, []))).
  { unfold cden, B1_0RB____1RC1LB_1RD1RD_0LB0RC, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StD, ((rep [S1;S0] (S j) ++ [S1;S1]) ++ [S0], S0, []))).
  { unfold Cc_0RB____1RC1LB_1RD1RD_0LB0RC. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_0RB____1RC1LB_1RD1RD_0LB0RC. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_0RB____1RC1LB_1RD1RD_0LB0RC : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB____1RC1LB_1RD1RD_0LB0RC p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_0RB____1RC1LB_1RD1RD_0LB0RC B0_0RB____1RC1LB_1RD1RD_0LB0RC B1_0RB____1RC1LB_1RD1RD_0LB0RC 4 7 p j' [] []).
    + exact run_ovf_0RB____1RC1LB_1RD1RD_0LB0RC.
    + reflexivity.
    + reflexivity.
    + exact (gso_0RB____1RC1LB_1RD1RD_0LB0RC p j' E).
    + exact (geo_0RB____1RC1LB_1RD1RD_0LB0RC p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma bootq_0RB____1RC1LB_1RD1RD_0LB0RC : stepn tm_0RB____1RC1LB_1RD1RD_0LB0RC 3 InitES = Some (lift (Cc 1)).
Proof.
  assert (H : match csteps tm_0RB____1RC1LB_1RD1RD_0LB0RC 3 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm_0RB____1RC1LB_1RD1RD_0LB0RC 3 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** the quasihalt witness: a pinned instruction fired in the prefix *)
Lemma wit_0RB____1RC1LB_1RD1RD_0LB0RC : existsb (fun tg => cfires tm_0RB____1RC1LB_1RD1RD_0LB0RC c0 3 tg) pins_0RB____1RC1LB_1RD1RD_0LB0RC = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_0RB____1RC1LB_1RD1RD_0LB0RC : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_0RB____1RC1LB_1RD1RD_0LB0RC = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_0RB____1RC1LB_1RD1RD_0LB0RC p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB____1RC1LB_1RD1RD_0LB0RC p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_0RB____1RC1LB_1RD1RD_0LB0RC : forall t, ~ In t pins_0RB____1RC1LB_1RD1RD_0LB0RC ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_0RB____1RC1LB_1RD1RD_0LB0RC.
  destruct t as [q b]; destruct q, b.
  - (* A0: pinned *)
    exfalso. apply Hnp. apply tr_inb_spec. reflexivity.
  - (* A1: pinned *)
    exfalso. apply Hnp. apply tr_inb_spec. reflexivity.
  - (* B0 *)
    apply (fire_via_ovf tm Cc Hi (StB, S0)), fireo_0RB____1RC1LB_1RD1RD_0LB0RC
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 2]).
    vm_compute; reflexivity.
  - (* B1 *)
    apply (fire_via_ovf tm Cc Hi (StB, S1)), fireo_0RB____1RC1LB_1RD1RD_0LB0RC
      with (l := [SRotL 1; SWin 1]).
    vm_compute; reflexivity.
  - (* C0 *)
    apply (fire_via_ovf tm Cc Hi (StC, S0)), fireo_0RB____1RC1LB_1RD1RD_0LB0RC
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 4; SCycR 2; SWin 1]).
    vm_compute; reflexivity.
  - (* C1 *)
    apply (fire_via_ovf tm Cc Hi (StC, S1)), fireo_0RB____1RC1LB_1RD1RD_0LB0RC
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 3]).
    vm_compute; reflexivity.
  - (* D0 *)
    apply (fire_via_ovf tm Cc Hi (StD, S0)), fireo_0RB____1RC1LB_1RD1RD_0LB0RC
      with (l := []).
    vm_compute; reflexivity.
  - (* D1 *)
    apply (fire_via_ovf tm Cc Hi (StD, S1)), fireo_0RB____1RC1LB_1RD1RD_0LB0RC
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 4]).
    vm_compute; reflexivity.
Qed.

Theorem qhtr_0RB____1RC1LB_1RD1RD_0LB0RC : NonHalt tm_0RB____1RC1LB_1RD1RD_0LB0RC /\ QHBoundTr 32779478 tm_0RB____1RC1LB_1RD1RD_0LB0RC /\ QuasiHaltsTr tm_0RB____1RC1LB_1RD1RD_0LB0RC.
Proof.
  apply (lap_qh_stage tm_0RB____1RC1LB_1RD1RD_0LB0RC pins_0RB____1RC1LB_1RD1RD_0LB0RC Cc 1 3 32779478).
  - exact bootq_0RB____1RC1LB_1RD1RD_0LB0RC.
  - intros p _. apply lap_0RB____1RC1LB_1RD1RD_0LB0RC.
  - intros t Ht p _. apply fire_0RB____1RC1LB_1RD1RD_0LB0RC. exact Ht.
  - exact wit_0RB____1RC1LB_1RD1RD_0LB0RC.
  - vm_cast_no_check (eq_refl true).
Qed.
