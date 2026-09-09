(** * LAPQ_0RB0LA_1LC1RB_0LD0LA_1RD1RA: TRANSITION-LEVEL QUASIHALTING-side board for machine 0RB0LA_1LC1RB_0LD0LA_1RD1RA, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Kp digit alphabet (KpCounter.v), anchored at

      Cc p = (StB, (Kp p ++ [S0], S0, [S0;S1;S1;S1]))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  j=0: 8 ; j=S j': 2*j'+10 steps
      overflow  (cview p = (S j, None)):   2*j+10 steps

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
                                  MonoCounter JpCounter KpCounter LapCertGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
From BBB4 Require Import BBBT4_Statement.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr.
From BBB4 Require Import ClosureTr.
From BBB4.Counters Require Import LapGlueQHTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

Definition mk_0RB0LA_1LC1RB_0LD0LA_1RD1RA (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB0LA_1LC1RB_0LD0LA_1RD1RA.

(** 0RB0LA_1LC1RB_0LD0LA_1RD1RA *)
(** 0RB0LA_1LC1RB_0LD0LA_1RD1RA -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB0LA_1LC1RB_0LD0LA_1RD1RA : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S0 DL StA
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S0 DL StD | StC, S1 => mk S0 DL StA
  | StD, S0 => mk S1 DR StD | StD, S1 => mk S1 DR StA end.

(** Its mirror 0LB0RA_1RC1LB_0RD0RA_1LD1LA: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB0LA_1LC1RB_0LD0LA_1RD1RA : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S0 DR StA
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S0 DR StD | StC, S1 => mk S0 DR StA
  | StD, S0 => mk S1 DL StD | StD, S1 => mk S1 DL StA end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_0RB0LA_1LC1RB_0LD0LA_1RD1RA : list Instr := [(StD, S0)].
Definition tmw_0RB0LA_1LC1RB_0LD0LA_1RD1RA : TM := tm_wrap_trs tmm_0RB0LA_1LC1RB_0LD0LA_1RD1RA pins_0RB0LA_1LC1RB_0LD0LA_1RD1RA.
Local Notation tm := tmw_0RB0LA_1LC1RB_0LD0LA_1RD1RA.

Lemma mirror_ok_0RB0LA_1LC1RB_0LD0LA_1RD1RA : mirror_tm tm_0RB0LA_1LC1RB_0LD0LA_1RD1RA = tmm_0RB0LA_1LC1RB_0LD0LA_1RD1RA.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_0RB0LA_1LC1RB_0LD0LA_1RD1RA (p : positive) : cconf := (StB, (Kp p ++ [S0], S0, [S0;S1;S1;S1])).
Local Notation Cc := Cc_0RB0LA_1LC1RB_0LD0LA_1RD1RA.

(** ** The certificate *)

(** j = 0: the repeated block is absent, so the whole lap is concrete. *)
Definition Z0_0RB0LA_1LC1RB_0LD0LA_1RD1RA : sconf := mkC StB (mkS [S0] [] 0 0 []) S0 (mkS [S0;S1;S1;S1] [] 0 0 []).
Definition Z1_0RB0LA_1LC1RB_0LD0LA_1RD1RA : sconf := mkC StB (mkS [S1] [] 0 0 []) S0 (mkS [S0;S1;S1;S1] [] 0 0 []).
Definition chz_0RB0LA_1LC1RB_0LD0LA_1RD1RA : list lstep := [SWin 8].

Lemma run_z_0RB0LA_1LC1RB_0LD0LA_1RD1RA : srun tm false true chz_0RB0LA_1LC1RB_0LD0LA_1RD1RA Z0_0RB0LA_1LC1RB_0LD0LA_1RD1RA = Some (Z1_0RB0LA_1LC1RB_0LD0LA_1RD1RA, 0, 8).
Proof. vm_compute. reflexivity. Qed.

(** j = S j': one copy of the unit sits in the PREFIX, so the head always has
    a concrete cell to step onto. *)
Definition P0_0RB0LA_1LC1RB_0LD0LA_1RD1RA : sconf := mkC StB (mkS [S1] [S1] 1 0 [S0]) S0 (mkS [S0;S1;S1;S1] [] 0 0 []).
Definition P1_0RB0LA_1LC1RB_0LD0LA_1RD1RA : sconf := mkC StB (mkS [S0] [S0] 1 0 [S1]) S0 (mkS [S0;S1;S1;S1] [] 0 0 []).
Definition chp_0RB0LA_1LC1RB_0LD0LA_1RD1RA : list lstep := [SWin 5; SCycL 1 0; SWin 2; SRotR 1; SWin 1; SCycR 1; SWin 2; SRotL 1].

Lemma run_p_0RB0LA_1LC1RB_0LD0LA_1RD1RA : srun tm false true chp_0RB0LA_1LC1RB_0LD0LA_1RD1RA P0_0RB0LA_1LC1RB_0LD0LA_1RD1RA = Some (P1_0RB0LA_1LC1RB_0LD0LA_1RD1RA, 2, 10).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB0LA_1LC1RB_0LD0LA_1RD1RA : sconf := mkC StB (mkS [S1] [S1] 1 0 [S0]) S0 (mkS [S0;S1;S1;S1] [] 0 0 []).
Definition B1_0RB0LA_1LC1RB_0LD0LA_1RD1RA : sconf := mkC StB (mkS [] [S0] 1 1 [S1]) S0 (mkS [S0;S1;S1;S1] [] 0 0 []).
Definition cho_0RB0LA_1LC1RB_0LD0LA_1RD1RA : list lstep := [SWin 5; SCycL 1 0; SWin 2; SRotR 1; SWin 1; SCycR 1; SWin 2; SRotL 1; SFoldL 1].

Lemma run_ovf_0RB0LA_1LC1RB_0LD0LA_1RD1RA : srun tm true true cho_0RB0LA_1LC1RB_0LD0LA_1RD1RA B0_0RB0LA_1LC1RB_0LD0LA_1RD1RA = Some (B1_0RB0LA_1LC1RB_0LD0LA_1RD1RA, 2, 10).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gz_0RB0LA_1LC1RB_0LD0LA_1RD1RA : forall p q0, cview p = (0, Some q0) ->
  Cc p = cden (Kp q0 ++ [S0]) [] 0 Z0_0RB0LA_1LC1RB_0LD0LA_1RD1RA /\
  cden (Kp q0 ++ [S0]) [] 0 Z1_0RB0LA_1LC1RB_0LD0LA_1RD1RA = Cc (Pos.succ p).
Proof.
  intros p q0 E. destruct (KpCounter.cview_some_K p 0 q0 E) as (H1 & H2).
  unfold Cc_0RB0LA_1LC1RB_0LD0LA_1RD1RA, cden, Z0_0RB0LA_1LC1RB_0LD0LA_1RD1RA, Z1_0RB0LA_1LC1RB_0LD0LA_1RD1RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gp_0RB0LA_1LC1RB_0LD0LA_1RD1RA : forall p j q0, cview p = (S j, Some q0) ->
  Cc p = cden (Kp q0 ++ [S0]) [] j P0_0RB0LA_1LC1RB_0LD0LA_1RD1RA /\
  cden (Kp q0 ++ [S0]) [] j P1_0RB0LA_1LC1RB_0LD0LA_1RD1RA = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (KpCounter.cview_some_K p (S j) q0 E) as (H1 & H2).
  unfold Cc_0RB0LA_1LC1RB_0LD0LA_1RD1RA, cden, P0_0RB0LA_1LC1RB_0LD0LA_1RD1RA, P1_0RB0LA_1LC1RB_0LD0LA_1RD1RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_0RB0LA_1LC1RB_0LD0LA_1RD1RA : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct j as [|j'].
  - destruct (gz_0RB0LA_1LC1RB_0LD0LA_1RD1RA p q0 E) as (HA & HB).
    exists (0 * 0 + 8). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chz_0RB0LA_1LC1RB_0LD0LA_1RD1RA Z0_0RB0LA_1LC1RB_0LD0LA_1RD1RA Z1_0RB0LA_1LC1RB_0LD0LA_1RD1RA 0 8
               run_z_0RB0LA_1LC1RB_0LD0LA_1RD1RA (Kp q0 ++ [S0]) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gp_0RB0LA_1LC1RB_0LD0LA_1RD1RA p j' q0 E) as (HA & HB).
    exists (2 * j' + 10). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chp_0RB0LA_1LC1RB_0LD0LA_1RD1RA P0_0RB0LA_1LC1RB_0LD0LA_1RD1RA P1_0RB0LA_1LC1RB_0LD0LA_1RD1RA 2 10
               run_p_0RB0LA_1LC1RB_0LD0LA_1RD1RA (Kp q0 ++ [S0]) [] j'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
Qed.

Lemma gso_0RB0LA_1LC1RB_0LD0LA_1RD1RA : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_0RB0LA_1LC1RB_0LD0LA_1RD1RA.
Proof.
  intros p j E. destruct (KpCounter.cview_none_K p j E) as (H1 & _).
  unfold Cc_0RB0LA_1LC1RB_0LD0LA_1RD1RA, cden, B0_0RB0LA_1LC1RB_0LD0LA_1RD1RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_0RB0LA_1LC1RB_0LD0LA_1RD1RA : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_0RB0LA_1LC1RB_0LD0LA_1RD1RA : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB0LA_1LC1RB_0LD0LA_1RD1RA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (KpCounter.cview_none_K p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_0RB0LA_1LC1RB_0LD0LA_1RD1RA
             = (StB, (rep [S0] (S j) ++ [S1], S0, [S0;S1;S1;S1]))).
  { unfold cden, B1_0RB0LA_1LC1RB_0LD0LA_1RD1RA, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StB, ((rep [S0] (S j) ++ [S1]) ++ [S0], S0, [S0;S1;S1;S1]))).
  { unfold Cc_0RB0LA_1LC1RB_0LD0LA_1RD1RA. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_0RB0LA_1LC1RB_0LD0LA_1RD1RA. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_0RB0LA_1LC1RB_0LD0LA_1RD1RA : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB0LA_1LC1RB_0LD0LA_1RD1RA p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_0RB0LA_1LC1RB_0LD0LA_1RD1RA B0_0RB0LA_1LC1RB_0LD0LA_1RD1RA B1_0RB0LA_1LC1RB_0LD0LA_1RD1RA 2 10 p j' [] []).
    + exact run_ovf_0RB0LA_1LC1RB_0LD0LA_1RD1RA.
    + reflexivity.
    + reflexivity.
    + exact (gso_0RB0LA_1LC1RB_0LD0LA_1RD1RA p j' E).
    + exact (geo_0RB0LA_1LC1RB_0LD0LA_1RD1RA p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma bootq_0RB0LA_1LC1RB_0LD0LA_1RD1RA : stepn tmm_0RB0LA_1LC1RB_0LD0LA_1RD1RA 15 InitES = Some (lift (Cc 1)).
Proof.
  assert (H : match csteps tmm_0RB0LA_1LC1RB_0LD0LA_1RD1RA 15 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tmm_0RB0LA_1LC1RB_0LD0LA_1RD1RA 15 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** the quasihalt witness: a pinned instruction fired in the prefix *)
Lemma wit_0RB0LA_1LC1RB_0LD0LA_1RD1RA : existsb (fun tg => cfires tmm_0RB0LA_1LC1RB_0LD0LA_1RD1RA c0 15 tg) pins_0RB0LA_1LC1RB_0LD0LA_1RD1RA = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_0RB0LA_1LC1RB_0LD0LA_1RD1RA : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_0RB0LA_1LC1RB_0LD0LA_1RD1RA = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_0RB0LA_1LC1RB_0LD0LA_1RD1RA p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB0LA_1LC1RB_0LD0LA_1RD1RA p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_0RB0LA_1LC1RB_0LD0LA_1RD1RA : forall t, ~ In t pins_0RB0LA_1LC1RB_0LD0LA_1RD1RA ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_0RB0LA_1LC1RB_0LD0LA_1RD1RA.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_via_ovf tm Cc Hi (StA, S0)), fireo_0RB0LA_1LC1RB_0LD0LA_1RD1RA
      with (l := [SWin 3]).
    vm_compute; reflexivity.
  - (* A1 *)
    apply (fire_via_ovf tm Cc Hi (StA, S1)), fireo_0RB0LA_1LC1RB_0LD0LA_1RD1RA
      with (l := [SWin 5; SCycL 1 0; SWin 2; SRotR 1; SWin 1]).
    vm_compute; reflexivity.
  - (* B0 *)
    apply (fire_via_ovf tm Cc Hi (StB, S0)), fireo_0RB0LA_1LC1RB_0LD0LA_1RD1RA
      with (l := []).
    vm_compute; reflexivity.
  - (* B1 *)
    apply (fire_via_ovf tm Cc Hi (StB, S1)), fireo_0RB0LA_1LC1RB_0LD0LA_1RD1RA
      with (l := [SWin 4]).
    vm_compute; reflexivity.
  - (* C0 *)
    apply (fire_via_ovf tm Cc Hi (StC, S0)), fireo_0RB0LA_1LC1RB_0LD0LA_1RD1RA
      with (l := [SWin 1]).
    vm_compute; reflexivity.
  - (* C1 *)
    apply (fire_via_ovf tm Cc Hi (StC, S1)), fireo_0RB0LA_1LC1RB_0LD0LA_1RD1RA
      with (l := [SWin 5; SCycL 1 0; SWin 2]).
    vm_compute; reflexivity.
  - (* D0: pinned *)
    exfalso. apply Hnp. apply tr_inb_spec. reflexivity.
  - (* D1 *)
    apply (fire_via_ovf tm Cc Hi (StD, S1)), fireo_0RB0LA_1LC1RB_0LD0LA_1RD1RA
      with (l := [SWin 2]).
    vm_compute; reflexivity.
Qed.

Theorem qhtrm_0RB0LA_1LC1RB_0LD0LA_1RD1RA : NonHalt tmm_0RB0LA_1LC1RB_0LD0LA_1RD1RA /\ QHBoundTr 32779478 tmm_0RB0LA_1LC1RB_0LD0LA_1RD1RA /\ QuasiHaltsTr tmm_0RB0LA_1LC1RB_0LD0LA_1RD1RA.
Proof.
  apply (lap_qh_stage tmm_0RB0LA_1LC1RB_0LD0LA_1RD1RA pins_0RB0LA_1LC1RB_0LD0LA_1RD1RA Cc 1 15 32779478).
  - exact bootq_0RB0LA_1LC1RB_0LD0LA_1RD1RA.
  - intros p _. apply lap_0RB0LA_1LC1RB_0LD0LA_1RD1RA.
  - intros t Ht p _. apply fire_0RB0LA_1LC1RB_0LD0LA_1RD1RA. exact Ht.
  - exact wit_0RB0LA_1LC1RB_0LD0LA_1RD1RA.
  - vm_cast_no_check (eq_refl true).
Qed.

Theorem qhtr_0RB0LA_1LC1RB_0LD0LA_1RD1RA : NonHalt tm_0RB0LA_1LC1RB_0LD0LA_1RD1RA /\ QHBoundTr 32779478 tm_0RB0LA_1LC1RB_0LD0LA_1RD1RA /\ QuasiHaltsTr tm_0RB0LA_1LC1RB_0LD0LA_1RD1RA.
Proof. apply (qh_triple_unmirror 32779478 tm_0RB0LA_1LC1RB_0LD0LA_1RD1RA). rewrite mirror_ok_0RB0LA_1LC1RB_0LD0LA_1RD1RA. exact qhtrm_0RB0LA_1LC1RB_0LD0LA_1RD1RA. Qed.
