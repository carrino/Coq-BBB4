(** * LAPQ_0RB0LD_1LA1RC_1RB1RD_0RC0LD: TRANSITION-LEVEL QUASIHALTING-side board for machine 0RB0LD_1LA1RC_1RB1RD_0RC0LD, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Bp digit alphabet (BpCounter.v), anchored at

      Cc p = (StD, (Bp p ++ [S0], S0, [S1;S1;S1]))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  j=0: 4 ; j=S j': 4*j'+8 steps
      overflow  (cview p = (S j, None)):   4*j+8 steps

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
                                  MonoCounter JpCounter BpCounter LapCertGlue.
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

Definition mk_0RB0LD_1LA1RC_1RB1RD_0RC0LD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB0LD_1LA1RC_1RB1RD_0RC0LD.

(** 0RB0LD_1LA1RC_1RB1RD_0RC0LD *)
(** 0RB0LD_1LA1RC_1RB1RD_0RC0LD -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB0LD_1LA1RC_1RB1RD_0RC0LD : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S0 DL StD
  | StB, S0 => mk S1 DL StA | StB, S1 => mk S1 DR StC
  | StC, S0 => mk S1 DR StB | StC, S1 => mk S1 DR StD
  | StD, S0 => mk S0 DR StC | StD, S1 => mk S0 DL StD end.

(** Its mirror 0LB0RD_1RA1LC_1LB1LD_0LC0RD: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB0LD_1LA1RC_1RB1RD_0RC0LD : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S0 DR StD
  | StB, S0 => mk S1 DR StA | StB, S1 => mk S1 DL StC
  | StC, S0 => mk S1 DL StB | StC, S1 => mk S1 DL StD
  | StD, S0 => mk S0 DL StC | StD, S1 => mk S0 DR StD end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_0RB0LD_1LA1RC_1RB1RD_0RC0LD : list Instr := [(StA, S0); (StC, S1)].
Definition tmw_0RB0LD_1LA1RC_1RB1RD_0RC0LD : TM := tm_wrap_trs tmm_0RB0LD_1LA1RC_1RB1RD_0RC0LD pins_0RB0LD_1LA1RC_1RB1RD_0RC0LD.
Local Notation tm := tmw_0RB0LD_1LA1RC_1RB1RD_0RC0LD.

Lemma mirror_ok_0RB0LD_1LA1RC_1RB1RD_0RC0LD : mirror_tm tm_0RB0LD_1LA1RC_1RB1RD_0RC0LD = tmm_0RB0LD_1LA1RC_1RB1RD_0RC0LD.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_0RB0LD_1LA1RC_1RB1RD_0RC0LD (p : positive) : cconf := (StD, (Bp p ++ [S0], S0, [S1;S1;S1])).
Local Notation Cc := Cc_0RB0LD_1LA1RC_1RB1RD_0RC0LD.

(** ** The certificate *)

(** j = 0: the repeated block is absent, so the whole lap is concrete. *)
Definition Z0_0RB0LD_1LA1RC_1RB1RD_0RC0LD : sconf := mkC StD (mkS [S0;S0] [] 0 0 []) S0 (mkS [S1;S1;S1] [] 0 0 []).
Definition Z1_0RB0LD_1LA1RC_1RB1RD_0RC0LD : sconf := mkC StD (mkS [S0;S1] [] 0 0 []) S0 (mkS [S1;S1;S1] [] 0 0 []).
Definition chz_0RB0LD_1LA1RC_1RB1RD_0RC0LD : list lstep := [SWin 4].

Lemma run_z_0RB0LD_1LA1RC_1RB1RD_0RC0LD : srun tm false true chz_0RB0LD_1LA1RC_1RB1RD_0RC0LD Z0_0RB0LD_1LA1RC_1RB1RD_0RC0LD = Some (Z1_0RB0LD_1LA1RC_1RB1RD_0RC0LD, 0, 4).
Proof. vm_compute. reflexivity. Qed.

(** j = S j': one copy of the unit sits in the PREFIX, so the head always has
    a concrete cell to step onto. *)
Definition P0_0RB0LD_1LA1RC_1RB1RD_0RC0LD : sconf := mkC StD (mkS [S0;S1] [S0;S1] 1 0 [S0;S0]) S0 (mkS [S1;S1;S1] [] 0 0 []).
Definition P1_0RB0LD_1LA1RC_1RB1RD_0RC0LD : sconf := mkC StD (mkS [S0;S0] [S0;S0] 1 0 [S0;S1]) S0 (mkS [S1;S1;S1] [] 0 0 []).
Definition chp_0RB0LD_1LA1RC_1RB1RD_0RC0LD : list lstep := [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 2].

Lemma run_p_0RB0LD_1LA1RC_1RB1RD_0RC0LD : srun tm false true chp_0RB0LD_1LA1RC_1RB1RD_0RC0LD P0_0RB0LD_1LA1RC_1RB1RD_0RC0LD = Some (P1_0RB0LD_1LA1RC_1RB1RD_0RC0LD, 4, 8).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB0LD_1LA1RC_1RB1RD_0RC0LD : sconf := mkC StD (mkS [S0;S1] [S0;S1] 1 0 [S0]) S0 (mkS [S1;S1;S1] [] 0 0 []).
Definition B1_0RB0LD_1LA1RC_1RB1RD_0RC0LD : sconf := mkC StD (mkS [] [S0;S0] 1 1 [S0;S1]) S0 (mkS [S1;S1;S1] [] 0 0 []).
Definition cho_0RB0LD_1LA1RC_1RB1RD_0RC0LD : list lstep := [SWin 2; SCycL 2 0; SWin 1; SWinL 3; SCycR 2; SWin 2; SFoldL 1].

Lemma run_ovf_0RB0LD_1LA1RC_1RB1RD_0RC0LD : srun tm true true cho_0RB0LD_1LA1RC_1RB1RD_0RC0LD B0_0RB0LD_1LA1RC_1RB1RD_0RC0LD = Some (B1_0RB0LD_1LA1RC_1RB1RD_0RC0LD, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gz_0RB0LD_1LA1RC_1RB1RD_0RC0LD : forall p q0, cview p = (0, Some q0) ->
  Cc p = cden (Bp q0 ++ [S0]) [] 0 Z0_0RB0LD_1LA1RC_1RB1RD_0RC0LD /\
  cden (Bp q0 ++ [S0]) [] 0 Z1_0RB0LD_1LA1RC_1RB1RD_0RC0LD = Cc (Pos.succ p).
Proof.
  intros p q0 E. destruct (BpCounter.cview_some_B p 0 q0 E) as (H1 & H2).
  unfold Cc_0RB0LD_1LA1RC_1RB1RD_0RC0LD, cden, Z0_0RB0LD_1LA1RC_1RB1RD_0RC0LD, Z1_0RB0LD_1LA1RC_1RB1RD_0RC0LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gp_0RB0LD_1LA1RC_1RB1RD_0RC0LD : forall p j q0, cview p = (S j, Some q0) ->
  Cc p = cden (Bp q0 ++ [S0]) [] j P0_0RB0LD_1LA1RC_1RB1RD_0RC0LD /\
  cden (Bp q0 ++ [S0]) [] j P1_0RB0LD_1LA1RC_1RB1RD_0RC0LD = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (BpCounter.cview_some_B p (S j) q0 E) as (H1 & H2).
  unfold Cc_0RB0LD_1LA1RC_1RB1RD_0RC0LD, cden, P0_0RB0LD_1LA1RC_1RB1RD_0RC0LD, P1_0RB0LD_1LA1RC_1RB1RD_0RC0LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_0RB0LD_1LA1RC_1RB1RD_0RC0LD : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct j as [|j'].
  - destruct (gz_0RB0LD_1LA1RC_1RB1RD_0RC0LD p q0 E) as (HA & HB).
    exists (0 * 0 + 4). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chz_0RB0LD_1LA1RC_1RB1RD_0RC0LD Z0_0RB0LD_1LA1RC_1RB1RD_0RC0LD Z1_0RB0LD_1LA1RC_1RB1RD_0RC0LD 0 4
               run_z_0RB0LD_1LA1RC_1RB1RD_0RC0LD (Bp q0 ++ [S0]) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gp_0RB0LD_1LA1RC_1RB1RD_0RC0LD p j' q0 E) as (HA & HB).
    exists (4 * j' + 8). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chp_0RB0LD_1LA1RC_1RB1RD_0RC0LD P0_0RB0LD_1LA1RC_1RB1RD_0RC0LD P1_0RB0LD_1LA1RC_1RB1RD_0RC0LD 4 8
               run_p_0RB0LD_1LA1RC_1RB1RD_0RC0LD (Bp q0 ++ [S0]) [] j'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
Qed.

Lemma gso_0RB0LD_1LA1RC_1RB1RD_0RC0LD : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_0RB0LD_1LA1RC_1RB1RD_0RC0LD.
Proof.
  intros p j E. destruct (BpCounter.cview_none_B p j E) as (H1 & _).
  unfold Cc_0RB0LD_1LA1RC_1RB1RD_0RC0LD, cden, B0_0RB0LD_1LA1RC_1RB1RD_0RC0LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_0RB0LD_1LA1RC_1RB1RD_0RC0LD : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_0RB0LD_1LA1RC_1RB1RD_0RC0LD : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB0LD_1LA1RC_1RB1RD_0RC0LD) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (BpCounter.cview_none_B p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_0RB0LD_1LA1RC_1RB1RD_0RC0LD
             = (StD, (rep [S0;S0] (S j) ++ [S0;S1], S0, [S1;S1;S1]))).
  { unfold cden, B1_0RB0LD_1LA1RC_1RB1RD_0RC0LD, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StD, ((rep [S0;S0] (S j) ++ [S0;S1]) ++ [S0], S0, [S1;S1;S1]))).
  { unfold Cc_0RB0LD_1LA1RC_1RB1RD_0RC0LD. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_0RB0LD_1LA1RC_1RB1RD_0RC0LD. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_0RB0LD_1LA1RC_1RB1RD_0RC0LD : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB0LD_1LA1RC_1RB1RD_0RC0LD p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_0RB0LD_1LA1RC_1RB1RD_0RC0LD B0_0RB0LD_1LA1RC_1RB1RD_0RC0LD B1_0RB0LD_1LA1RC_1RB1RD_0RC0LD 4 8 p j' [] []).
    + exact run_ovf_0RB0LD_1LA1RC_1RB1RD_0RC0LD.
    + reflexivity.
    + reflexivity.
    + exact (gso_0RB0LD_1LA1RC_1RB1RD_0RC0LD p j' E).
    + exact (geo_0RB0LD_1LA1RC_1RB1RD_0RC0LD p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma bootq_0RB0LD_1LA1RC_1RB1RD_0RC0LD : stepn tmm_0RB0LD_1LA1RC_1RB1RD_0RC0LD 20 InitES = Some (lift (Cc 1)).
Proof.
  assert (H : match csteps tmm_0RB0LD_1LA1RC_1RB1RD_0RC0LD 20 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tmm_0RB0LD_1LA1RC_1RB1RD_0RC0LD 20 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** the quasihalt witness: a pinned instruction fired in the prefix *)
Lemma wit_0RB0LD_1LA1RC_1RB1RD_0RC0LD : existsb (fun tg => cfires tmm_0RB0LD_1LA1RC_1RB1RD_0RC0LD c0 20 tg) pins_0RB0LD_1LA1RC_1RB1RD_0RC0LD = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_0RB0LD_1LA1RC_1RB1RD_0RC0LD : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_0RB0LD_1LA1RC_1RB1RD_0RC0LD = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_0RB0LD_1LA1RC_1RB1RD_0RC0LD p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB0LD_1LA1RC_1RB1RD_0RC0LD p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_0RB0LD_1LA1RC_1RB1RD_0RC0LD : forall t, ~ In t pins_0RB0LD_1LA1RC_1RB1RD_0RC0LD ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_0RB0LD_1LA1RC_1RB1RD_0RC0LD.
  destruct t as [q b]; destruct q, b.
  - (* A0: pinned *)
    exfalso. apply Hnp. apply tr_inb_spec. reflexivity.
  - (* A1 *)
    apply (fire_via_ovf tm Cc Hi (StA, S1)), fireo_0RB0LD_1LA1RC_1RB1RD_0RC0LD
      with (l := [SWin 2; SCycL 2 0; SWin 1; SWinL 2]).
    vm_compute; reflexivity.
  - (* B0 *)
    apply (fire_via_ovf tm Cc Hi (StB, S0)), fireo_0RB0LD_1LA1RC_1RB1RD_0RC0LD
      with (l := [SWin 2; SCycL 2 0; SWin 1; SWinL 1]).
    vm_compute; reflexivity.
  - (* B1 *)
    apply (fire_via_ovf tm Cc Hi (StB, S1)), fireo_0RB0LD_1LA1RC_1RB1RD_0RC0LD
      with (l := [SWin 2]).
    vm_compute; reflexivity.
  - (* C0 *)
    apply (fire_via_ovf tm Cc Hi (StC, S0)), fireo_0RB0LD_1LA1RC_1RB1RD_0RC0LD
      with (l := [SWin 1]).
    vm_compute; reflexivity.
  - (* C1: pinned *)
    exfalso. apply Hnp. apply tr_inb_spec. reflexivity.
  - (* D0 *)
    apply (fire_via_ovf tm Cc Hi (StD, S0)), fireo_0RB0LD_1LA1RC_1RB1RD_0RC0LD
      with (l := []).
    vm_compute; reflexivity.
  - (* D1 *)
    apply (fire_via_ovf tm Cc Hi (StD, S1)), fireo_0RB0LD_1LA1RC_1RB1RD_0RC0LD
      with (l := [SWin 2; SCycL 2 0; SWin 1; SWinL 3]).
    vm_compute; reflexivity.
Qed.

Theorem qhtrm_0RB0LD_1LA1RC_1RB1RD_0RC0LD : NonHalt tmm_0RB0LD_1LA1RC_1RB1RD_0RC0LD /\ QHBoundTr 32779478 tmm_0RB0LD_1LA1RC_1RB1RD_0RC0LD /\ QuasiHaltsTr tmm_0RB0LD_1LA1RC_1RB1RD_0RC0LD.
Proof.
  apply (lap_qh_stage tmm_0RB0LD_1LA1RC_1RB1RD_0RC0LD pins_0RB0LD_1LA1RC_1RB1RD_0RC0LD Cc 1 20 32779478).
  - exact bootq_0RB0LD_1LA1RC_1RB1RD_0RC0LD.
  - intros p _. apply lap_0RB0LD_1LA1RC_1RB1RD_0RC0LD.
  - intros t Ht p _. apply fire_0RB0LD_1LA1RC_1RB1RD_0RC0LD. exact Ht.
  - exact wit_0RB0LD_1LA1RC_1RB1RD_0RC0LD.
  - vm_cast_no_check (eq_refl true).
Qed.

Theorem qhtr_0RB0LD_1LA1RC_1RB1RD_0RC0LD : NonHalt tm_0RB0LD_1LA1RC_1RB1RD_0RC0LD /\ QHBoundTr 32779478 tm_0RB0LD_1LA1RC_1RB1RD_0RC0LD /\ QuasiHaltsTr tm_0RB0LD_1LA1RC_1RB1RD_0RC0LD.
Proof. apply (qh_triple_unmirror 32779478 tm_0RB0LD_1LA1RC_1RB1RD_0RC0LD). rewrite mirror_ok_0RB0LD_1LA1RC_1RB1RD_0RC0LD. exact qhtrm_0RB0LD_1LA1RC_1RB1RD_0RC0LD. Qed.
