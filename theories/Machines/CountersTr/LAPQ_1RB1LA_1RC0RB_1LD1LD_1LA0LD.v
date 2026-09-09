(** * LAPQ_1RB1LA_1RC0RB_1LD1LD_1LA0LD: TRANSITION-LEVEL QUASIHALTING-side board for machine 1RB1LA_1RC0RB_1LD1LD_1LA0LD, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Kp digit alphabet (KpCounter.v), anchored at

      Cc p = (StD, (Kp p ++ [S0], S0, [S0;S1;S1]))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  j=0: 6 ; j=S j': 2*j'+8 steps
      overflow  (cview p = (S j, None)):   2*j+8 steps

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 198 anchors.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter KpCounter LapCertGlue.
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

Definition mk_1RB1LA_1RC0RB_1LD1LD_1LA0LD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1LA_1RC0RB_1LD1LD_1LA0LD.

(** 1RB1LA_1RC0RB_1LD1LD_1LA0LD *)
Definition tm_1RB1LA_1RC0RB_1LD1LD_1LA0LD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StA
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S0 DR StB
  | StC, S0 => mk S1 DL StD | StC, S1 => mk S1 DL StD
  | StD, S0 => mk S1 DL StA | StD, S1 => mk S0 DL StD end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_1RB1LA_1RC0RB_1LD1LD_1LA0LD : list Instr := [(StC, S0)].
Definition tmw_1RB1LA_1RC0RB_1LD1LD_1LA0LD : TM := tm_wrap_trs tm_1RB1LA_1RC0RB_1LD1LD_1LA0LD pins_1RB1LA_1RC0RB_1LD1LD_1LA0LD.
Local Notation tm := tmw_1RB1LA_1RC0RB_1LD1LD_1LA0LD.

Definition Cc_1RB1LA_1RC0RB_1LD1LD_1LA0LD (p : positive) : cconf := (StD, (Kp p ++ [S0], S0, [S0;S1;S1])).
Local Notation Cc := Cc_1RB1LA_1RC0RB_1LD1LD_1LA0LD.

(** ** The certificate *)

(** j = 0: the repeated block is absent, so the whole lap is concrete. *)
Definition Z0_1RB1LA_1RC0RB_1LD1LD_1LA0LD : sconf := mkC StD (mkS [S0] [] 0 0 []) S0 (mkS [S0;S1;S1] [] 0 0 []).
Definition Z1_1RB1LA_1RC0RB_1LD1LD_1LA0LD : sconf := mkC StD (mkS [S1] [] 0 0 []) S0 (mkS [S0;S1;S1] [] 0 0 []).
Definition chz_1RB1LA_1RC0RB_1LD1LD_1LA0LD : list lstep := [SWin 6].

Lemma run_z_1RB1LA_1RC0RB_1LD1LD_1LA0LD : srun tm false true chz_1RB1LA_1RC0RB_1LD1LD_1LA0LD Z0_1RB1LA_1RC0RB_1LD1LD_1LA0LD = Some (Z1_1RB1LA_1RC0RB_1LD1LD_1LA0LD, 0, 6).
Proof. vm_compute. reflexivity. Qed.

(** j = S j': one copy of the unit sits in the PREFIX, so the head always has
    a concrete cell to step onto. *)
Definition P0_1RB1LA_1RC0RB_1LD1LD_1LA0LD : sconf := mkC StD (mkS [S1] [S1] 1 0 [S0]) S0 (mkS [S0;S1;S1] [] 0 0 []).
Definition P1_1RB1LA_1RC0RB_1LD1LD_1LA0LD : sconf := mkC StD (mkS [S0] [S0] 1 0 [S1]) S0 (mkS [S0;S1;S1] [] 0 0 []).
Definition chp_1RB1LA_1RC0RB_1LD1LD_1LA0LD : list lstep := [SWin 1; SCycL 1 0; SWin 2; SCycR 1; SWin 5].

Lemma run_p_1RB1LA_1RC0RB_1LD1LD_1LA0LD : srun tm false true chp_1RB1LA_1RC0RB_1LD1LD_1LA0LD P0_1RB1LA_1RC0RB_1LD1LD_1LA0LD = Some (P1_1RB1LA_1RC0RB_1LD1LD_1LA0LD, 2, 8).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB1LA_1RC0RB_1LD1LD_1LA0LD : sconf := mkC StD (mkS [S1] [S1] 1 0 [S0]) S0 (mkS [S0;S1;S1] [] 0 0 []).
Definition B1_1RB1LA_1RC0RB_1LD1LD_1LA0LD : sconf := mkC StD (mkS [] [S0] 1 1 [S1]) S0 (mkS [S0;S1;S1] [] 0 0 []).
Definition cho_1RB1LA_1RC0RB_1LD1LD_1LA0LD : list lstep := [SWin 1; SCycL 1 0; SWin 2; SCycR 1; SWin 5; SFoldL 1].

Lemma run_ovf_1RB1LA_1RC0RB_1LD1LD_1LA0LD : srun tm true true cho_1RB1LA_1RC0RB_1LD1LD_1LA0LD B0_1RB1LA_1RC0RB_1LD1LD_1LA0LD = Some (B1_1RB1LA_1RC0RB_1LD1LD_1LA0LD, 2, 8).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gz_1RB1LA_1RC0RB_1LD1LD_1LA0LD : forall p q0, cview p = (0, Some q0) ->
  Cc p = cden (Kp q0 ++ [S0]) [] 0 Z0_1RB1LA_1RC0RB_1LD1LD_1LA0LD /\
  cden (Kp q0 ++ [S0]) [] 0 Z1_1RB1LA_1RC0RB_1LD1LD_1LA0LD = Cc (Pos.succ p).
Proof.
  intros p q0 E. destruct (KpCounter.cview_some_K p 0 q0 E) as (H1 & H2).
  unfold Cc_1RB1LA_1RC0RB_1LD1LD_1LA0LD, cden, Z0_1RB1LA_1RC0RB_1LD1LD_1LA0LD, Z1_1RB1LA_1RC0RB_1LD1LD_1LA0LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gp_1RB1LA_1RC0RB_1LD1LD_1LA0LD : forall p j q0, cview p = (S j, Some q0) ->
  Cc p = cden (Kp q0 ++ [S0]) [] j P0_1RB1LA_1RC0RB_1LD1LD_1LA0LD /\
  cden (Kp q0 ++ [S0]) [] j P1_1RB1LA_1RC0RB_1LD1LD_1LA0LD = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (KpCounter.cview_some_K p (S j) q0 E) as (H1 & H2).
  unfold Cc_1RB1LA_1RC0RB_1LD1LD_1LA0LD, cden, P0_1RB1LA_1RC0RB_1LD1LD_1LA0LD, P1_1RB1LA_1RC0RB_1LD1LD_1LA0LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB1LA_1RC0RB_1LD1LD_1LA0LD : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct j as [|j'].
  - destruct (gz_1RB1LA_1RC0RB_1LD1LD_1LA0LD p q0 E) as (HA & HB).
    exists (0 * 0 + 6). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chz_1RB1LA_1RC0RB_1LD1LD_1LA0LD Z0_1RB1LA_1RC0RB_1LD1LD_1LA0LD Z1_1RB1LA_1RC0RB_1LD1LD_1LA0LD 0 6
               run_z_1RB1LA_1RC0RB_1LD1LD_1LA0LD (Kp q0 ++ [S0]) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gp_1RB1LA_1RC0RB_1LD1LD_1LA0LD p j' q0 E) as (HA & HB).
    exists (2 * j' + 8). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chp_1RB1LA_1RC0RB_1LD1LD_1LA0LD P0_1RB1LA_1RC0RB_1LD1LD_1LA0LD P1_1RB1LA_1RC0RB_1LD1LD_1LA0LD 2 8
               run_p_1RB1LA_1RC0RB_1LD1LD_1LA0LD (Kp q0 ++ [S0]) [] j'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
Qed.

Lemma gso_1RB1LA_1RC0RB_1LD1LD_1LA0LD : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_1RB1LA_1RC0RB_1LD1LD_1LA0LD.
Proof.
  intros p j E. destruct (KpCounter.cview_none_K p j E) as (H1 & _).
  unfold Cc_1RB1LA_1RC0RB_1LD1LD_1LA0LD, cden, B0_1RB1LA_1RC0RB_1LD1LD_1LA0LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB1LA_1RC0RB_1LD1LD_1LA0LD : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB1LA_1RC0RB_1LD1LD_1LA0LD : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB1LA_1RC0RB_1LD1LD_1LA0LD) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (KpCounter.cview_none_K p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB1LA_1RC0RB_1LD1LD_1LA0LD
             = (StD, (rep [S0] (S j) ++ [S1], S0, [S0;S1;S1]))).
  { unfold cden, B1_1RB1LA_1RC0RB_1LD1LD_1LA0LD, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StD, ((rep [S0] (S j) ++ [S1]) ++ [S0], S0, [S0;S1;S1]))).
  { unfold Cc_1RB1LA_1RC0RB_1LD1LD_1LA0LD. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_1RB1LA_1RC0RB_1LD1LD_1LA0LD. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_1RB1LA_1RC0RB_1LD1LD_1LA0LD : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB1LA_1RC0RB_1LD1LD_1LA0LD p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_1RB1LA_1RC0RB_1LD1LD_1LA0LD B0_1RB1LA_1RC0RB_1LD1LD_1LA0LD B1_1RB1LA_1RC0RB_1LD1LD_1LA0LD 2 8 p j' [] []).
    + exact run_ovf_1RB1LA_1RC0RB_1LD1LD_1LA0LD.
    + reflexivity.
    + reflexivity.
    + exact (gso_1RB1LA_1RC0RB_1LD1LD_1LA0LD p j' E).
    + exact (geo_1RB1LA_1RC0RB_1LD1LD_1LA0LD p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma bootq_1RB1LA_1RC0RB_1LD1LD_1LA0LD : stepn tm_1RB1LA_1RC0RB_1LD1LD_1LA0LD 11 InitES = Some (lift (Cc 1)).
Proof.
  assert (H : match csteps tm_1RB1LA_1RC0RB_1LD1LD_1LA0LD 11 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm_1RB1LA_1RC0RB_1LD1LD_1LA0LD 11 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** the quasihalt witness: a pinned instruction fired in the prefix *)
Lemma wit_1RB1LA_1RC0RB_1LD1LD_1LA0LD : existsb (fun tg => cfires tm_1RB1LA_1RC0RB_1LD1LD_1LA0LD c0 11 tg) pins_1RB1LA_1RC0RB_1LD1LD_1LA0LD = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_1RB1LA_1RC0RB_1LD1LD_1LA0LD : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_1RB1LA_1RC0RB_1LD1LD_1LA0LD = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_1RB1LA_1RC0RB_1LD1LD_1LA0LD p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB1LA_1RC0RB_1LD1LD_1LA0LD p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_1RB1LA_1RC0RB_1LD1LD_1LA0LD : forall t, ~ In t pins_1RB1LA_1RC0RB_1LD1LD_1LA0LD ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_1RB1LA_1RC0RB_1LD1LD_1LA0LD.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_via_ovf tm Cc Hi (StA, S0)), fireo_1RB1LA_1RC0RB_1LD1LD_1LA0LD
      with (l := [SWin 1; SCycL 1 0; SWin 1]).
    vm_compute; reflexivity.
  - (* A1 *)
    apply (fire_via_ovf tm Cc Hi (StA, S1)), fireo_1RB1LA_1RC0RB_1LD1LD_1LA0LD
      with (l := [SWin 1]).
    vm_compute; reflexivity.
  - (* B0 *)
    apply (fire_via_ovf tm Cc Hi (StB, S0)), fireo_1RB1LA_1RC0RB_1LD1LD_1LA0LD
      with (l := [SWin 1; SCycL 1 0; SWin 2; SCycR 1; SWin 2]).
    vm_compute; reflexivity.
  - (* B1 *)
    apply (fire_via_ovf tm Cc Hi (StB, S1)), fireo_1RB1LA_1RC0RB_1LD1LD_1LA0LD
      with (l := [SWin 1; SCycL 1 0; SWin 2]).
    vm_compute; reflexivity.
  - (* C0: pinned *)
    exfalso. apply Hnp. apply tr_inb_spec. reflexivity.
  - (* C1 *)
    apply (fire_via_ovf tm Cc Hi (StC, S1)), fireo_1RB1LA_1RC0RB_1LD1LD_1LA0LD
      with (l := [SWin 1; SCycL 1 0; SWin 2; SCycR 1; SWin 3]).
    vm_compute; reflexivity.
  - (* D0 *)
    apply (fire_via_ovf tm Cc Hi (StD, S0)), fireo_1RB1LA_1RC0RB_1LD1LD_1LA0LD
      with (l := []).
    vm_compute; reflexivity.
  - (* D1 *)
    apply (fire_via_ovf tm Cc Hi (StD, S1)), fireo_1RB1LA_1RC0RB_1LD1LD_1LA0LD
      with (l := [SWin 1; SCycL 1 0; SWin 2; SCycR 1; SWin 4]).
    vm_compute; reflexivity.
Qed.

Theorem qhtr_1RB1LA_1RC0RB_1LD1LD_1LA0LD : NonHalt tm_1RB1LA_1RC0RB_1LD1LD_1LA0LD /\ QHBoundTr 32779478 tm_1RB1LA_1RC0RB_1LD1LD_1LA0LD /\ QuasiHaltsTr tm_1RB1LA_1RC0RB_1LD1LD_1LA0LD.
Proof.
  apply (lap_qh_stage tm_1RB1LA_1RC0RB_1LD1LD_1LA0LD pins_1RB1LA_1RC0RB_1LD1LD_1LA0LD Cc 1 11 32779478).
  - exact bootq_1RB1LA_1RC0RB_1LD1LD_1LA0LD.
  - intros p _. apply lap_1RB1LA_1RC0RB_1LD1LD_1LA0LD.
  - intros t Ht p _. apply fire_1RB1LA_1RC0RB_1LD1LD_1LA0LD. exact Ht.
  - exact wit_1RB1LA_1RC0RB_1LD1LD_1LA0LD.
  - vm_cast_no_check (eq_refl true).
Qed.
