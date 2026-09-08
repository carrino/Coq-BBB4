(** * LAPT_1RB0LD_1RC0LD_1LB1RB_0RA1LD: TRANSITION-LEVEL board for machine 1RB0LD_1RC0LD_1LB1RB_0RA1LD, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Jp digit alphabet (JpCounter.v), anchored at

      Cc p = (StD, (Jp p ++ [S0;S1;S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  j=0: 6 ; j=S j': 4*j'+10 steps
      overflow  (cview p = (S j, None)):   4*j+12 steps

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

Definition mk_1RB0LD_1RC0LD_1LB1RB_0RA1LD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB0LD_1RC0LD_1LB1RB_0RA1LD.

(** 1RB0LD_1RC0LD_1LB1RB_0RA1LD *)
(** 1RB0LD_1RC0LD_1LB1RB_0RA1LD -- the real machine (its counter grows RIGHT). *)
Definition tm_1RB0LD_1RC0LD_1LB1RB_0RA1LD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StD
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S0 DL StD
  | StC, S0 => mk S1 DL StB | StC, S1 => mk S1 DR StB
  | StD, S0 => mk S0 DR StA | StD, S1 => mk S1 DL StD end.

(** Its mirror 1LB0RD_1LC0RD_1RB1LB_0LA1RD: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_1RB0LD_1RC0LD_1LB1RB_0RA1LD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => mk S0 DR StD
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DR StD
  | StC, S0 => mk S1 DR StB | StC, S1 => mk S1 DL StB
  | StD, S0 => mk S0 DL StA | StD, S1 => mk S1 DR StD end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_1RB0LD_1RC0LD_1LB1RB_0RA1LD : list Instr := [].
Definition tmw_1RB0LD_1RC0LD_1LB1RB_0RA1LD : TM := tm_wrap_trs tmm_1RB0LD_1RC0LD_1LB1RB_0RA1LD pins_1RB0LD_1RC0LD_1LB1RB_0RA1LD.
Local Notation tm := tmw_1RB0LD_1RC0LD_1LB1RB_0RA1LD.

Lemma mirror_ok_1RB0LD_1RC0LD_1LB1RB_0RA1LD : mirror_tm tm_1RB0LD_1RC0LD_1LB1RB_0RA1LD = tmm_1RB0LD_1RC0LD_1LB1RB_0RA1LD.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_1RB0LD_1RC0LD_1LB1RB_0RA1LD (p : positive) : cconf := (StD, (Jp p ++ [S0;S1;S0], S0, [])).
Local Notation Cc := Cc_1RB0LD_1RC0LD_1LB1RB_0RA1LD.

(** ** The certificate *)

(** j = 0: the repeated block is absent, so the whole lap is concrete. *)
Definition Z0_1RB0LD_1RC0LD_1LB1RB_0RA1LD : sconf := mkC StD (mkS [S1;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition Z1_1RB0LD_1RC0LD_1LB1RB_0RA1LD : sconf := mkC StD (mkS [S1;S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition chz_1RB0LD_1RC0LD_1LB1RB_0RA1LD : list lstep := [SWin 6].

Lemma run_z_1RB0LD_1RC0LD_1LB1RB_0RA1LD : srun tm false true chz_1RB0LD_1RC0LD_1LB1RB_0RA1LD Z0_1RB0LD_1RC0LD_1LB1RB_0RA1LD = Some (Z1_1RB0LD_1RC0LD_1LB1RB_0RA1LD, 0, 6).
Proof. vm_compute. reflexivity. Qed.

(** j = S j': one copy of the unit sits in the PREFIX, so the head always has
    a concrete cell to step onto. *)
Definition P0_1RB0LD_1RC0LD_1LB1RB_0RA1LD : sconf := mkC StD (mkS [S1;S0] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition P1_1RB0LD_1RC0LD_1LB1RB_0RA1LD : sconf := mkC StD (mkS [S1;S1] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chp_1RB0LD_1RC0LD_1LB1RB_0RA1LD : list lstep := [SWin 4; SCycL 2 0; SWin 4; SCycR 2; SWin 2].

Lemma run_p_1RB0LD_1RC0LD_1LB1RB_0RA1LD : srun tm false true chp_1RB0LD_1RC0LD_1LB1RB_0RA1LD P0_1RB0LD_1RC0LD_1LB1RB_0RA1LD = Some (P1_1RB0LD_1RC0LD_1LB1RB_0RA1LD, 4, 10).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB0LD_1RC0LD_1LB1RB_0RA1LD : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S0;S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_1RB0LD_1RC0LD_1LB1RB_0RA1LD : sconf := mkC StD (mkS [] [S1;S1] 1 1 [S1;S0;S1]) S0 (mkS [] [] 0 0 []).
Definition cho_1RB0LD_1RC0LD_1LB1RB_0RA1LD : list lstep := [SRotL 1; SWin 3; SRotL 1; SWin 1; SCycL 2 0; SWin 2; SWinL 4; SCycR 2; SWin 2; SFoldL 1].

Lemma run_ovf_1RB0LD_1RC0LD_1LB1RB_0RA1LD : srun tm true true cho_1RB0LD_1RC0LD_1LB1RB_0RA1LD B0_1RB0LD_1RC0LD_1LB1RB_0RA1LD = Some (B1_1RB0LD_1RC0LD_1LB1RB_0RA1LD, 4, 12).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gz_1RB0LD_1RC0LD_1LB1RB_0RA1LD : forall p q0, cview p = (0, Some q0) ->
  Cc p = cden (Jp q0 ++ [S0;S1;S0]) [] 0 Z0_1RB0LD_1RC0LD_1LB1RB_0RA1LD /\
  cden (Jp q0 ++ [S0;S1;S0]) [] 0 Z1_1RB0LD_1RC0LD_1LB1RB_0RA1LD = Cc (Pos.succ p).
Proof.
  intros p q0 E. destruct (JpCounter.cview_some_J p 0 q0 E) as (H1 & H2).
  unfold Cc_1RB0LD_1RC0LD_1LB1RB_0RA1LD, cden, Z0_1RB0LD_1RC0LD_1LB1RB_0RA1LD, Z1_1RB0LD_1RC0LD_1LB1RB_0RA1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gp_1RB0LD_1RC0LD_1LB1RB_0RA1LD : forall p j q0, cview p = (S j, Some q0) ->
  Cc p = cden (Jp q0 ++ [S0;S1;S0]) [] j P0_1RB0LD_1RC0LD_1LB1RB_0RA1LD /\
  cden (Jp q0 ++ [S0;S1;S0]) [] j P1_1RB0LD_1RC0LD_1LB1RB_0RA1LD = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p (S j) q0 E) as (H1 & H2).
  unfold Cc_1RB0LD_1RC0LD_1LB1RB_0RA1LD, cden, P0_1RB0LD_1RC0LD_1LB1RB_0RA1LD, P1_1RB0LD_1RC0LD_1LB1RB_0RA1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB0LD_1RC0LD_1LB1RB_0RA1LD : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct j as [|j'].
  - destruct (gz_1RB0LD_1RC0LD_1LB1RB_0RA1LD p q0 E) as (HA & HB).
    exists (0 * 0 + 6). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chz_1RB0LD_1RC0LD_1LB1RB_0RA1LD Z0_1RB0LD_1RC0LD_1LB1RB_0RA1LD Z1_1RB0LD_1RC0LD_1LB1RB_0RA1LD 0 6
               run_z_1RB0LD_1RC0LD_1LB1RB_0RA1LD (Jp q0 ++ [S0;S1;S0]) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gp_1RB0LD_1RC0LD_1LB1RB_0RA1LD p j' q0 E) as (HA & HB).
    exists (4 * j' + 10). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chp_1RB0LD_1RC0LD_1LB1RB_0RA1LD P0_1RB0LD_1RC0LD_1LB1RB_0RA1LD P1_1RB0LD_1RC0LD_1LB1RB_0RA1LD 4 10
               run_p_1RB0LD_1RC0LD_1LB1RB_0RA1LD (Jp q0 ++ [S0;S1;S0]) [] j'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
Qed.

Lemma gso_1RB0LD_1RC0LD_1LB1RB_0RA1LD : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_1RB0LD_1RC0LD_1LB1RB_0RA1LD.
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (H1 & _).
  unfold Cc_1RB0LD_1RC0LD_1LB1RB_0RA1LD, cden, B0_1RB0LD_1RC0LD_1LB1RB_0RA1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB0LD_1RC0LD_1LB1RB_0RA1LD : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB0LD_1RC0LD_1LB1RB_0RA1LD : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB0LD_1RC0LD_1LB1RB_0RA1LD) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB0LD_1RC0LD_1LB1RB_0RA1LD
             = (StD, (rep [S1;S1] (S j) ++ [S1;S0;S1], S0, []))).
  { unfold cden, B1_1RB0LD_1RC0LD_1LB1RB_0RA1LD, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StD, ((rep [S1;S1] (S j) ++ [S1;S0;S1]) ++ [S0], S0, []))).
  { unfold Cc_1RB0LD_1RC0LD_1LB1RB_0RA1LD. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_1RB0LD_1RC0LD_1LB1RB_0RA1LD. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_1RB0LD_1RC0LD_1LB1RB_0RA1LD : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB0LD_1RC0LD_1LB1RB_0RA1LD p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_1RB0LD_1RC0LD_1LB1RB_0RA1LD B0_1RB0LD_1RC0LD_1LB1RB_0RA1LD B1_1RB0LD_1RC0LD_1LB1RB_0RA1LD 4 12 p j' [] []).
    + exact run_ovf_1RB0LD_1RC0LD_1LB1RB_0RA1LD.
    + reflexivity.
    + reflexivity.
    + exact (gso_1RB0LD_1RC0LD_1LB1RB_0RA1LD p j' E).
    + exact (geo_1RB0LD_1RC0LD_1LB1RB_0RA1LD p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_1RB0LD_1RC0LD_1LB1RB_0RA1LD : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 5.
  assert (H : match csteps tm 5 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 5 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_1RB0LD_1RC0LD_1LB1RB_0RA1LD : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_1RB0LD_1RC0LD_1LB1RB_0RA1LD = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_1RB0LD_1RC0LD_1LB1RB_0RA1LD p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB0LD_1RC0LD_1LB1RB_0RA1LD p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_1RB0LD_1RC0LD_1LB1RB_0RA1LD : forall t, ~ In t pins_1RB0LD_1RC0LD_1LB1RB_0RA1LD ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_1RB0LD_1RC0LD_1LB1RB_0RA1LD.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_via_ovf tm Cc Hi (StA, S0)), fireo_1RB0LD_1RC0LD_1LB1RB_0RA1LD
      with (l := [SRotL 1; SWin 3]).
    vm_compute; reflexivity.
  - (* A1 *)
    apply (fire_via_ovf tm Cc Hi (StA, S1)), fireo_1RB0LD_1RC0LD_1LB1RB_0RA1LD
      with (l := [SRotL 1; SWin 1]).
    vm_compute; reflexivity.
  - (* B0 *)
    apply (fire_via_ovf tm Cc Hi (StB, S0)), fireo_1RB0LD_1RC0LD_1LB1RB_0RA1LD
      with (l := [SRotL 1; SWin 3; SRotL 1; SWin 1]).
    vm_compute; reflexivity.
  - (* B1 *)
    apply (fire_via_ovf tm Cc Hi (StB, S1)), fireo_1RB0LD_1RC0LD_1LB1RB_0RA1LD
      with (l := [SRotL 1; SWin 3; SRotL 1; SWin 1; SCycL 2 0; SWin 2; SWinL 2]).
    vm_compute; reflexivity.
  - (* C0 *)
    apply (fire_via_ovf tm Cc Hi (StC, S0)), fireo_1RB0LD_1RC0LD_1LB1RB_0RA1LD
      with (l := [SRotL 1; SWin 3; SRotL 1; SWin 1; SCycL 2 0; SWin 2; SWinL 1]).
    vm_compute; reflexivity.
  - (* C1 *)
    apply (fire_via_ovf tm Cc Hi (StC, S1)), fireo_1RB0LD_1RC0LD_1LB1RB_0RA1LD
      with (l := [SRotL 1; SWin 3; SRotL 1; SWin 1; SCycL 2 0; SWin 1]).
    vm_compute; reflexivity.
  - (* D0 *)
    apply (fire_via_ovf tm Cc Hi (StD, S0)), fireo_1RB0LD_1RC0LD_1LB1RB_0RA1LD
      with (l := []).
    vm_compute; reflexivity.
  - (* D1 *)
    apply (fire_via_ovf tm Cc Hi (StD, S1)), fireo_1RB0LD_1RC0LD_1LB1RB_0RA1LD
      with (l := [SRotL 1; SWin 3; SRotL 1; SWin 1; SCycL 2 0; SWin 2; SWinL 3]).
    vm_compute; reflexivity.
Qed.

Theorem nqhtrm_1RB0LD_1RC0LD_1LB1RB_0RA1LD : NeverQuasiHaltsTr tmm_1RB0LD_1RC0LD_1LB1RB_0RA1LD.
Proof.
  apply (glue_neverqhtr tmm_1RB0LD_1RC0LD_1LB1RB_0RA1LD pins_1RB0LD_1RC0LD_1LB1RB_0RA1LD Cc 1).
  - exact boot_1RB0LD_1RC0LD_1LB1RB_0RA1LD.
  - intros p _. apply lap_1RB0LD_1RC0LD_1LB1RB_0RA1LD.
  - intros t Ht p _. apply fire_1RB0LD_1RC0LD_1LB1RB_0RA1LD. exact Ht.
Qed.

Theorem nqhtr_1RB0LD_1RC0LD_1LB1RB_0RA1LD : NeverQuasiHaltsTr tm_1RB0LD_1RC0LD_1LB1RB_0RA1LD.
Proof. apply (neverqhtr_mirror tm_1RB0LD_1RC0LD_1LB1RB_0RA1LD). rewrite mirror_ok_1RB0LD_1RC0LD_1LB1RB_0RA1LD. exact nqhtrm_1RB0LD_1RC0LD_1LB1RB_0RA1LD. Qed.

Theorem nonhalt_1RB0LD_1RC0LD_1LB1RB_0RA1LD : NonHalt tm_1RB0LD_1RC0LD_1LB1RB_0RA1LD.
Proof. apply never_qh_tr_nonhalt, nqhtr_1RB0LD_1RC0LD_1LB1RB_0RA1LD. Qed.
