(** * LAPQ_0RB0LD_1RC0LD_1LB1RB_0RB0LA: TRANSITION-LEVEL QUASIHALTING-side board for machine 0RB0LD_1RC0LD_1LB1RB_0RB0LA, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Ap_Alph_00_10_1 digit alphabet (Alph_00_10_1.v), anchored at

      Cc p = (StB, (Ap_Alph_00_10_1 p ++ [S0], S0, []))

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
                                  MonoCounter JpCounter Alph_00_10_1 LapCertGlue LapCertGlueLift.
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

Definition mk_0RB0LD_1RC0LD_1LB1RB_0RB0LA (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB0LD_1RC0LD_1LB1RB_0RB0LA.

(** 0RB0LD_1RC0LD_1LB1RB_0RB0LA *)
(** 0RB0LD_1RC0LD_1LB1RB_0RB0LA -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB0LD_1RC0LD_1LB1RB_0RB0LA : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S0 DL StD
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S0 DL StD
  | StC, S0 => mk S1 DL StB | StC, S1 => mk S1 DR StB
  | StD, S0 => mk S0 DR StB | StD, S1 => mk S0 DL StA end.

(** Its mirror 0LB0RD_1LC0RD_1RB1LB_0LB0RA: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB0LD_1RC0LD_1LB1RB_0RB0LA : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S0 DR StD
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DR StD
  | StC, S0 => mk S1 DR StB | StC, S1 => mk S1 DL StB
  | StD, S0 => mk S0 DL StB | StD, S1 => mk S0 DR StA end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_0RB0LD_1RC0LD_1LB1RB_0RB0LA : list Instr := [(StA, S0)].
Definition tmw_0RB0LD_1RC0LD_1LB1RB_0RB0LA : TM := tm_wrap_trs tmm_0RB0LD_1RC0LD_1LB1RB_0RB0LA pins_0RB0LD_1RC0LD_1LB1RB_0RB0LA.
Local Notation tm := tmw_0RB0LD_1RC0LD_1LB1RB_0RB0LA.

Lemma mirror_ok_0RB0LD_1RC0LD_1LB1RB_0RB0LA : mirror_tm tm_0RB0LD_1RC0LD_1LB1RB_0RB0LA = tmm_0RB0LD_1RC0LD_1LB1RB_0RB0LA.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_0RB0LD_1RC0LD_1LB1RB_0RB0LA (p : positive) : cconf := (StB, (Ap_Alph_00_10_1 p ++ [S0], S0, [])).
Local Notation Cc := Cc_0RB0LD_1RC0LD_1LB1RB_0RB0LA.

(** ** The certificate *)

(** j = 0: the repeated block is absent, so the whole lap is concrete. *)
Definition Z0_0RB0LD_1RC0LD_1LB1RB_0RB0LA : sconf := mkC StB (mkS [S0;S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition Z1_0RB0LD_1RC0LD_1LB1RB_0RB0LA : sconf := mkC StB (mkS [S1;S0] [] 0 0 []) S0 (mkS [S0] [] 0 0 []).
Definition chz_0RB0LD_1RC0LD_1LB1RB_0RB0LA : list lstep := [SWin 2; SWinR 2].

Lemma run_z_0RB0LD_1RC0LD_1LB1RB_0RB0LA : srun tm false true chz_0RB0LD_1RC0LD_1LB1RB_0RB0LA Z0_0RB0LD_1RC0LD_1LB1RB_0RB0LA = Some (Z1_0RB0LD_1RC0LD_1LB1RB_0RB0LA, 0, 4).
Proof. vm_compute. reflexivity. Qed.

(** j = S j': one copy of the unit sits in the PREFIX, so the head always has
    a concrete cell to step onto. *)
Definition P0_0RB0LD_1RC0LD_1LB1RB_0RB0LA : sconf := mkC StB (mkS [S1;S0] [S1;S0] 1 0 [S0;S0]) S0 (mkS [] [] 0 0 []).
Definition P1_0RB0LD_1RC0LD_1LB1RB_0RB0LA : sconf := mkC StB (mkS [S0;S0] [S0;S0] 1 0 [S1;S0]) S0 (mkS [S0] [] 0 0 []).
Definition chp_0RB0LD_1RC0LD_1LB1RB_0RB0LA : list lstep := [SWin 2; SCycL 2 0; SWin 2; SRotR 1; SWin 1; SCycR 2; SWin 1; SWinR 2; SRotL 1].

Lemma run_p_0RB0LD_1RC0LD_1LB1RB_0RB0LA : srun tm false true chp_0RB0LD_1RC0LD_1LB1RB_0RB0LA P0_0RB0LD_1RC0LD_1LB1RB_0RB0LA = Some (P1_0RB0LD_1RC0LD_1LB1RB_0RB0LA, 4, 8).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB0LD_1RC0LD_1LB1RB_0RB0LA : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_0RB0LD_1RC0LD_1LB1RB_0RB0LA : sconf := mkC StB (mkS [] [S0;S0] 1 1 [S1]) S0 (mkS [S0] [] 0 0 []).
Definition cho_0RB0LD_1RC0LD_1LB1RB_0RB0LA : list lstep := [SCycL 2 0; SWin 2; SWinL 4; SCycR 2; SWinR 2; SRotL 2; SFoldL 1].

Lemma run_ovf_0RB0LD_1RC0LD_1LB1RB_0RB0LA : srun tm true true cho_0RB0LD_1RC0LD_1LB1RB_0RB0LA B0_0RB0LD_1RC0LD_1LB1RB_0RB0LA = Some (B1_0RB0LD_1RC0LD_1LB1RB_0RB0LA, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gz_0RB0LD_1RC0LD_1LB1RB_0RB0LA : forall p q0, cview p = (0, Some q0) ->
  Cc p = cden (Ap_Alph_00_10_1 q0 ++ [S0]) [] 0 Z0_0RB0LD_1RC0LD_1LB1RB_0RB0LA /\
  lift (cden (Ap_Alph_00_10_1 q0 ++ [S0]) [] 0 Z1_0RB0LD_1RC0LD_1LB1RB_0RB0LA) = lift (Cc (Pos.succ p)).
Proof.
  intros p q0 E. destruct (Alph_00_10_1.cview_some_Alph_00_10_1 p 0 q0 E) as (H1 & H2).
  unfold Cc_0RB0LD_1RC0LD_1LB1RB_0RB0LA, cden, Z0_0RB0LD_1RC0LD_1LB1RB_0RB0LA, Z1_0RB0LD_1RC0LD_1LB1RB_0RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - cbn [rep app Nat.mul Nat.add]; rewrite ?app_nil_r.
    change ([S0]) with (([]) ++ [S0]).
    rewrite !lift_app_blank.
    rewrite H2; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gp_0RB0LD_1RC0LD_1LB1RB_0RB0LA : forall p j q0, cview p = (S j, Some q0) ->
  Cc p = cden (Ap_Alph_00_10_1 q0 ++ [S0]) [] j P0_0RB0LD_1RC0LD_1LB1RB_0RB0LA /\
  lift (cden (Ap_Alph_00_10_1 q0 ++ [S0]) [] j P1_0RB0LD_1RC0LD_1LB1RB_0RB0LA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (Alph_00_10_1.cview_some_Alph_00_10_1 p (S j) q0 E) as (H1 & H2).
  unfold Cc_0RB0LD_1RC0LD_1LB1RB_0RB0LA, cden, P0_0RB0LD_1RC0LD_1LB1RB_0RB0LA, P1_0RB0LD_1RC0LD_1LB1RB_0RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - cbn [rep app Nat.mul Nat.add]; rewrite ?app_nil_r.
    change ([S0]) with (([]) ++ [S0]).
    rewrite !lift_app_blank.
    rewrite H2; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_0RB0LD_1RC0LD_1LB1RB_0RB0LA : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct j as [|j'].
  - destruct (gz_0RB0LD_1RC0LD_1LB1RB_0RB0LA p q0 E) as (HA & HB).
    exists (0 * 0 + 4), (cden (Ap_Alph_00_10_1 q0 ++ [S0]) [] 0 Z1_0RB0LD_1RC0LD_1LB1RB_0RB0LA).
    split; [lia|]. split; [| exact HB].
    rewrite HA.
    exact (srun_sound tm false true chz_0RB0LD_1RC0LD_1LB1RB_0RB0LA Z0_0RB0LD_1RC0LD_1LB1RB_0RB0LA Z1_0RB0LD_1RC0LD_1LB1RB_0RB0LA 0 4
             run_z_0RB0LD_1RC0LD_1LB1RB_0RB0LA (Ap_Alph_00_10_1 q0 ++ [S0]) [] 0
             ltac:(discriminate) ltac:(reflexivity)).
  - destruct (gp_0RB0LD_1RC0LD_1LB1RB_0RB0LA p j' q0 E) as (HA & HB).
    exists (4 * j' + 8), (cden (Ap_Alph_00_10_1 q0 ++ [S0]) [] j' P1_0RB0LD_1RC0LD_1LB1RB_0RB0LA).
    split; [lia|]. split; [| exact HB].
    rewrite HA.
    exact (srun_sound tm false true chp_0RB0LD_1RC0LD_1LB1RB_0RB0LA P0_0RB0LD_1RC0LD_1LB1RB_0RB0LA P1_0RB0LD_1RC0LD_1LB1RB_0RB0LA 4 8
             run_p_0RB0LD_1RC0LD_1LB1RB_0RB0LA (Ap_Alph_00_10_1 q0 ++ [S0]) [] j'
             ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma gso_0RB0LD_1RC0LD_1LB1RB_0RB0LA : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_0RB0LD_1RC0LD_1LB1RB_0RB0LA.
Proof.
  intros p j E. destruct (Alph_00_10_1.cview_none_Alph_00_10_1 p j E) as (H1 & _).
  unfold Cc_0RB0LD_1RC0LD_1LB1RB_0RB0LA, cden, B0_0RB0LD_1RC0LD_1LB1RB_0RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_0RB0LD_1RC0LD_1LB1RB_0RB0LA : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_0RB0LD_1RC0LD_1LB1RB_0RB0LA : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB0LD_1RC0LD_1LB1RB_0RB0LA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (Alph_00_10_1.cview_none_Alph_00_10_1 p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_0RB0LD_1RC0LD_1LB1RB_0RB0LA
             = (StB, (rep [S0;S0] (S j) ++ [S1], S0, ([]) ++ [S0]))).
  { unfold cden, B1_0RB0LD_1RC0LD_1LB1RB_0RB0LA, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StB, ((rep [S0;S0] (S j) ++ [S1]) ++ [S0], S0, []))).
  { unfold Cc_0RB0LD_1RC0LD_1LB1RB_0RB0LA. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lift_app_blank. rewrite !lbl_0RB0LD_1RC0LD_1LB1RB_0RB0LA. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_0RB0LD_1RC0LD_1LB1RB_0RB0LA : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB0LD_1RC0LD_1LB1RB_0RB0LA p j q0 E) as (n & c' & Hn & Hrun & Hlift).
    exists n, c'. split; [exact Hrun | split; [exact Hlift | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_0RB0LD_1RC0LD_1LB1RB_0RB0LA B0_0RB0LD_1RC0LD_1LB1RB_0RB0LA B1_0RB0LD_1RC0LD_1LB1RB_0RB0LA 4 8 p j' [] []).
    + exact run_ovf_0RB0LD_1RC0LD_1LB1RB_0RB0LA.
    + reflexivity.
    + reflexivity.
    + exact (gso_0RB0LD_1RC0LD_1LB1RB_0RB0LA p j' E).
    + exact (geo_0RB0LD_1RC0LD_1LB1RB_0RB0LA p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma bootq_0RB0LD_1RC0LD_1LB1RB_0RB0LA : stepn tmm_0RB0LD_1RC0LD_1LB1RB_0RB0LA 5 InitES = Some (lift (Cc 1)).
Proof.
  assert (H : match csteps tmm_0RB0LD_1RC0LD_1LB1RB_0RB0LA 5 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tmm_0RB0LD_1RC0LD_1LB1RB_0RB0LA 5 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** the quasihalt witness: a pinned instruction fired in the prefix *)
Lemma wit_0RB0LD_1RC0LD_1LB1RB_0RB0LA : existsb (fun tg => cfires tmm_0RB0LD_1RC0LD_1LB1RB_0RB0LA c0 5 tg) pins_0RB0LD_1RC0LD_1LB1RB_0RB0LA = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_0RB0LD_1RC0LD_1LB1RB_0RB0LA : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_0RB0LD_1RC0LD_1LB1RB_0RB0LA = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_0RB0LD_1RC0LD_1LB1RB_0RB0LA p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB0LD_1RC0LD_1LB1RB_0RB0LA p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_0RB0LD_1RC0LD_1LB1RB_0RB0LA : forall t, ~ In t pins_0RB0LD_1RC0LD_1LB1RB_0RB0LA ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n c', 0 < n /\ csteps tm n (Cc p0) = Some c'
                         /\ lift c' = lift (Cc (Pos.succ p0)))
    by exact lapi_0RB0LD_1RC0LD_1LB1RB_0RB0LA.
  destruct t as [q b]; destruct q, b.
  - (* A0: pinned *)
    exfalso. apply Hnp. apply tr_inb_spec. reflexivity.
  - (* A1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StA, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB0LD_1RC0LD_1LB1RB_0RB0LA [SCycL 2 0; SWin 2; SWinL 4] (StA, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* B0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StB, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB0LD_1RC0LD_1LB1RB_0RB0LA [] (StB, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* B1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StB, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB0LD_1RC0LD_1LB1RB_0RB0LA [SCycL 2 0; SWin 2; SWinL 2] (StB, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* C0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StC, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB0LD_1RC0LD_1LB1RB_0RB0LA [SCycL 2 0; SWin 2; SWinL 1] (StC, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* C1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StC, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB0LD_1RC0LD_1LB1RB_0RB0LA [SCycL 2 0; SWin 1] (StC, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* D0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StD, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB0LD_1RC0LD_1LB1RB_0RB0LA [SCycL 2 0; SWin 2; SWinL 4; SCycR 2; SWinR 1] (StD, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* D1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StD, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB0LD_1RC0LD_1LB1RB_0RB0LA [SCycL 2 0; SWin 2; SWinL 3] (StD, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
Qed.

Theorem qhtrm_0RB0LD_1RC0LD_1LB1RB_0RB0LA : NonHalt tmm_0RB0LD_1RC0LD_1LB1RB_0RB0LA /\ QHBoundTr 32779478 tmm_0RB0LD_1RC0LD_1LB1RB_0RB0LA /\ QuasiHaltsTr tmm_0RB0LD_1RC0LD_1LB1RB_0RB0LA.
Proof.
  apply (lap_qh_stage tmm_0RB0LD_1RC0LD_1LB1RB_0RB0LA pins_0RB0LD_1RC0LD_1LB1RB_0RB0LA Cc 1 5 32779478).
  - exact bootq_0RB0LD_1RC0LD_1LB1RB_0RB0LA.
  - intros p _. apply lap_0RB0LD_1RC0LD_1LB1RB_0RB0LA.
  - intros t Ht p _. apply fire_0RB0LD_1RC0LD_1LB1RB_0RB0LA. exact Ht.
  - exact wit_0RB0LD_1RC0LD_1LB1RB_0RB0LA.
  - vm_cast_no_check (eq_refl true).
Qed.

Theorem qhtr_0RB0LD_1RC0LD_1LB1RB_0RB0LA : NonHalt tm_0RB0LD_1RC0LD_1LB1RB_0RB0LA /\ QHBoundTr 32779478 tm_0RB0LD_1RC0LD_1LB1RB_0RB0LA /\ QuasiHaltsTr tm_0RB0LD_1RC0LD_1LB1RB_0RB0LA.
Proof. apply (qh_triple_unmirror 32779478 tm_0RB0LD_1RC0LD_1LB1RB_0RB0LA). rewrite mirror_ok_0RB0LD_1RC0LD_1LB1RB_0RB0LA. exact qhtrm_0RB0LD_1RC0LD_1LB1RB_0RB0LA. Qed.
