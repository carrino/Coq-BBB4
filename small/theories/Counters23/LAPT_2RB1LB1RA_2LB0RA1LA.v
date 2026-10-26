(** * LAPT_2RB1LB1RA_2LB0RA1LA: TRANSITION-LEVEL board for machine 2RB1LB1RA_2LB0RA1LA, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Ap_Alph_1_0_02 digit alphabet (Alph_1_0_02.v), anchored at

      Cc p = (StA, (Ap_Alph_1_0_02 p ++ [S0], S1, [S1;S2]))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  j=0: 2 ; j=S j': 2*j'+4 steps
      overflow  (cview p = (S j, None)):   2*j+6 steps

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 198 anchors.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From SmallBB Require Import Statement CTape.
From SmallBB.Counters Require Import WTape LapGlue
                                  MonoCounter JpCounter Alph_1_0_02 LapCertGlue.
From SmallBB.Checkers Require Import LapDecider.
From SmallBB Require Import StatementTr.
From SmallBB.Checkers Require Import WrapTr.
From SmallBB.Checkers.IRules Require Import AnchorVisitsTr.
From SmallBB.Counters Require Import LapGlueTr.
Import ListNotations.

Definition mk_2RB1LB1RA_2LB0RA1LA (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_2RB1LB1RA_2LB0RA1LA.

(** 2RB1LB1RA_2LB0RA1LA *)
Definition tm_2RB1LB1RA_2LB0RA1LA : TM := fun q s => match q, s with
  | StA, S0 => mk S2 DR StB
  | StA, S1 => mk S1 DL StB
  | StA, S2 => mk S1 DR StA
  | StB, S0 => mk S2 DL StB
  | StB, S1 => mk S0 DR StA
  | StB, S2 => mk S1 DL StA
  | StC, S0 => None
  | StC, S1 => None
  | StC, S2 => None end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_2RB1LB1RA_2LB0RA1LA : list Instr := [(StC, S0); (StC, S1); (StC, S2)].
Definition tmw_2RB1LB1RA_2LB0RA1LA : TM := tm_wrap_trs tm_2RB1LB1RA_2LB0RA1LA pins_2RB1LB1RA_2LB0RA1LA.
Local Notation tm := tmw_2RB1LB1RA_2LB0RA1LA.

Definition Cc_2RB1LB1RA_2LB0RA1LA (p : positive) : cconf := (StA, (Ap_Alph_1_0_02 p ++ [S0], S1, [S1;S2])).
Local Notation Cc := Cc_2RB1LB1RA_2LB0RA1LA.

(** ** The certificate *)

(** j = 0: the repeated block is absent, so the whole lap is concrete. *)
Definition Z0_2RB1LB1RA_2LB0RA1LA : sconf := mkC StA (mkS [S1] [] 0 0 []) S1 (mkS [S1;S2] [] 0 0 []).
Definition Z1_2RB1LB1RA_2LB0RA1LA : sconf := mkC StA (mkS [S0] [] 0 0 []) S1 (mkS [S1;S2] [] 0 0 []).
Definition chz_2RB1LB1RA_2LB0RA1LA : list lstep := [SWin 2].

Lemma run_z_2RB1LB1RA_2LB0RA1LA : srun tm false true chz_2RB1LB1RA_2LB0RA1LA Z0_2RB1LB1RA_2LB0RA1LA = Some (Z1_2RB1LB1RA_2LB0RA1LA, 0, 2).
Proof. vm_compute. reflexivity. Qed.

(** j = S j': one copy of the unit sits in the PREFIX, so the head always has
    a concrete cell to step onto. *)
Definition P0_2RB1LB1RA_2LB0RA1LA : sconf := mkC StA (mkS [S0] [S0] 1 0 [S1]) S1 (mkS [S1;S2] [] 0 0 []).
Definition P1_2RB1LB1RA_2LB0RA1LA : sconf := mkC StA (mkS [S1] [S1] 1 0 [S0]) S1 (mkS [S1;S2] [] 0 0 []).
Definition chp_2RB1LB1RA_2LB0RA1LA : list lstep := [SWin 1; SCycL 1 0; SWin 2; SCycR 1; SWin 1].

Lemma run_p_2RB1LB1RA_2LB0RA1LA : srun tm false true chp_2RB1LB1RA_2LB0RA1LA P0_2RB1LB1RA_2LB0RA1LA = Some (P1_2RB1LB1RA_2LB0RA1LA, 2, 4).
Proof. vm_compute. reflexivity. Qed.

Definition B0_2RB1LB1RA_2LB0RA1LA : sconf := mkC StA (mkS [] [S0] 1 0 [S0;S2;S0]) S1 (mkS [S1;S2] [] 0 0 []).
Definition B1_2RB1LB1RA_2LB0RA1LA : sconf := mkC StA (mkS [] [S1] 1 1 [S0;S2]) S1 (mkS [S1;S2] [] 0 0 []).
Definition cho_2RB1LB1RA_2LB0RA1LA : list lstep := [SRotL 1; SWin 1; SCycL 1 0; SWin 4; SCycR 1; SWin 1; SFoldL 1].

Lemma run_ovf_2RB1LB1RA_2LB0RA1LA : srun tm true true cho_2RB1LB1RA_2LB0RA1LA B0_2RB1LB1RA_2LB0RA1LA = Some (B1_2RB1LB1RA_2LB0RA1LA, 2, 6).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gz_2RB1LB1RA_2LB0RA1LA : forall p q0, cview p = (0, Some q0) ->
  Cc p = cden (Ap_Alph_1_0_02 q0 ++ [S0]) [] 0 Z0_2RB1LB1RA_2LB0RA1LA /\
  cden (Ap_Alph_1_0_02 q0 ++ [S0]) [] 0 Z1_2RB1LB1RA_2LB0RA1LA = Cc (Pos.succ p).
Proof.
  intros p q0 E. destruct (Alph_1_0_02.cview_some_Alph_1_0_02 p 0 q0 E) as (H1 & H2).
  unfold Cc_2RB1LB1RA_2LB0RA1LA, cden, Z0_2RB1LB1RA_2LB0RA1LA, Z1_2RB1LB1RA_2LB0RA1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gp_2RB1LB1RA_2LB0RA1LA : forall p j q0, cview p = (S j, Some q0) ->
  Cc p = cden (Ap_Alph_1_0_02 q0 ++ [S0]) [] j P0_2RB1LB1RA_2LB0RA1LA /\
  cden (Ap_Alph_1_0_02 q0 ++ [S0]) [] j P1_2RB1LB1RA_2LB0RA1LA = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (Alph_1_0_02.cview_some_Alph_1_0_02 p (S j) q0 E) as (H1 & H2).
  unfold Cc_2RB1LB1RA_2LB0RA1LA, cden, P0_2RB1LB1RA_2LB0RA1LA, P1_2RB1LB1RA_2LB0RA1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_2RB1LB1RA_2LB0RA1LA : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct j as [|j'].
  - destruct (gz_2RB1LB1RA_2LB0RA1LA p q0 E) as (HA & HB).
    exists (0 * 0 + 2). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chz_2RB1LB1RA_2LB0RA1LA Z0_2RB1LB1RA_2LB0RA1LA Z1_2RB1LB1RA_2LB0RA1LA 0 2
               run_z_2RB1LB1RA_2LB0RA1LA (Ap_Alph_1_0_02 q0 ++ [S0]) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gp_2RB1LB1RA_2LB0RA1LA p j' q0 E) as (HA & HB).
    exists (2 * j' + 4). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chp_2RB1LB1RA_2LB0RA1LA P0_2RB1LB1RA_2LB0RA1LA P1_2RB1LB1RA_2LB0RA1LA 2 4
               run_p_2RB1LB1RA_2LB0RA1LA (Ap_Alph_1_0_02 q0 ++ [S0]) [] j'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
Qed.

Lemma gso_2RB1LB1RA_2LB0RA1LA : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_2RB1LB1RA_2LB0RA1LA.
Proof.
  intros p j E. destruct (Alph_1_0_02.cview_none_Alph_1_0_02 p j E) as (H1 & _).
  unfold Cc_2RB1LB1RA_2LB0RA1LA, cden, B0_2RB1LB1RA_2LB0RA1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_2RB1LB1RA_2LB0RA1LA : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_2RB1LB1RA_2LB0RA1LA : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_2RB1LB1RA_2LB0RA1LA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (Alph_1_0_02.cview_none_Alph_1_0_02 p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_2RB1LB1RA_2LB0RA1LA
             = (StA, (rep [S1] (S j) ++ [S0;S2], S1, [S1;S2]))).
  { unfold cden, B1_2RB1LB1RA_2LB0RA1LA, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StA, ((rep [S1] (S j) ++ [S0;S2]) ++ [S0], S1, [S1;S2]))).
  { unfold Cc_2RB1LB1RA_2LB0RA1LA. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_2RB1LB1RA_2LB0RA1LA. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_2RB1LB1RA_2LB0RA1LA : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_2RB1LB1RA_2LB0RA1LA p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_2RB1LB1RA_2LB0RA1LA B0_2RB1LB1RA_2LB0RA1LA B1_2RB1LB1RA_2LB0RA1LA 2 6 p j' [] []).
    + exact run_ovf_2RB1LB1RA_2LB0RA1LA.
    + reflexivity.
    + reflexivity.
    + exact (gso_2RB1LB1RA_2LB0RA1LA p j' E).
    + exact (geo_2RB1LB1RA_2LB0RA1LA p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_2RB1LB1RA_2LB0RA1LA : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 9.
  assert (H : match csteps tm 9 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 9 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_2RB1LB1RA_2LB0RA1LA : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_2RB1LB1RA_2LB0RA1LA = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_2RB1LB1RA_2LB0RA1LA p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_2RB1LB1RA_2LB0RA1LA p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_2RB1LB1RA_2LB0RA1LA : forall t, ~ In t pins_2RB1LB1RA_2LB0RA1LA ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_2RB1LB1RA_2LB0RA1LA.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_via_ovf tm Cc Hi (StA, S0)), fireo_2RB1LB1RA_2LB0RA1LA
      with (l := [SRotL 1; SWin 1; SCycL 1 0; SWin 2]).
    vm_compute; reflexivity.
  - (* A1 *)
    apply (fire_via_ovf tm Cc Hi (StA, S1)), fireo_2RB1LB1RA_2LB0RA1LA
      with (l := []).
    vm_compute; reflexivity.
  - (* A2 *)
    apply (fire_via_ovf tm Cc Hi (StA, S2)), fireo_2RB1LB1RA_2LB0RA1LA
      with (l := [SRotL 1; SWin 1; SCycL 1 0; SWin 4]).
    vm_compute; reflexivity.
  - (* B0 *)
    apply (fire_via_ovf tm Cc Hi (StB, S0)), fireo_2RB1LB1RA_2LB0RA1LA
      with (l := [SRotL 1; SWin 1]).
    vm_compute; reflexivity.
  - (* B1 *)
    apply (fire_via_ovf tm Cc Hi (StB, S1)), fireo_2RB1LB1RA_2LB0RA1LA
      with (l := [SRotL 1; SWin 1; SCycL 1 0; SWin 3]).
    vm_compute; reflexivity.
  - (* B2 *)
    apply (fire_via_ovf tm Cc Hi (StB, S2)), fireo_2RB1LB1RA_2LB0RA1LA
      with (l := [SRotL 1; SWin 1; SCycL 1 0; SWin 1]).
    vm_compute; reflexivity.
  - (* C0: pinned *)
    exfalso. apply Hnp. apply tr_inb_spec. reflexivity.
  - (* C1: pinned *)
    exfalso. apply Hnp. apply tr_inb_spec. reflexivity.
  - (* C2: pinned *)
    exfalso. apply Hnp. apply tr_inb_spec. reflexivity.
Qed.

Theorem nqhtr_2RB1LB1RA_2LB0RA1LA : NeverQuasiHaltsTr tm_2RB1LB1RA_2LB0RA1LA.
Proof.
  apply (glue_neverqhtr tm_2RB1LB1RA_2LB0RA1LA pins_2RB1LB1RA_2LB0RA1LA Cc 1).
  - exact boot_2RB1LB1RA_2LB0RA1LA.
  - intros p _. apply lap_2RB1LB1RA_2LB0RA1LA.
  - intros t Ht p _. apply fire_2RB1LB1RA_2LB0RA1LA. exact Ht.
Qed.

Theorem nonhalt_2RB1LB1RA_2LB0RA1LA : NonHalt tm_2RB1LB1RA_2LB0RA1LA.
Proof. apply never_qh_tr_nonhalt, nqhtr_2RB1LB1RA_2LB0RA1LA. Qed.
