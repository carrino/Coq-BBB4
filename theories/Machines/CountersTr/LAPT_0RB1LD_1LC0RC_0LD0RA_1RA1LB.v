(** * LAPT_0RB1LD_1LC0RC_0LD0RA_1RA1LB: TRANSITION-LEVEL board for machine 0RB1LD_1LC0RC_0LD0RA_1RA1LB, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Ap_Alph_000_001_00 digit alphabet (Alph_000_001_00.v), anchored at

      Cc p = (StD, (Ap_Alph_000_001_00 p ++ [S1;S0], S0, [S1;S1;S0;S1]))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  6*j+10 steps
      overflow  (cview p = (S j, None)):   6*j+16 steps

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 198 anchors.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter Alph_000_001_00 LapCertGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
From BBB4 Require Import BBBT4_Statement.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
Import ListNotations.

Definition mk_0RB1LD_1LC0RC_0LD0RA_1RA1LB (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB1LD_1LC0RC_0LD0RA_1RA1LB.

(** 0RB1LD_1LC0RC_0LD0RA_1RA1LB *)
Definition tm_0RB1LD_1LC0RC_0LD0RA_1RA1LB : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S1 DL StD
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DR StC
  | StC, S0 => mk S0 DL StD | StC, S1 => mk S0 DR StA
  | StD, S0 => mk S1 DR StA | StD, S1 => mk S1 DL StB end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_0RB1LD_1LC0RC_0LD0RA_1RA1LB : list Instr := [].
Definition tmw_0RB1LD_1LC0RC_0LD0RA_1RA1LB : TM := tm_wrap_trs tm_0RB1LD_1LC0RC_0LD0RA_1RA1LB pins_0RB1LD_1LC0RC_0LD0RA_1RA1LB.
Local Notation tm := tmw_0RB1LD_1LC0RC_0LD0RA_1RA1LB.

Definition Cc_0RB1LD_1LC0RC_0LD0RA_1RA1LB (p : positive) : cconf := (StD, (Ap_Alph_000_001_00 p ++ [S1;S0], S0, [S1;S1;S0;S1])).
Local Notation Cc := Cc_0RB1LD_1LC0RC_0LD0RA_1RA1LB.

(** ** The certificate *)

Definition A0_0RB1LD_1LC0RC_0LD0RA_1RA1LB : sconf := mkC StD (mkS [] [S0;S0;S1] 1 0 [S0;S0;S0]) S0 (mkS [S1;S1;S0;S1] [] 0 0 []).
Definition A1_0RB1LD_1LC0RC_0LD0RA_1RA1LB : sconf := mkC StD (mkS [] [S0;S0;S0] 1 0 [S0;S0;S1]) S0 (mkS [S1;S1;S0;S1] [] 0 0 []).
Definition chi_0RB1LD_1LC0RC_0LD0RA_1RA1LB : list lstep := [SWin 2; SCycL 3 0; SWin 6; SCycR 3; SWin 2].

Lemma run_int_0RB1LD_1LC0RC_0LD0RA_1RA1LB : srun tm false true chi_0RB1LD_1LC0RC_0LD0RA_1RA1LB A0_0RB1LD_1LC0RC_0LD0RA_1RA1LB = Some (A1_0RB1LD_1LC0RC_0LD0RA_1RA1LB, 6, 10).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB1LD_1LC0RC_0LD0RA_1RA1LB : sconf := mkC StD (mkS [] [S0;S0;S1] 1 0 [S0;S0;S1;S0]) S0 (mkS [S1;S1;S0;S1] [] 0 0 []).
Definition B1_0RB1LD_1LC0RC_0LD0RA_1RA1LB : sconf := mkC StD (mkS [] [S0;S0;S0] 1 1 [S0;S0;S1]) S0 (mkS [S1;S1;S0;S1] [] 0 0 []).
Definition cho_0RB1LD_1LC0RC_0LD0RA_1RA1LB : list lstep := [SWin 2; SCycL 3 0; SWin 4; SWinL 8; SCycR 3; SWin 2; SRotL 3; SFoldL 1].

Lemma run_ovf_0RB1LD_1LC0RC_0LD0RA_1RA1LB : srun tm true true cho_0RB1LD_1LC0RC_0LD0RA_1RA1LB B0_0RB1LD_1LC0RC_0LD0RA_1RA1LB = Some (B1_0RB1LD_1LC0RC_0LD0RA_1RA1LB, 6, 16).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_0RB1LD_1LC0RC_0LD0RA_1RA1LB : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Ap_Alph_000_001_00 q0 ++ [S1;S0]) [] j A0_0RB1LD_1LC0RC_0LD0RA_1RA1LB.
Proof.
  intros p j q0 E. destruct (Alph_000_001_00.cview_some_Alph_000_001_00 p j q0 E) as (H1 & _).
  unfold Cc_0RB1LD_1LC0RC_0LD0RA_1RA1LB, cden, A0_0RB1LD_1LC0RC_0LD0RA_1RA1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S0;S0;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gei_0RB1LD_1LC0RC_0LD0RA_1RA1LB : forall p j q0, cview p = (j, Some q0) ->
  cden (Ap_Alph_000_001_00 q0 ++ [S1;S0]) [] j A1_0RB1LD_1LC0RC_0LD0RA_1RA1LB = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (Alph_000_001_00.cview_some_Alph_000_001_00 p j q0 E) as (_ & H2).
  unfold Cc_0RB1LD_1LC0RC_0LD0RA_1RA1LB, cden, A1_0RB1LD_1LC0RC_0LD0RA_1RA1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S0;S0;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_0RB1LD_1LC0RC_0LD0RA_1RA1LB : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (6 * j + 10). split; [lia|].
  rewrite (gsi_0RB1LD_1LC0RC_0LD0RA_1RA1LB p j q0 E).
  rewrite (srun_sound tm false true chi_0RB1LD_1LC0RC_0LD0RA_1RA1LB A0_0RB1LD_1LC0RC_0LD0RA_1RA1LB A1_0RB1LD_1LC0RC_0LD0RA_1RA1LB 6 10
             run_int_0RB1LD_1LC0RC_0LD0RA_1RA1LB (Ap_Alph_000_001_00 q0 ++ [S1;S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_0RB1LD_1LC0RC_0LD0RA_1RA1LB p j q0 E).
Qed.

Lemma gso_0RB1LD_1LC0RC_0LD0RA_1RA1LB : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_0RB1LD_1LC0RC_0LD0RA_1RA1LB.
Proof.
  intros p j E. destruct (Alph_000_001_00.cview_none_Alph_000_001_00 p j E) as (H1 & _).
  unfold Cc_0RB1LD_1LC0RC_0LD0RA_1RA1LB, cden, B0_0RB1LD_1LC0RC_0LD0RA_1RA1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_0RB1LD_1LC0RC_0LD0RA_1RA1LB : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_0RB1LD_1LC0RC_0LD0RA_1RA1LB : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB1LD_1LC0RC_0LD0RA_1RA1LB) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (Alph_000_001_00.cview_none_Alph_000_001_00 p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_0RB1LD_1LC0RC_0LD0RA_1RA1LB
             = (StD, (rep [S0;S0;S0] (S j) ++ [S0;S0;S1], S0, [S1;S1;S0;S1]))).
  { unfold cden, B1_0RB1LD_1LC0RC_0LD0RA_1RA1LB, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StD, ((rep [S0;S0;S0] (S j) ++ [S0;S0;S1]) ++ [S0], S0, [S1;S1;S0;S1]))).
  { unfold Cc_0RB1LD_1LC0RC_0LD0RA_1RA1LB. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_0RB1LD_1LC0RC_0LD0RA_1RA1LB. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_0RB1LD_1LC0RC_0LD0RA_1RA1LB : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB1LD_1LC0RC_0LD0RA_1RA1LB p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_0RB1LD_1LC0RC_0LD0RA_1RA1LB B0_0RB1LD_1LC0RC_0LD0RA_1RA1LB B1_0RB1LD_1LC0RC_0LD0RA_1RA1LB 6 16 p j' [] []).
    + exact run_ovf_0RB1LD_1LC0RC_0LD0RA_1RA1LB.
    + reflexivity.
    + reflexivity.
    + exact (gso_0RB1LD_1LC0RC_0LD0RA_1RA1LB p j' E).
    + exact (geo_0RB1LD_1LC0RC_0LD0RA_1RA1LB p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_0RB1LD_1LC0RC_0LD0RA_1RA1LB : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 25.
  assert (H : match csteps tm 25 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 25 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_0RB1LD_1LC0RC_0LD0RA_1RA1LB : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_0RB1LD_1LC0RC_0LD0RA_1RA1LB = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_0RB1LD_1LC0RC_0LD0RA_1RA1LB p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB1LD_1LC0RC_0LD0RA_1RA1LB p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_0RB1LD_1LC0RC_0LD0RA_1RA1LB : forall t, ~ In t pins_0RB1LD_1LC0RC_0LD0RA_1RA1LB ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_0RB1LD_1LC0RC_0LD0RA_1RA1LB.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_via_ovf tm Cc Hi (StA, S0)), fireo_0RB1LD_1LC0RC_0LD0RA_1RA1LB
      with (l := [SWin 2; SCycL 3 0; SWin 4; SWinL 3]).
    vm_compute; reflexivity.
  - (* A1 *)
    apply (fire_via_ovf tm Cc Hi (StA, S1)), fireo_0RB1LD_1LC0RC_0LD0RA_1RA1LB
      with (l := [SWin 1]).
    vm_compute; reflexivity.
  - (* B0 *)
    apply (fire_via_ovf tm Cc Hi (StB, S0)), fireo_0RB1LD_1LC0RC_0LD0RA_1RA1LB
      with (l := [SWin 2; SCycL 3 0; SWin 1]).
    vm_compute; reflexivity.
  - (* B1 *)
    apply (fire_via_ovf tm Cc Hi (StB, S1)), fireo_0RB1LD_1LC0RC_0LD0RA_1RA1LB
      with (l := [SWin 2; SCycL 3 0; SWin 4; SWinL 4]).
    vm_compute; reflexivity.
  - (* C0 *)
    apply (fire_via_ovf tm Cc Hi (StC, S0)), fireo_0RB1LD_1LC0RC_0LD0RA_1RA1LB
      with (l := [SWin 2; SCycL 3 0; SWin 2]).
    vm_compute; reflexivity.
  - (* C1 *)
    apply (fire_via_ovf tm Cc Hi (StC, S1)), fireo_0RB1LD_1LC0RC_0LD0RA_1RA1LB
      with (l := [SWin 2; SCycL 3 0; SWin 4; SWinL 5]).
    vm_compute; reflexivity.
  - (* D0 *)
    apply (fire_via_ovf tm Cc Hi (StD, S0)), fireo_0RB1LD_1LC0RC_0LD0RA_1RA1LB
      with (l := []).
    vm_compute; reflexivity.
  - (* D1 *)
    apply (fire_via_ovf tm Cc Hi (StD, S1)), fireo_0RB1LD_1LC0RC_0LD0RA_1RA1LB
      with (l := [SWin 2]).
    vm_compute; reflexivity.
Qed.

Theorem nqhtr_0RB1LD_1LC0RC_0LD0RA_1RA1LB : NeverQuasiHaltsTr tm_0RB1LD_1LC0RC_0LD0RA_1RA1LB.
Proof.
  apply (glue_neverqhtr tm_0RB1LD_1LC0RC_0LD0RA_1RA1LB pins_0RB1LD_1LC0RC_0LD0RA_1RA1LB Cc 1).
  - exact boot_0RB1LD_1LC0RC_0LD0RA_1RA1LB.
  - intros p _. apply lap_0RB1LD_1LC0RC_0LD0RA_1RA1LB.
  - intros t Ht p _. apply fire_0RB1LD_1LC0RC_0LD0RA_1RA1LB. exact Ht.
Qed.

Theorem nonhalt_0RB1LD_1LC0RC_0LD0RA_1RA1LB : NonHalt tm_0RB1LD_1LC0RC_0LD0RA_1RA1LB.
Proof. apply never_qh_tr_nonhalt, nqhtr_0RB1LD_1LC0RC_0LD0RA_1RA1LB. Qed.
