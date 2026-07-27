(** * LAPC_1RB1LC_1LA____1RD0LC_0RD1LC: machine 1RB1LC_1LA---_1RD0LC_0RD1LC, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Kp digit alphabet (KpCounter.v), anchored at

      Cc p = (StD, (Kp p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  2*j+6 steps
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
Import ListNotations.

Definition mk_1RB1LC_1LA____1RD0LC_0RD1LC (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1LC_1LA____1RD0LC_0RD1LC.

(** 1RB1LC_1LA---_1RD0LC_0RD1LC *)
Definition tm_1RB1LC_1LA____1RD0LC_0RD1LC : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StC
  | StB, S0 => mk S1 DL StA | StB, S1 => None
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S0 DL StC
  | StD, S0 => mk S0 DR StD | StD, S1 => mk S1 DL StC end.
Local Notation tm := tm_1RB1LC_1LA____1RD0LC_0RD1LC.

Definition Cc_1RB1LC_1LA____1RD0LC_0RD1LC (p : positive) : cconf := (StD, (Kp p ++ [S0], S0, [S1;S1])).
Local Notation Cc := Cc_1RB1LC_1LA____1RD0LC_0RD1LC.

(** ** The certificate *)

Definition A0_1RB1LC_1LA____1RD0LC_0RD1LC : sconf := mkC StD (mkS [] [S1] 1 0 [S0]) S0 (mkS [S1;S1] [] 0 0 []).
Definition A1_1RB1LC_1LA____1RD0LC_0RD1LC : sconf := mkC StD (mkS [] [S0] 1 0 [S1]) S0 (mkS [S1;S1] [] 0 0 []).
Definition chi_1RB1LC_1LA____1RD0LC_0RD1LC : list lstep := [SWin 4; SCycL 1 0; SWin 2; SCycR 1].

Lemma run_int_1RB1LC_1LA____1RD0LC_0RD1LC : srun tm false true chi_1RB1LC_1LA____1RD0LC_0RD1LC A0_1RB1LC_1LA____1RD0LC_0RD1LC = Some (A1_1RB1LC_1LA____1RD0LC_0RD1LC, 2, 6).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB1LC_1LA____1RD0LC_0RD1LC : sconf := mkC StD (mkS [S1] [S1] 1 0 [S0]) S0 (mkS [S1;S1] [] 0 0 []).
Definition B1_1RB1LC_1LA____1RD0LC_0RD1LC : sconf := mkC StD (mkS [] [S0] 1 1 [S1]) S0 (mkS [S1;S1] [] 0 0 []).
Definition cho_1RB1LC_1LA____1RD0LC_0RD1LC : list lstep := [SWin 5; SCycL 1 0; SWin 2; SCycR 1; SWin 1; SFoldL 1].

Lemma run_ovf_1RB1LC_1LA____1RD0LC_0RD1LC : srun tm true true cho_1RB1LC_1LA____1RD0LC_0RD1LC B0_1RB1LC_1LA____1RD0LC_0RD1LC = Some (B1_1RB1LC_1LA____1RD0LC_0RD1LC, 2, 8).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_1RB1LC_1LA____1RD0LC_0RD1LC : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Kp q0 ++ [S0]) [] j A0_1RB1LC_1LA____1RD0LC_0RD1LC.
Proof.
  intros p j q0 E. destruct (KpCounter.cview_some_K p j q0 E) as (H1 & _).
  unfold Cc_1RB1LC_1LA____1RD0LC_0RD1LC, cden, A0_1RB1LC_1LA____1RD0LC_0RD1LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gei_1RB1LC_1LA____1RD0LC_0RD1LC : forall p j q0, cview p = (j, Some q0) ->
  cden (Kp q0 ++ [S0]) [] j A1_1RB1LC_1LA____1RD0LC_0RD1LC = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (KpCounter.cview_some_K p j q0 E) as (_ & H2).
  unfold Cc_1RB1LC_1LA____1RD0LC_0RD1LC, cden, A1_1RB1LC_1LA____1RD0LC_0RD1LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB1LC_1LA____1RD0LC_0RD1LC : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (2 * j + 6). split; [lia|].
  rewrite (gsi_1RB1LC_1LA____1RD0LC_0RD1LC p j q0 E).
  rewrite (srun_sound tm false true chi_1RB1LC_1LA____1RD0LC_0RD1LC A0_1RB1LC_1LA____1RD0LC_0RD1LC A1_1RB1LC_1LA____1RD0LC_0RD1LC 2 6
             run_int_1RB1LC_1LA____1RD0LC_0RD1LC (Kp q0 ++ [S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_1RB1LC_1LA____1RD0LC_0RD1LC p j q0 E).
Qed.

Lemma gso_1RB1LC_1LA____1RD0LC_0RD1LC : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_1RB1LC_1LA____1RD0LC_0RD1LC.
Proof.
  intros p j E. destruct (KpCounter.cview_none_K p j E) as (H1 & _).
  unfold Cc_1RB1LC_1LA____1RD0LC_0RD1LC, cden, B0_1RB1LC_1LA____1RD0LC_0RD1LC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB1LC_1LA____1RD0LC_0RD1LC : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB1LC_1LA____1RD0LC_0RD1LC : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB1LC_1LA____1RD0LC_0RD1LC) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (KpCounter.cview_none_K p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB1LC_1LA____1RD0LC_0RD1LC
             = (StD, (rep [S0] (S j) ++ [S1], S0, [S1;S1]))).
  { unfold cden, B1_1RB1LC_1LA____1RD0LC_0RD1LC, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. reflexivity. }
  assert (HC : Cc (Pos.succ p) = (StD, ((rep [S0] (S j) ++ [S1]) ++ [S0], S0, [S1;S1]))).
  { unfold Cc_1RB1LC_1LA____1RD0LC_0RD1LC. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_1RB1LC_1LA____1RD0LC_0RD1LC. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_1RB1LC_1LA____1RD0LC_0RD1LC : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB1LC_1LA____1RD0LC_0RD1LC p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_1RB1LC_1LA____1RD0LC_0RD1LC B0_1RB1LC_1LA____1RD0LC_0RD1LC B1_1RB1LC_1LA____1RD0LC_0RD1LC 2 8 p j' [] []).
    + exact run_ovf_1RB1LC_1LA____1RD0LC_0RD1LC.
    + reflexivity.
    + reflexivity.
    + exact (gso_1RB1LC_1LA____1RD0LC_0RD1LC p j' E).
    + exact (geo_1RB1LC_1LA____1RD0LC_0RD1LC p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_1RB1LC_1LA____1RD0LC_0RD1LC : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 7.
  assert (H : match csteps tm 7 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 7 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma viso_1RB1LC_1LA____1RD0LC_0RD1LC : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_1RB1LC_1LA____1RD0LC_0RD1LC = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_1RB1LC_1LA____1RD0LC_0RD1LC p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB1LC_1LA____1RD0LC_0RD1LC p j E)].
Qed.

Lemma vis_1RB1LC_1LA____1RD0LC_0RD1LC : forall p q, In q [StC; StD] -> exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q Hq.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_1RB1LC_1LA____1RD0LC_0RD1LC.
  destruct q.

  - (* StA: not in the reached set *)
    exfalso; cbn in Hq; intuition discriminate.
  - (* StB: not in the reached set *)
    exfalso; cbn in Hq; intuition discriminate.
  - (* StC *)
    apply (vis_via_ovf tm Cc Hi StC), viso_1RB1LC_1LA____1RD0LC_0RD1LC
      with (l := [SWin 2]).
    vm_compute; reflexivity.
  - (* StD: the anchor state *)
    exists 0. eexists. split; reflexivity.
Qed.

(** The lap reaches only StC, StD, which is CLOSED under the table, and the
    machine is already inside it at configuration index 3 -- so every state
    outside made all of its visits before 3 ([LapGlueAbs.glue_qh_abs]).
    StA, StB is therefore quiet, with a last visit before 3; the bound is
    weakened to the census tier's 2000. *)
Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.

Theorem iqh_1RB1LC_1LA____1RD0LC_0RD1LC : iqh tm.
Proof.
  destruct (glue_qh_abs tm Cc 1 [StC; StD] 3
                    boot_1RB1LC_1LA____1RD0LC_0RD1LC (fun p _ => lap_1RB1LC_1LA____1RD0LC_0RD1LC p)
                    (fun p q _ Hq => vis_1RB1LC_1LA____1RD0LC_0RD1LC p q Hq)
                    (closed_b_sound tm [StC; StD] ltac:(vm_compute; reflexivity))
                    ltac:(eexists; split;
                          [vm_compute; reflexivity | cbn; tauto])
                    ltac:(cbn; intuition discriminate))
    as (Hn & Hb & Hq).
  split; [exact Hn | split; [| exact Hq]].
  apply (qhbound_mono 3 2000); [lia | exact Hb].
Qed.

Theorem nonhalt_1RB1LC_1LA____1RD0LC_0RD1LC : NonHalt tm.
Proof. apply (proj1 iqh_1RB1LC_1LA____1RD0LC_0RD1LC). Qed.
