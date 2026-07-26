(** * LAPC_0RB0LC_1LC1RB_0RD1LA_0LB1LA: machine 0RB0LC_1LC1RB_0RD1LA_0LB1LA, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Ip digit alphabet (ILCounter.v), anchored at

      Cc p = (StA, (Ip p ++ [S1;S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  4*j+4 steps
      overflow  (cview p = (S j, None)):   4*j+11 steps

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 198 anchors.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape LapGlue MonoCounter ILCounter JpCounter
                                  LapCertGlue.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_0RB0LC_1LC1RB_0RD1LA_0LB1LA (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB0LC_1LC1RB_0RD1LA_0LB1LA.

(** 0RB0LC_1LC1RB_0RD1LA_0LB1LA *)
(** 0RB0LC_1LC1RB_0RD1LA_0LB1LA -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB0LC_1LC1RB_0RD1LA_0LB1LA : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S0 DL StC
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S0 DR StD | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S0 DL StB | StD, S1 => mk S1 DL StA end.

(** Its mirror 0LB0RC_1RC1LB_0LD1RA_0RB1RA: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB0LC_1LC1RB_0RD1LA_0LB1LA : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S0 DR StC
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S0 DL StD | StC, S1 => mk S1 DR StA
  | StD, S0 => mk S0 DR StB | StD, S1 => mk S1 DR StA end.
Local Notation tm := tmm_0RB0LC_1LC1RB_0RD1LA_0LB1LA.

Lemma mirror_ok_0RB0LC_1LC1RB_0RD1LA_0LB1LA : mirror_tm tm_0RB0LC_1LC1RB_0RD1LA_0LB1LA = tmm_0RB0LC_1LC1RB_0RD1LA_0LB1LA.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_0RB0LC_1LC1RB_0RD1LA_0LB1LA (p : positive) : cconf := (StA, (Ip p ++ [S1;S0], S0, [])).
Local Notation Cc := Cc_0RB0LC_1LC1RB_0RD1LA_0LB1LA.

(** ** The certificate *)

Definition A0_0RB0LC_1LC1RB_0RD1LA_0LB1LA : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition A1_0RB0LC_1LC1RB_0RD1LA_0LB1LA : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chi_0RB0LC_1LC1RB_0RD1LA_0LB1LA : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_int_0RB0LC_1LC1RB_0RD1LA_0LB1LA : srun tm false true chi_0RB0LC_1LC1RB_0RD1LA_0LB1LA A0_0RB0LC_1LC1RB_0RD1LA_0LB1LA = Some (A1_0RB0LC_1LC1RB_0RD1LA_0LB1LA, 4, 4).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB0LC_1LC1RB_0RD1LA_0LB1LA : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_0RB0LC_1LC1RB_0RD1LA_0LB1LA : sconf := mkC StA (mkS [S1;S0] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition cho_0RB0LC_1LC1RB_0RD1LA_0LB1LA : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 4; SCycR 2; SWin 3; SWinR 3].

Lemma run_ovf_0RB0LC_1LC1RB_0RD1LA_0LB1LA : srun tm true true cho_0RB0LC_1LC1RB_0RD1LA_0LB1LA B0_0RB0LC_1LC1RB_0RD1LA_0LB1LA = Some (B1_0RB0LC_1LC1RB_0RD1LA_0LB1LA, 4, 11).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_0RB0LC_1LC1RB_0RD1LA_0LB1LA : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Ip q0 ++ [S1;S0]) [] j A0_0RB0LC_1LC1RB_0RD1LA_0LB1LA.
Proof.
  intros p j q0 E. destruct (ILCounter.cview_some_I p j q0 E) as (H1 & _).
  unfold Cc_0RB0LC_1LC1RB_0RD1LA_0LB1LA, cden, A0_0RB0LC_1LC1RB_0RD1LA_0LB1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1, <- (app_assoc (rep [S1;S1] j)). reflexivity.
Qed.

Lemma gei_0RB0LC_1LC1RB_0RD1LA_0LB1LA : forall p j q0, cview p = (j, Some q0) ->
  cden (Ip q0 ++ [S1;S0]) [] j A1_0RB0LC_1LC1RB_0RD1LA_0LB1LA = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (ILCounter.cview_some_I p j q0 E) as (_ & H2).
  unfold Cc_0RB0LC_1LC1RB_0RD1LA_0LB1LA, cden, A1_0RB0LC_1LC1RB_0RD1LA_0LB1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2, <- (app_assoc (rep [S1;S0] j)). reflexivity.
Qed.

Lemma gso_0RB0LC_1LC1RB_0RD1LA_0LB1LA : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_0RB0LC_1LC1RB_0RD1LA_0LB1LA.
Proof.
  intros p j E. destruct (ILCounter.cview_none_I p j E) as (H1 & _).
  unfold Cc_0RB0LC_1LC1RB_0RD1LA_0LB1LA, cden, B0_0RB0LC_1LC1RB_0RD1LA_0LB1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1, <- (app_assoc (rep [S1;S1] j)). reflexivity.
Qed.

Lemma lbl_0RB0LC_1LC1RB_0RD1LA_0LB1LA : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_0RB0LC_1LC1RB_0RD1LA_0LB1LA : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB0LC_1LC1RB_0RD1LA_0LB1LA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (ILCounter.cview_none_I p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_0RB0LC_1LC1RB_0RD1LA_0LB1LA
             = (StA, ([S1;S0] ++ rep [S1;S0] j ++ [S1;S1], S0, []))).
  { unfold cden, B1_0RB0LC_1LC1RB_0RD1LA_0LB1LA, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. reflexivity. }
  assert (HC : Cc (Pos.succ p)
             = (StA, (([S1;S0] ++ rep [S1;S0] j ++ [S1;S1]) ++ [S0], S0, []))).
  { unfold Cc_0RB0LC_1LC1RB_0RD1LA_0LB1LA. rewrite H2. cbn [rep app]. rewrite <- !app_assoc.
    reflexivity. }
  rewrite HD, HC. rewrite !lbl_0RB0LC_1LC1RB_0RD1LA_0LB1LA. reflexivity.
Qed.

(** ** The lap *)

Lemma lapi_0RB0LC_1LC1RB_0RD1LA_0LB1LA : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (4 * j + 4). split; [lia|].
  rewrite (gsi_0RB0LC_1LC1RB_0RD1LA_0LB1LA p j q0 E).
  rewrite (srun_sound tm false true chi_0RB0LC_1LC1RB_0RD1LA_0LB1LA A0_0RB0LC_1LC1RB_0RD1LA_0LB1LA A1_0RB0LC_1LC1RB_0RD1LA_0LB1LA 4 4
             run_int_0RB0LC_1LC1RB_0RD1LA_0LB1LA (Ip q0 ++ [S1;S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_0RB0LC_1LC1RB_0RD1LA_0LB1LA p j q0 E).
Qed.

Lemma lap_0RB0LC_1LC1RB_0RD1LA_0LB1LA : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB0LC_1LC1RB_0RD1LA_0LB1LA p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_0RB0LC_1LC1RB_0RD1LA_0LB1LA B0_0RB0LC_1LC1RB_0RD1LA_0LB1LA B1_0RB0LC_1LC1RB_0RD1LA_0LB1LA 4 11 p j' [] []).
    + exact run_ovf_0RB0LC_1LC1RB_0RD1LA_0LB1LA.
    + reflexivity.
    + reflexivity.
    + exact (gso_0RB0LC_1LC1RB_0RD1LA_0LB1LA p j' E).
    + exact (geo_0RB0LC_1LC1RB_0RD1LA_0LB1LA p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_0RB0LC_1LC1RB_0RD1LA_0LB1LA : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 8.
  assert (H : match csteps tm 8 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 8 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma viso_0RB0LC_1LC1RB_0RD1LA_0LB1LA : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_0RB0LC_1LC1RB_0RD1LA_0LB1LA = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_0RB0LC_1LC1RB_0RD1LA_0LB1LA p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB0LC_1LC1RB_0RD1LA_0LB1LA p j E)].
Qed.

Lemma vis_0RB0LC_1LC1RB_0RD1LA_0LB1LA : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_0RB0LC_1LC1RB_0RD1LA_0LB1LA.
  destruct q.
  - (* StA: the anchor state *)
    exists 0. eexists. split; reflexivity.
  - (* StB *)
    apply (vis_via_ovf tm Cc Hi StB), viso_0RB0LC_1LC1RB_0RD1LA_0LB1LA
      with (l := [SRotL 1; SWin 1]).
    vm_compute; reflexivity.
  - (* StC *)
    apply (vis_via_ovf tm Cc Hi StC), viso_0RB0LC_1LC1RB_0RD1LA_0LB1LA
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 3]).
    vm_compute; reflexivity.
  - (* StD *)
    apply (vis_via_ovf tm Cc Hi StD), viso_0RB0LC_1LC1RB_0RD1LA_0LB1LA
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 4; SCycR 2; SWin 2]).
    vm_compute; reflexivity.
Qed.

Theorem nqhm_0RB0LC_1LC1RB_0RD1LA_0LB1LA : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 1). - exact boot_0RB0LC_1LC1RB_0RD1LA_0LB1LA. - intros p _. apply lap_0RB0LC_1LC1RB_0RD1LA_0LB1LA. - intros p q _. apply vis_0RB0LC_1LC1RB_0RD1LA_0LB1LA. Qed.

Theorem nqh_0RB0LC_1LC1RB_0RD1LA_0LB1LA : NeverQuasiHaltsSt tm_0RB0LC_1LC1RB_0RD1LA_0LB1LA.
Proof. apply (mirror_never_qh tm_0RB0LC_1LC1RB_0RD1LA_0LB1LA). rewrite mirror_ok_0RB0LC_1LC1RB_0RD1LA_0LB1LA. exact nqhm_0RB0LC_1LC1RB_0RD1LA_0LB1LA. Qed.

Theorem nonhalt_0RB0LC_1LC1RB_0RD1LA_0LB1LA : NonHalt tm_0RB0LC_1LC1RB_0RD1LA_0LB1LA.
Proof. apply never_qh_nonhalt, nqh_0RB0LC_1LC1RB_0RD1LA_0LB1LA. Qed.
