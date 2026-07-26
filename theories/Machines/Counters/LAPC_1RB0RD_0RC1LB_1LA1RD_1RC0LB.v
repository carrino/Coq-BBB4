(** * LAPC_1RB0RD_0RC1LB_1LA1RD_1RC0LB: machine 1RB0RD_0RC1LB_1LA1RD_1RC0LB, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Jp digit alphabet (JpCounter.v), anchored at

      Cc p = (StB, (Jp p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  4*j+4 steps
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
From BBB4.Counters Require Import WTape LapGlue LapGlueQH MonoCounter
                                  JpCounter JpCounter LapCertGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_1RB0RD_0RC1LB_1LA1RD_1RC0LB (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB0RD_0RC1LB_1LA1RD_1RC0LB.

(** 1RB0RD_0RC1LB_1LA1RD_1RC0LB *)
(** 1RB0RD_0RC1LB_1LA1RD_1RC0LB -- the real machine (its counter grows RIGHT). *)
Definition tm_1RB0RD_0RC1LB_1LA1RD_1RC0LB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DR StD
  | StB, S0 => mk S0 DR StC | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S1 DL StA | StC, S1 => mk S1 DR StD
  | StD, S0 => mk S1 DR StC | StD, S1 => mk S0 DL StB end.

(** Its mirror 1LB0LD_0LC1RB_1RA1LD_1LC0RB: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_1RB0RD_0RC1LB_1LA1RD_1RC0LB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => mk S0 DL StD
  | StB, S0 => mk S0 DL StC | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S1 DR StA | StC, S1 => mk S1 DL StD
  | StD, S0 => mk S1 DL StC | StD, S1 => mk S0 DR StB end.
Local Notation tm := tmm_1RB0RD_0RC1LB_1LA1RD_1RC0LB.

Lemma mirror_ok_1RB0RD_0RC1LB_1LA1RD_1RC0LB : mirror_tm tm_1RB0RD_0RC1LB_1LA1RD_1RC0LB = tmm_1RB0RD_0RC1LB_1LA1RD_1RC0LB.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_1RB0RD_0RC1LB_1LA1RD_1RC0LB (p : positive) : cconf := (StB, (Jp p ++ [S0], S0, [])).
Local Notation Cc := Cc_1RB0RD_0RC1LB_1LA1RD_1RC0LB.

(** ** The certificate *)

Definition A0_1RB0RD_0RC1LB_1LA1RD_1RC0LB : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition A1_1RB0RD_0RC1LB_1LA1RD_1RC0LB : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chi_1RB0RD_0RC1LB_1LA1RD_1RC0LB : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_int_1RB0RD_0RC1LB_1LA1RD_1RC0LB : srun tm false true chi_1RB0RD_0RC1LB_1LA1RD_1RC0LB A0_1RB0RD_0RC1LB_1LA1RD_1RC0LB = Some (A1_1RB0RD_0RC1LB_1LA1RD_1RC0LB, 4, 4).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB0RD_0RC1LB_1LA1RD_1RC0LB : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_1RB0RD_0RC1LB_1LA1RD_1RC0LB : sconf := mkC StB (mkS [] [S1;S1] 1 1 [S1]) S0 (mkS [] [] 0 0 []).
Definition cho_1RB0RD_0RC1LB_1LA1RD_1RC0LB : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 9; SCycR 2; SWin 1; SRotL 1; SFoldL 1].

Lemma run_ovf_1RB0RD_0RC1LB_1LA1RD_1RC0LB : srun tm true true cho_1RB0RD_0RC1LB_1LA1RD_1RC0LB B0_1RB0RD_0RC1LB_1LA1RD_1RC0LB = Some (B1_1RB0RD_0RC1LB_1LA1RD_1RC0LB, 4, 12).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_1RB0RD_0RC1LB_1LA1RD_1RC0LB : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Jp q0 ++ [S0]) [] j A0_1RB0RD_0RC1LB_1LA1RD_1RC0LB.
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (H1 & _).
  unfold Cc_1RB0RD_0RC1LB_1LA1RD_1RC0LB, cden, A0_1RB0RD_0RC1LB_1LA1RD_1RC0LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1, <- (app_assoc (rep [S1;S0] j)). reflexivity.
Qed.

Lemma gei_1RB0RD_0RC1LB_1LA1RD_1RC0LB : forall p j q0, cview p = (j, Some q0) ->
  cden (Jp q0 ++ [S0]) [] j A1_1RB0RD_0RC1LB_1LA1RD_1RC0LB = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (_ & H2).
  unfold Cc_1RB0RD_0RC1LB_1LA1RD_1RC0LB, cden, A1_1RB0RD_0RC1LB_1LA1RD_1RC0LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2, <- (app_assoc (rep [S1;S1] j)). reflexivity.
Qed.

Lemma gso_1RB0RD_0RC1LB_1LA1RD_1RC0LB : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_1RB0RD_0RC1LB_1LA1RD_1RC0LB.
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (H1 & _).
  unfold Cc_1RB0RD_0RC1LB_1LA1RD_1RC0LB, cden, B0_1RB0RD_0RC1LB_1LA1RD_1RC0LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1, <- (app_assoc (rep [S1;S0] (j))). reflexivity.
Qed.

Lemma lbl_1RB0RD_0RC1LB_1LA1RD_1RC0LB : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB0RD_0RC1LB_1LA1RD_1RC0LB : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB0RD_0RC1LB_1LA1RD_1RC0LB) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB0RD_0RC1LB_1LA1RD_1RC0LB
             = (StB, (rep [S1;S1] (S j) ++ [S1], S0, []))).
  { unfold cden, B1_1RB0RD_0RC1LB_1LA1RD_1RC0LB, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. reflexivity. }
  assert (HC : Cc (Pos.succ p) = (StB, ((rep [S1;S1] (S j) ++ [S1]) ++ [S0], S0, []))).
  { unfold Cc_1RB0RD_0RC1LB_1LA1RD_1RC0LB. rewrite H2. rewrite <- !app_assoc. reflexivity. }
  rewrite HD, HC. rewrite !lbl_1RB0RD_0RC1LB_1LA1RD_1RC0LB. reflexivity.
Qed.

(** ** The lap *)

Lemma lapi_1RB0RD_0RC1LB_1LA1RD_1RC0LB : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (4 * j + 4). split; [lia|].
  rewrite (gsi_1RB0RD_0RC1LB_1LA1RD_1RC0LB p j q0 E).
  rewrite (srun_sound tm false true chi_1RB0RD_0RC1LB_1LA1RD_1RC0LB A0_1RB0RD_0RC1LB_1LA1RD_1RC0LB A1_1RB0RD_0RC1LB_1LA1RD_1RC0LB 4 4
             run_int_1RB0RD_0RC1LB_1LA1RD_1RC0LB (Jp q0 ++ [S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_1RB0RD_0RC1LB_1LA1RD_1RC0LB p j q0 E).
Qed.

Lemma lap_1RB0RD_0RC1LB_1LA1RD_1RC0LB : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB0RD_0RC1LB_1LA1RD_1RC0LB p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_1RB0RD_0RC1LB_1LA1RD_1RC0LB B0_1RB0RD_0RC1LB_1LA1RD_1RC0LB B1_1RB0RD_0RC1LB_1LA1RD_1RC0LB 4 12 p j' [] []).
    + exact run_ovf_1RB0RD_0RC1LB_1LA1RD_1RC0LB.
    + reflexivity.
    + reflexivity.
    + exact (gso_1RB0RD_0RC1LB_1LA1RD_1RC0LB p j' E).
    + exact (geo_1RB0RD_0RC1LB_1LA1RD_1RC0LB p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_1RB0RD_0RC1LB_1LA1RD_1RC0LB : exists t0, stepn tm t0 InitES = Some (lift (Cc 2)).
Proof.
  exists 7.
  assert (H : match csteps tm 7 c0 with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 7 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma viso_1RB0RD_0RC1LB_1LA1RD_1RC0LB : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_1RB0RD_0RC1LB_1LA1RD_1RC0LB = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_1RB0RD_0RC1LB_1LA1RD_1RC0LB p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB0RD_0RC1LB_1LA1RD_1RC0LB p j E)].
Qed.

Lemma vis_1RB0RD_0RC1LB_1LA1RD_1RC0LB : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_1RB0RD_0RC1LB_1LA1RD_1RC0LB.
  destruct q.

  - (* StA *)
    apply (vis_via_ovf tm Cc Hi StA), viso_1RB0RD_0RC1LB_1LA1RD_1RC0LB
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 2]).
    vm_compute; reflexivity.
  - (* StB: the anchor state *)
    exists 0. eexists. split; reflexivity.
  - (* StC *)
    apply (vis_via_ovf tm Cc Hi StC), viso_1RB0RD_0RC1LB_1LA1RD_1RC0LB
      with (l := [SRotL 1; SWin 1]).
    vm_compute; reflexivity.
  - (* StD *)
    apply (vis_via_ovf tm Cc Hi StD), viso_1RB0RD_0RC1LB_1LA1RD_1RC0LB
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 1]).
    vm_compute; reflexivity.
Qed.

Theorem nqhm_1RB0RD_0RC1LB_1LA1RD_1RC0LB : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 2). - exact boot_1RB0RD_0RC1LB_1LA1RD_1RC0LB. - intros p _. apply lap_1RB0RD_0RC1LB_1LA1RD_1RC0LB. - intros p q _. apply vis_1RB0RD_0RC1LB_1LA1RD_1RC0LB. Qed.

Theorem nqh_1RB0RD_0RC1LB_1LA1RD_1RC0LB : NeverQuasiHaltsSt tm_1RB0RD_0RC1LB_1LA1RD_1RC0LB.
Proof. apply (mirror_never_qh tm_1RB0RD_0RC1LB_1LA1RD_1RC0LB). rewrite mirror_ok_1RB0RD_0RC1LB_1LA1RD_1RC0LB. exact nqhm_1RB0RD_0RC1LB_1LA1RD_1RC0LB. Qed.

Theorem nonhalt_1RB0RD_0RC1LB_1LA1RD_1RC0LB : NonHalt tm_1RB0RD_0RC1LB_1LA1RD_1RC0LB.
Proof. apply never_qh_nonhalt, nqh_1RB0RD_0RC1LB_1LA1RD_1RC0LB. Qed.
