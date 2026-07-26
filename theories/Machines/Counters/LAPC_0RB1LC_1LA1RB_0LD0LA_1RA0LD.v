(** * LAPC_0RB1LC_1LA1RB_0LD0LA_1RA0LD: machine 0RB1LC_1LA1RB_0LD0LA_1RA0LD, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Ip digit alphabet (ILCounter.v), anchored at

      Cc p = (StB, (Ip p ++ [S1;S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  4*j+8 steps
      overflow  (cview p = (S j, None)):   4*j+13 steps

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
                                  JpCounter ILCounter LapCertGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_0RB1LC_1LA1RB_0LD0LA_1RA0LD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB1LC_1LA1RB_0LD0LA_1RA0LD.

(** 0RB1LC_1LA1RB_0LD0LA_1RA0LD *)
(** 0RB1LC_1LA1RB_0LD0LA_1RA0LD -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB1LC_1LA1RB_0LD0LA_1RA0LD : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S1 DL StC
  | StB, S0 => mk S1 DL StA | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S0 DL StD | StC, S1 => mk S0 DL StA
  | StD, S0 => mk S1 DR StA | StD, S1 => mk S0 DL StD end.

(** Its mirror 0LB1RC_1RA1LB_0RD0RA_1LA0RD: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB1LC_1LA1RB_0LD0LA_1RA0LD : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S1 DR StC
  | StB, S0 => mk S1 DR StA | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S0 DR StD | StC, S1 => mk S0 DR StA
  | StD, S0 => mk S1 DL StA | StD, S1 => mk S0 DR StD end.
Local Notation tm := tmm_0RB1LC_1LA1RB_0LD0LA_1RA0LD.

Lemma mirror_ok_0RB1LC_1LA1RB_0LD0LA_1RA0LD : mirror_tm tm_0RB1LC_1LA1RB_0LD0LA_1RA0LD = tmm_0RB1LC_1LA1RB_0LD0LA_1RA0LD.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_0RB1LC_1LA1RB_0LD0LA_1RA0LD (p : positive) : cconf := (StB, (Ip p ++ [S1;S0], S0, [S0;S1])).
Local Notation Cc := Cc_0RB1LC_1LA1RB_0LD0LA_1RA0LD.

(** ** The certificate *)

Definition A0_0RB1LC_1LA1RB_0LD0LA_1RA0LD : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S0;S1] [] 0 0 []).
Definition A1_0RB1LC_1LA1RB_0LD0LA_1RA0LD : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S0;S1] [] 0 0 []).
Definition chi_0RB1LC_1LA1RB_0LD0LA_1RA0LD : list lstep := [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 2].

Lemma run_int_0RB1LC_1LA1RB_0LD0LA_1RA0LD : srun tm false true chi_0RB1LC_1LA1RB_0LD0LA_1RA0LD A0_0RB1LC_1LA1RB_0LD0LA_1RA0LD = Some (A1_0RB1LC_1LA1RB_0LD0LA_1RA0LD, 4, 8).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB1LC_1LA1RB_0LD0LA_1RA0LD : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S1;S0]) S0 (mkS [S0;S1] [] 0 0 []).
Definition B1_0RB1LC_1LA1RB_0LD0LA_1RA0LD : sconf := mkC StB (mkS [] [S1;S0] 1 1 [S1;S1]) S0 (mkS [S0;S1] [] 0 0 []).
Definition cho_0RB1LC_1LA1RB_0LD0LA_1RA0LD : list lstep := [SWin 2; SCycL 2 0; SWin 6; SCycR 2; SWin 2; SWinR 3; SRotL 1; SFoldL 1].

Lemma run_ovf_0RB1LC_1LA1RB_0LD0LA_1RA0LD : srun tm true true cho_0RB1LC_1LA1RB_0LD0LA_1RA0LD B0_0RB1LC_1LA1RB_0LD0LA_1RA0LD = Some (B1_0RB1LC_1LA1RB_0LD0LA_1RA0LD, 4, 13).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_0RB1LC_1LA1RB_0LD0LA_1RA0LD : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Ip q0 ++ [S1;S0]) [] j A0_0RB1LC_1LA1RB_0LD0LA_1RA0LD.
Proof.
  intros p j q0 E. destruct (ILCounter.cview_some_I p j q0 E) as (H1 & _).
  unfold Cc_0RB1LC_1LA1RB_0LD0LA_1RA0LD, cden, A0_0RB1LC_1LA1RB_0LD0LA_1RA0LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1, <- (app_assoc (rep [S1;S1] j)). reflexivity.
Qed.

Lemma gei_0RB1LC_1LA1RB_0LD0LA_1RA0LD : forall p j q0, cview p = (j, Some q0) ->
  cden (Ip q0 ++ [S1;S0]) [] j A1_0RB1LC_1LA1RB_0LD0LA_1RA0LD = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (ILCounter.cview_some_I p j q0 E) as (_ & H2).
  unfold Cc_0RB1LC_1LA1RB_0LD0LA_1RA0LD, cden, A1_0RB1LC_1LA1RB_0LD0LA_1RA0LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2, <- (app_assoc (rep [S1;S0] j)). reflexivity.
Qed.

Lemma gso_0RB1LC_1LA1RB_0LD0LA_1RA0LD : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_0RB1LC_1LA1RB_0LD0LA_1RA0LD.
Proof.
  intros p j E. destruct (ILCounter.cview_none_I p j E) as (H1 & _).
  unfold Cc_0RB1LC_1LA1RB_0LD0LA_1RA0LD, cden, B0_0RB1LC_1LA1RB_0LD0LA_1RA0LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1, <- (app_assoc (rep [S1;S1] (j))). reflexivity.
Qed.

Lemma lbl_0RB1LC_1LA1RB_0LD0LA_1RA0LD : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_0RB1LC_1LA1RB_0LD0LA_1RA0LD : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB1LC_1LA1RB_0LD0LA_1RA0LD) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (ILCounter.cview_none_I p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_0RB1LC_1LA1RB_0LD0LA_1RA0LD
             = (StB, (rep [S1;S0] (S j) ++ [S1;S1], S0, [S0;S1]))).
  { unfold cden, B1_0RB1LC_1LA1RB_0LD0LA_1RA0LD, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. reflexivity. }
  assert (HC : Cc (Pos.succ p) = (StB, ((rep [S1;S0] (S j) ++ [S1;S1]) ++ [S0], S0, [S0;S1]))).
  { unfold Cc_0RB1LC_1LA1RB_0LD0LA_1RA0LD. rewrite H2. rewrite <- !app_assoc. reflexivity. }
  rewrite HD, HC. rewrite !lbl_0RB1LC_1LA1RB_0LD0LA_1RA0LD. reflexivity.
Qed.

(** ** The lap *)

Lemma lapi_0RB1LC_1LA1RB_0LD0LA_1RA0LD : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (4 * j + 8). split; [lia|].
  rewrite (gsi_0RB1LC_1LA1RB_0LD0LA_1RA0LD p j q0 E).
  rewrite (srun_sound tm false true chi_0RB1LC_1LA1RB_0LD0LA_1RA0LD A0_0RB1LC_1LA1RB_0LD0LA_1RA0LD A1_0RB1LC_1LA1RB_0LD0LA_1RA0LD 4 8
             run_int_0RB1LC_1LA1RB_0LD0LA_1RA0LD (Ip q0 ++ [S1;S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_0RB1LC_1LA1RB_0LD0LA_1RA0LD p j q0 E).
Qed.

Lemma lap_0RB1LC_1LA1RB_0LD0LA_1RA0LD : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB1LC_1LA1RB_0LD0LA_1RA0LD p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_0RB1LC_1LA1RB_0LD0LA_1RA0LD B0_0RB1LC_1LA1RB_0LD0LA_1RA0LD B1_0RB1LC_1LA1RB_0LD0LA_1RA0LD 4 13 p j' [] []).
    + exact run_ovf_0RB1LC_1LA1RB_0LD0LA_1RA0LD.
    + reflexivity.
    + reflexivity.
    + exact (gso_0RB1LC_1LA1RB_0LD0LA_1RA0LD p j' E).
    + exact (geo_0RB1LC_1LA1RB_0LD0LA_1RA0LD p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_0RB1LC_1LA1RB_0LD0LA_1RA0LD : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 15.
  assert (H : match csteps tm 15 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 15 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma viso_0RB1LC_1LA1RB_0LD0LA_1RA0LD : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_0RB1LC_1LA1RB_0LD0LA_1RA0LD = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_0RB1LC_1LA1RB_0LD0LA_1RA0LD p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB1LC_1LA1RB_0LD0LA_1RA0LD p j E)].
Qed.

Lemma vis_0RB1LC_1LA1RB_0LD0LA_1RA0LD : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_0RB1LC_1LA1RB_0LD0LA_1RA0LD.
  destruct q.

  - (* StA *)
    apply (vis_via_ovf tm Cc Hi StA), viso_0RB1LC_1LA1RB_0LD0LA_1RA0LD
      with (l := [SWin 1]).
    vm_compute; reflexivity.
  - (* StB: the anchor state *)
    exists 0. eexists. split; reflexivity.
  - (* StC *)
    apply (vis_via_ovf tm Cc Hi StC), viso_0RB1LC_1LA1RB_0LD0LA_1RA0LD
      with (l := [SWin 2; SCycL 2 0; SWin 5]).
    vm_compute; reflexivity.
  - (* StD *)
    apply (vis_via_ovf tm Cc Hi StD), viso_0RB1LC_1LA1RB_0LD0LA_1RA0LD
      with (l := [SWin 2; SCycL 2 0; SWin 6; SCycR 2; SWin 2]).
    vm_compute; reflexivity.
Qed.

Theorem nqhm_0RB1LC_1LA1RB_0LD0LA_1RA0LD : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 1). - exact boot_0RB1LC_1LA1RB_0LD0LA_1RA0LD. - intros p _. apply lap_0RB1LC_1LA1RB_0LD0LA_1RA0LD. - intros p q _. apply vis_0RB1LC_1LA1RB_0LD0LA_1RA0LD. Qed.

Theorem nqh_0RB1LC_1LA1RB_0LD0LA_1RA0LD : NeverQuasiHaltsSt tm_0RB1LC_1LA1RB_0LD0LA_1RA0LD.
Proof. apply (mirror_never_qh tm_0RB1LC_1LA1RB_0LD0LA_1RA0LD). rewrite mirror_ok_0RB1LC_1LA1RB_0LD0LA_1RA0LD. exact nqhm_0RB1LC_1LA1RB_0LD0LA_1RA0LD. Qed.

Theorem nonhalt_0RB1LC_1LA1RB_0LD0LA_1RA0LD : NonHalt tm_0RB1LC_1LA1RB_0LD0LA_1RA0LD.
Proof. apply never_qh_nonhalt, nqh_0RB1LC_1LA1RB_0LD0LA_1RA0LD. Qed.
