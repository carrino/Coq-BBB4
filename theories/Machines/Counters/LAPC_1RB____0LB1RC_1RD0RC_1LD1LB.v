(** * LAPC_1RB____0LB1RC_1RD0RC_1LD1LB: machine 1RB---_0LB1RC_1RD0RC_1LD1LB, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Dp digit alphabet (DpCounter.v), anchored at

      Cc p = (StB, (Dp p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  4*j+12 steps
      overflow  (cview p = (S j, None)):   4*j+16 steps

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
                                  JpCounter DpCounter LapCertGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_1RB____0LB1RC_1RD0RC_1LD1LB (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB____0LB1RC_1RD0RC_1LD1LB.

(** 1RB---_0LB1RC_1RD0RC_1LD1LB *)
(** 1RB---_0LB1RC_1RD0RC_1LD1LB -- the real machine (its counter grows RIGHT). *)
Definition tm_1RB____0LB1RC_1RD0RC_1LD1LB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => None
  | StB, S0 => mk S0 DL StB | StB, S1 => mk S1 DR StC
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S0 DR StC
  | StD, S0 => mk S1 DL StD | StD, S1 => mk S1 DL StB end.

(** Its mirror 1LB---_0RB1LC_1LD0LC_1RD1RB: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_1RB____0LB1RC_1RD0RC_1LD1LB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => None
  | StB, S0 => mk S0 DR StB | StB, S1 => mk S1 DL StC
  | StC, S0 => mk S1 DL StD | StC, S1 => mk S0 DL StC
  | StD, S0 => mk S1 DR StD | StD, S1 => mk S1 DR StB end.
Local Notation tm := tmm_1RB____0LB1RC_1RD0RC_1LD1LB.

Lemma mirror_ok_1RB____0LB1RC_1RD0RC_1LD1LB : mirror_tm tm_1RB____0LB1RC_1RD0RC_1LD1LB = tmm_1RB____0LB1RC_1RD0RC_1LD1LB.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_1RB____0LB1RC_1RD0RC_1LD1LB (p : positive) : cconf := (StB, (Dp p ++ [S0], S0, [S0;S1])).
Local Notation Cc := Cc_1RB____0LB1RC_1RD0RC_1LD1LB.

(** ** The certificate *)

Definition A0_1RB____0LB1RC_1RD0RC_1LD1LB : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S0;S0]) S0 (mkS [S0;S1] [] 0 0 []).
Definition A1_1RB____0LB1RC_1RD0RC_1LD1LB : sconf := mkC StB (mkS [] [S0;S0] 1 0 [S1;S1]) S0 (mkS [S0;S1] [] 0 0 []).
Definition chi_1RB____0LB1RC_1RD0RC_1LD1LB : list lstep := [SWin 8; SCycL 2 0; SWin 4; SCycR 2].

Lemma run_int_1RB____0LB1RC_1RD0RC_1LD1LB : srun tm false true chi_1RB____0LB1RC_1RD0RC_1LD1LB A0_1RB____0LB1RC_1RD0RC_1LD1LB = Some (A1_1RB____0LB1RC_1RD0RC_1LD1LB, 4, 12).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB____0LB1RC_1RD0RC_1LD1LB : sconf := mkC StB (mkS [S1;S1] [S1;S1] 1 0 [S0]) S0 (mkS [S0;S1] [] 0 0 []).
Definition B1_1RB____0LB1RC_1RD0RC_1LD1LB : sconf := mkC StB (mkS [] [S0;S0] 1 1 [S1;S1]) S0 (mkS [S0;S1] [] 0 0 []).
Definition cho_1RB____0LB1RC_1RD0RC_1LD1LB : list lstep := [SWin 10; SCycL 2 0; SWin 1; SWinL 3; SCycR 2; SWin 2; SFoldL 1].

Lemma run_ovf_1RB____0LB1RC_1RD0RC_1LD1LB : srun tm true true cho_1RB____0LB1RC_1RD0RC_1LD1LB B0_1RB____0LB1RC_1RD0RC_1LD1LB = Some (B1_1RB____0LB1RC_1RD0RC_1LD1LB, 4, 16).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_1RB____0LB1RC_1RD0RC_1LD1LB : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Dp q0 ++ [S0]) [] j A0_1RB____0LB1RC_1RD0RC_1LD1LB.
Proof.
  intros p j q0 E. destruct (DpCounter.cview_some_D p j q0 E) as (H1 & _).
  unfold Cc_1RB____0LB1RC_1RD0RC_1LD1LB, cden, A0_1RB____0LB1RC_1RD0RC_1LD1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gei_1RB____0LB1RC_1RD0RC_1LD1LB : forall p j q0, cview p = (j, Some q0) ->
  cden (Dp q0 ++ [S0]) [] j A1_1RB____0LB1RC_1RD0RC_1LD1LB = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (DpCounter.cview_some_D p j q0 E) as (_ & H2).
  unfold Cc_1RB____0LB1RC_1RD0RC_1LD1LB, cden, A1_1RB____0LB1RC_1RD0RC_1LD1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S0;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB____0LB1RC_1RD0RC_1LD1LB : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (4 * j + 12). split; [lia|].
  rewrite (gsi_1RB____0LB1RC_1RD0RC_1LD1LB p j q0 E).
  rewrite (srun_sound tm false true chi_1RB____0LB1RC_1RD0RC_1LD1LB A0_1RB____0LB1RC_1RD0RC_1LD1LB A1_1RB____0LB1RC_1RD0RC_1LD1LB 4 12
             run_int_1RB____0LB1RC_1RD0RC_1LD1LB (Dp q0 ++ [S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_1RB____0LB1RC_1RD0RC_1LD1LB p j q0 E).
Qed.

Lemma gso_1RB____0LB1RC_1RD0RC_1LD1LB : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_1RB____0LB1RC_1RD0RC_1LD1LB.
Proof.
  intros p j E. destruct (DpCounter.cview_none_D p j E) as (H1 & _).
  unfold Cc_1RB____0LB1RC_1RD0RC_1LD1LB, cden, B0_1RB____0LB1RC_1RD0RC_1LD1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB____0LB1RC_1RD0RC_1LD1LB : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB____0LB1RC_1RD0RC_1LD1LB : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB____0LB1RC_1RD0RC_1LD1LB) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (DpCounter.cview_none_D p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB____0LB1RC_1RD0RC_1LD1LB
             = (StB, (rep [S0;S0] (S j) ++ [S1;S1], S0, [S0;S1]))).
  { unfold cden, B1_1RB____0LB1RC_1RD0RC_1LD1LB, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. reflexivity. }
  assert (HC : Cc (Pos.succ p) = (StB, ((rep [S0;S0] (S j) ++ [S1;S1]) ++ [S0], S0, [S0;S1]))).
  { unfold Cc_1RB____0LB1RC_1RD0RC_1LD1LB. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_1RB____0LB1RC_1RD0RC_1LD1LB. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_1RB____0LB1RC_1RD0RC_1LD1LB : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB____0LB1RC_1RD0RC_1LD1LB p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_1RB____0LB1RC_1RD0RC_1LD1LB B0_1RB____0LB1RC_1RD0RC_1LD1LB B1_1RB____0LB1RC_1RD0RC_1LD1LB 4 16 p j' [] []).
    + exact run_ovf_1RB____0LB1RC_1RD0RC_1LD1LB.
    + reflexivity.
    + reflexivity.
    + exact (gso_1RB____0LB1RC_1RD0RC_1LD1LB p j' E).
    + exact (geo_1RB____0LB1RC_1RD0RC_1LD1LB p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_1RB____0LB1RC_1RD0RC_1LD1LB : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 12.
  assert (H : match csteps tm 12 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 12 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma viso_1RB____0LB1RC_1RD0RC_1LD1LB : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_1RB____0LB1RC_1RD0RC_1LD1LB = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_1RB____0LB1RC_1RD0RC_1LD1LB p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB____0LB1RC_1RD0RC_1LD1LB p j E)].
Qed.

Lemma vis_1RB____0LB1RC_1RD0RC_1LD1LB : forall p q, q <> StA -> exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q Hq.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_1RB____0LB1RC_1RD0RC_1LD1LB.
  destruct q.
  - (* StA: quiet -- see the closing theorem *)
    exfalso; exact (Hq eq_refl).
  - (* StB: the anchor state *)
    exists 0. eexists. split; reflexivity.
  - (* StC *)
    apply (vis_via_ovf tm Cc Hi StC), viso_1RB____0LB1RC_1RD0RC_1LD1LB
      with (l := [SWin 3]).
    vm_compute; reflexivity.
  - (* StD *)
    apply (vis_via_ovf tm Cc Hi StD), viso_1RB____0LB1RC_1RD0RC_1LD1LB
      with (l := [SWin 4]).
    vm_compute; reflexivity.
Qed.

(** StA is TARGETED BY NOTHING, so its only visit is at configuration index
    0 and the quiet bound is 1 -- weakened to the census tier's 2000. *)
Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.

Theorem iqhm_1RB____0LB1RC_1RD0RC_1LD1LB : iqh tmm_1RB____0LB1RC_1RD0RC_1LD1LB.
Proof.
  destruct (glue_qh tm Cc 1 boot_1RB____0LB1RC_1RD0RC_1LD1LB (fun p _ => lap_1RB____0LB1RC_1RD0RC_1LD1LB p)
                    (fun p q _ Hq => vis_1RB____0LB1RC_1RD0RC_1LD1LB p q Hq)
                    (ltac:(intros q b tr Ht; destruct q, b; cbn in Ht;
                           try discriminate; injection Ht as <-; discriminate)))
    as (Hn & Hb & Hq).
  split; [exact Hn | split; [| exact Hq]].
  apply (qhbound_mono 1 2000); [lia | exact Hb].
Qed.

(** Transfer to the REAL machine.  [mirror_nonhalt] and [mirror_qh]
    are Mirror.v; [qhbound_mirror] is Census/TNF_QH.v. *)
Theorem iqh_1RB____0LB1RC_1RD0RC_1LD1LB : iqh tm_1RB____0LB1RC_1RD0RC_1LD1LB.
Proof.
  destruct iqhm_1RB____0LB1RC_1RD0RC_1LD1LB as (Hn & Hb & Hq).
  rewrite <- mirror_ok_1RB____0LB1RC_1RD0RC_1LD1LB in Hn, Hb, Hq.
  split; [exact (mirror_nonhalt _ Hn)
         | split; [exact (qhbound_mirror _ _ Hb)
                  | exact (mirror_qh _ Hq)]].
Qed.

Theorem nonhalt_1RB____0LB1RC_1RD0RC_1LD1LB : NonHalt tm_1RB____0LB1RC_1RD0RC_1LD1LB.
Proof. apply (proj1 iqh_1RB____0LB1RC_1RD0RC_1LD1LB). Qed.
