(** * LAPC_1RB____0LB1RC_1LB0RD_1LB0RD: machine 1RB---_0LB1RC_1LB0RD_1LB0RD, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Kp digit alphabet (KpCounter.v), anchored at

      Cc p = (StB, (Kp p ++ [S0], S0, []))

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
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH MonoCounter
                                  JpCounter KpCounter LapCertGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_1RB____0LB1RC_1LB0RD_1LB0RD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB____0LB1RC_1LB0RD_1LB0RD.

(** 1RB---_0LB1RC_1LB0RD_1LB0RD *)
(** 1RB---_0LB1RC_1LB0RD_1LB0RD -- the real machine (its counter grows RIGHT). *)
Definition tm_1RB____0LB1RC_1LB0RD_1LB0RD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => None
  | StB, S0 => mk S0 DL StB | StB, S1 => mk S1 DR StC
  | StC, S0 => mk S1 DL StB | StC, S1 => mk S0 DR StD
  | StD, S0 => mk S1 DL StB | StD, S1 => mk S0 DR StD end.

(** Its mirror 1LB---_0RB1LC_1RB0LD_1RB0LD: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_1RB____0LB1RC_1LB0RD_1LB0RD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => None
  | StB, S0 => mk S0 DR StB | StB, S1 => mk S1 DL StC
  | StC, S0 => mk S1 DR StB | StC, S1 => mk S0 DL StD
  | StD, S0 => mk S1 DR StB | StD, S1 => mk S0 DL StD end.
Local Notation tm := tmm_1RB____0LB1RC_1LB0RD_1LB0RD.

Lemma mirror_ok_1RB____0LB1RC_1LB0RD_1LB0RD : mirror_tm tm_1RB____0LB1RC_1LB0RD_1LB0RD = tmm_1RB____0LB1RC_1LB0RD_1LB0RD.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_1RB____0LB1RC_1LB0RD_1LB0RD (p : positive) : cconf := (StB, (Kp p ++ [S0], S0, [S1])).
Local Notation Cc := Cc_1RB____0LB1RC_1LB0RD_1LB0RD.

(** ** The certificate *)

(** j = 0: the repeated block is absent, so the whole lap is concrete. *)
Definition Z0_1RB____0LB1RC_1LB0RD_1LB0RD : sconf := mkC StB (mkS [S0] [] 0 0 []) S0 (mkS [S1] [] 0 0 []).
Definition Z1_1RB____0LB1RC_1LB0RD_1LB0RD : sconf := mkC StB (mkS [S1] [] 0 0 []) S0 (mkS [S1] [] 0 0 []).
Definition chz_1RB____0LB1RC_1LB0RD_1LB0RD : list lstep := [SWin 6].

Lemma run_z_1RB____0LB1RC_1LB0RD_1LB0RD : srun tm false true chz_1RB____0LB1RC_1LB0RD_1LB0RD Z0_1RB____0LB1RC_1LB0RD_1LB0RD = Some (Z1_1RB____0LB1RC_1LB0RD_1LB0RD, 0, 6).
Proof. vm_compute. reflexivity. Qed.

(** j = S j': one copy of the unit sits in the PREFIX, so the head always has
    a concrete cell to step onto. *)
Definition P0_1RB____0LB1RC_1LB0RD_1LB0RD : sconf := mkC StB (mkS [S1] [S1] 1 0 [S0]) S0 (mkS [S1] [] 0 0 []).
Definition P1_1RB____0LB1RC_1LB0RD_1LB0RD : sconf := mkC StB (mkS [S0] [S0] 1 0 [S1]) S0 (mkS [S1] [] 0 0 []).
Definition chp_1RB____0LB1RC_1LB0RD_1LB0RD : list lstep := [SWin 5; SCycL 1 0; SWin 2; SCycR 1; SWin 1].

Lemma run_p_1RB____0LB1RC_1LB0RD_1LB0RD : srun tm false true chp_1RB____0LB1RC_1LB0RD_1LB0RD P0_1RB____0LB1RC_1LB0RD_1LB0RD = Some (P1_1RB____0LB1RC_1LB0RD_1LB0RD, 2, 8).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB____0LB1RC_1LB0RD_1LB0RD : sconf := mkC StB (mkS [S1] [S1] 1 0 [S0]) S0 (mkS [S1] [] 0 0 []).
Definition B1_1RB____0LB1RC_1LB0RD_1LB0RD : sconf := mkC StB (mkS [] [S0] 1 1 [S1]) S0 (mkS [S1] [] 0 0 []).
Definition cho_1RB____0LB1RC_1LB0RD_1LB0RD : list lstep := [SWin 5; SCycL 1 0; SWin 2; SCycR 1; SWin 1; SFoldL 1].

Lemma run_ovf_1RB____0LB1RC_1LB0RD_1LB0RD : srun tm true true cho_1RB____0LB1RC_1LB0RD_1LB0RD B0_1RB____0LB1RC_1LB0RD_1LB0RD = Some (B1_1RB____0LB1RC_1LB0RD_1LB0RD, 2, 8).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gz_1RB____0LB1RC_1LB0RD_1LB0RD : forall p q0, cview p = (0, Some q0) ->
  Cc p = cden (Kp q0 ++ [S0]) [] 0 Z0_1RB____0LB1RC_1LB0RD_1LB0RD /\
  cden (Kp q0 ++ [S0]) [] 0 Z1_1RB____0LB1RC_1LB0RD_1LB0RD = Cc (Pos.succ p).
Proof.
  intros p q0 E. destruct (KpCounter.cview_some_K p 0 q0 E) as (H1 & H2).
  unfold Cc_1RB____0LB1RC_1LB0RD_1LB0RD, cden, Z0_1RB____0LB1RC_1LB0RD_1LB0RD, Z1_1RB____0LB1RC_1LB0RD_1LB0RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gp_1RB____0LB1RC_1LB0RD_1LB0RD : forall p j q0, cview p = (S j, Some q0) ->
  Cc p = cden (Kp q0 ++ [S0]) [] j P0_1RB____0LB1RC_1LB0RD_1LB0RD /\
  cden (Kp q0 ++ [S0]) [] j P1_1RB____0LB1RC_1LB0RD_1LB0RD = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (KpCounter.cview_some_K p (S j) q0 E) as (H1 & H2).
  unfold Cc_1RB____0LB1RC_1LB0RD_1LB0RD, cden, P0_1RB____0LB1RC_1LB0RD_1LB0RD, P1_1RB____0LB1RC_1LB0RD_1LB0RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB____0LB1RC_1LB0RD_1LB0RD : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct j as [|j'].
  - destruct (gz_1RB____0LB1RC_1LB0RD_1LB0RD p q0 E) as (HA & HB).
    exists (0 * 0 + 6). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chz_1RB____0LB1RC_1LB0RD_1LB0RD Z0_1RB____0LB1RC_1LB0RD_1LB0RD Z1_1RB____0LB1RC_1LB0RD_1LB0RD 0 6
               run_z_1RB____0LB1RC_1LB0RD_1LB0RD (Kp q0 ++ [S0]) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gp_1RB____0LB1RC_1LB0RD_1LB0RD p j' q0 E) as (HA & HB).
    exists (2 * j' + 8). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chp_1RB____0LB1RC_1LB0RD_1LB0RD P0_1RB____0LB1RC_1LB0RD_1LB0RD P1_1RB____0LB1RC_1LB0RD_1LB0RD 2 8
               run_p_1RB____0LB1RC_1LB0RD_1LB0RD (Kp q0 ++ [S0]) [] j'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
Qed.

Lemma gso_1RB____0LB1RC_1LB0RD_1LB0RD : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_1RB____0LB1RC_1LB0RD_1LB0RD.
Proof.
  intros p j E. destruct (KpCounter.cview_none_K p j E) as (H1 & _).
  unfold Cc_1RB____0LB1RC_1LB0RD_1LB0RD, cden, B0_1RB____0LB1RC_1LB0RD_1LB0RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB____0LB1RC_1LB0RD_1LB0RD : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB____0LB1RC_1LB0RD_1LB0RD : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB____0LB1RC_1LB0RD_1LB0RD) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (KpCounter.cview_none_K p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB____0LB1RC_1LB0RD_1LB0RD
             = (StB, (rep [S0] (S j) ++ [S1], S0, [S1]))).
  { unfold cden, B1_1RB____0LB1RC_1LB0RD_1LB0RD, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. reflexivity. }
  assert (HC : Cc (Pos.succ p) = (StB, ((rep [S0] (S j) ++ [S1]) ++ [S0], S0, [S1]))).
  { unfold Cc_1RB____0LB1RC_1LB0RD_1LB0RD. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_1RB____0LB1RC_1LB0RD_1LB0RD. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_1RB____0LB1RC_1LB0RD_1LB0RD : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB____0LB1RC_1LB0RD_1LB0RD p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_1RB____0LB1RC_1LB0RD_1LB0RD B0_1RB____0LB1RC_1LB0RD_1LB0RD B1_1RB____0LB1RC_1LB0RD_1LB0RD 2 8 p j' [] []).
    + exact run_ovf_1RB____0LB1RC_1LB0RD_1LB0RD.
    + reflexivity.
    + reflexivity.
    + exact (gso_1RB____0LB1RC_1LB0RD_1LB0RD p j' E).
    + exact (geo_1RB____0LB1RC_1LB0RD_1LB0RD p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_1RB____0LB1RC_1LB0RD_1LB0RD : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
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

Lemma viso_1RB____0LB1RC_1LB0RD_1LB0RD : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_1RB____0LB1RC_1LB0RD_1LB0RD = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_1RB____0LB1RC_1LB0RD_1LB0RD p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB____0LB1RC_1LB0RD_1LB0RD p j E)].
Qed.

Lemma vis_1RB____0LB1RC_1LB0RD_1LB0RD : forall p q, q <> StA -> exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q Hq.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_1RB____0LB1RC_1LB0RD_1LB0RD.
  destruct q.
  - (* StA: quiet -- see the closing theorem *)
    exfalso; exact (Hq eq_refl).
  - (* StB: the anchor state *)
    exists 0. eexists. split; reflexivity.
  - (* StC *)
    apply (vis_via_ovf tm Cc Hi StC), viso_1RB____0LB1RC_1LB0RD_1LB0RD
      with (l := [SWin 2]).
    vm_compute; reflexivity.
  - (* StD *)
    apply (vis_via_ovf tm Cc Hi StD), viso_1RB____0LB1RC_1LB0RD_1LB0RD
      with (l := [SWin 5]).
    vm_compute; reflexivity.
Qed.

(** StA is TARGETED BY NOTHING, so its only visit is at configuration index
    0 and the quiet bound is 1 -- weakened to the census tier's 2000. *)
Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.

Theorem iqhm_1RB____0LB1RC_1LB0RD_1LB0RD : iqh tmm_1RB____0LB1RC_1LB0RD_1LB0RD.
Proof.
  destruct (glue_qh tm Cc 1 boot_1RB____0LB1RC_1LB0RD_1LB0RD (fun p _ => lap_1RB____0LB1RC_1LB0RD_1LB0RD p)
                    (fun p q _ Hq => vis_1RB____0LB1RC_1LB0RD_1LB0RD p q Hq)
                    (ltac:(intros q b tr Ht; destruct q, b; cbn in Ht;
                           try discriminate; injection Ht as <-; discriminate)))
    as (Hn & Hb & Hq).
  split; [exact Hn | split; [| exact Hq]].
  apply (qhbound_mono 1 2000); [lia | exact Hb].
Qed.

(** Transfer to the REAL machine.  [mirror_nonhalt] and [mirror_qh]
    are Mirror.v; [qhbound_mirror] is Census/TNF_QH.v. *)
Theorem iqh_1RB____0LB1RC_1LB0RD_1LB0RD : iqh tm_1RB____0LB1RC_1LB0RD_1LB0RD.
Proof.
  destruct iqhm_1RB____0LB1RC_1LB0RD_1LB0RD as (Hn & Hb & Hq).
  rewrite <- mirror_ok_1RB____0LB1RC_1LB0RD_1LB0RD in Hn, Hb, Hq.
  split; [exact (mirror_nonhalt _ Hn)
         | split; [exact (qhbound_mirror _ _ Hb)
                  | exact (mirror_qh _ Hq)]].
Qed.

Theorem nonhalt_1RB____0LB1RC_1LB0RD_1LB0RD : NonHalt tm_1RB____0LB1RC_1LB0RD_1LB0RD.
Proof. apply (proj1 iqh_1RB____0LB1RC_1LB0RD_1LB0RD). Qed.
