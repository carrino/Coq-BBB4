(** * PEEL_1RB0RB_0LC1RB_1LC1LD_1LA0RA: machine 1RB0RB_0LC1RB_1LC1LD_1LA0RA, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Ap_Alph_11_00_1 digit alphabet (Alph_11_00_1.v), anchored at

      Cc p = (StB, (Ap_Alph_11_00_1 p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  j=0: 4 ; j=S j': 4*j'+8 steps
      overflow  (cview p = (S j, None)):   4*j+10 steps at j = S j', 6 at p = 1

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 199 anchors (overflow PEELED at j = S j', p = 1 concrete).
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter Alph_11_00_1 LapCertGlue IXPGadgets.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_1RB0RB_0LC1RB_1LC1LD_1LA0RA (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB0RB_0LC1RB_1LC1LD_1LA0RA.

(** 1RB0RB_0LC1RB_1LC1LD_1LA0RA *)
Definition tm_1RB0RB_0LC1RB_1LC1LD_1LA0RA : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DR StB
  | StB, S0 => mk S0 DL StC | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S1 DL StC | StC, S1 => mk S1 DL StD
  | StD, S0 => mk S1 DL StA | StD, S1 => mk S0 DR StA end.
Local Notation tm := tm_1RB0RB_0LC1RB_1LC1LD_1LA0RA.

Definition Cc_1RB0RB_0LC1RB_1LC1LD_1LA0RA (p : positive) : cconf := (StB, (Ap_Alph_11_00_1 p ++ [S0], S0, [])).
Local Notation Cc := Cc_1RB0RB_0LC1RB_1LC1LD_1LA0RA.

(** ** The certificate *)

(** j = 0: the repeated block is absent, so the whole lap is concrete. *)
Definition Z0_1RB0RB_0LC1RB_1LC1LD_1LA0RA : sconf := mkC StB (mkS [S1;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition Z1_1RB0RB_0LC1RB_1LC1LD_1LA0RA : sconf := mkC StB (mkS [S0;S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition chz_1RB0RB_0LC1RB_1LC1LD_1LA0RA : list lstep := [SWin 4].

Lemma run_z_1RB0RB_0LC1RB_1LC1LD_1LA0RA : srun tm false true chz_1RB0RB_0LC1RB_1LC1LD_1LA0RA Z0_1RB0RB_0LC1RB_1LC1LD_1LA0RA = Some (Z1_1RB0RB_0LC1RB_1LC1LD_1LA0RA, 0, 4).
Proof. vm_compute. reflexivity. Qed.

(** j = S j': one copy of the unit sits in the PREFIX, so the head always has
    a concrete cell to step onto. *)
Definition P0_1RB0RB_0LC1RB_1LC1LD_1LA0RA : sconf := mkC StB (mkS [S0;S0] [S0;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition P1_1RB0RB_0LC1RB_1LC1LD_1LA0RA : sconf := mkC StB (mkS [S1;S1] [S1;S1] 1 0 [S0;S0]) S0 (mkS [] [] 0 0 []).
Definition chp_1RB0RB_0LC1RB_1LC1LD_1LA0RA : list lstep := [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 2].

Lemma run_p_1RB0RB_0LC1RB_1LC1LD_1LA0RA : srun tm false true chp_1RB0RB_0LC1RB_1LC1LD_1LA0RA P0_1RB0RB_0LC1RB_1LC1LD_1LA0RA = Some (P1_1RB0RB_0LC1RB_1LC1LD_1LA0RA, 4, 8).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB0RB_0LC1RB_1LC1LD_1LA0RA : sconf := mkC StB (mkS [S0;S0] [S0;S0] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_1RB0RB_0LC1RB_1LC1LD_1LA0RA : sconf := mkC StB (mkS [S1;S1] [S1;S1] 1 1 [S1]) S0 (mkS [] [] 0 0 []).
Definition cho_1RB0RB_0LC1RB_1LC1LD_1LA0RA : list lstep := [SWin 2; SCycL 2 0; SWin 2; SWinL 4; SCycR 2; SWin 2; SRotL 2; SFoldL 1].

Lemma run_ovf_1RB0RB_0LC1RB_1LC1LD_1LA0RA : srun tm true true cho_1RB0RB_0LC1RB_1LC1LD_1LA0RA B0_1RB0RB_0LC1RB_1LC1LD_1LA0RA = Some (B1_1RB0RB_0LC1RB_1LC1LD_1LA0RA, 4, 10).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gz_1RB0RB_0LC1RB_1LC1LD_1LA0RA : forall p q0, cview p = (0, Some q0) ->
  Cc p = cden (Ap_Alph_11_00_1 q0 ++ [S0]) [] 0 Z0_1RB0RB_0LC1RB_1LC1LD_1LA0RA /\
  cden (Ap_Alph_11_00_1 q0 ++ [S0]) [] 0 Z1_1RB0RB_0LC1RB_1LC1LD_1LA0RA = Cc (Pos.succ p).
Proof.
  intros p q0 E. destruct (Alph_11_00_1.cview_some_Alph_11_00_1 p 0 q0 E) as (H1 & H2).
  unfold Cc_1RB0RB_0LC1RB_1LC1LD_1LA0RA, cden, Z0_1RB0RB_0LC1RB_1LC1LD_1LA0RA, Z1_1RB0RB_0LC1RB_1LC1LD_1LA0RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gp_1RB0RB_0LC1RB_1LC1LD_1LA0RA : forall p j q0, cview p = (S j, Some q0) ->
  Cc p = cden (Ap_Alph_11_00_1 q0 ++ [S0]) [] j P0_1RB0RB_0LC1RB_1LC1LD_1LA0RA /\
  cden (Ap_Alph_11_00_1 q0 ++ [S0]) [] j P1_1RB0RB_0LC1RB_1LC1LD_1LA0RA = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (Alph_11_00_1.cview_some_Alph_11_00_1 p (S j) q0 E) as (H1 & H2).
  unfold Cc_1RB0RB_0LC1RB_1LC1LD_1LA0RA, cden, P0_1RB0RB_0LC1RB_1LC1LD_1LA0RA, P1_1RB0RB_0LC1RB_1LC1LD_1LA0RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB0RB_0LC1RB_1LC1LD_1LA0RA : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct j as [|j'].
  - destruct (gz_1RB0RB_0LC1RB_1LC1LD_1LA0RA p q0 E) as (HA & HB).
    exists (0 * 0 + 4). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chz_1RB0RB_0LC1RB_1LC1LD_1LA0RA Z0_1RB0RB_0LC1RB_1LC1LD_1LA0RA Z1_1RB0RB_0LC1RB_1LC1LD_1LA0RA 0 4
               run_z_1RB0RB_0LC1RB_1LC1LD_1LA0RA (Ap_Alph_11_00_1 q0 ++ [S0]) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gp_1RB0RB_0LC1RB_1LC1LD_1LA0RA p j' q0 E) as (HA & HB).
    exists (4 * j' + 8). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chp_1RB0RB_0LC1RB_1LC1LD_1LA0RA P0_1RB0RB_0LC1RB_1LC1LD_1LA0RA P1_1RB0RB_0LC1RB_1LC1LD_1LA0RA 4 8
               run_p_1RB0RB_0LC1RB_1LC1LD_1LA0RA (Ap_Alph_11_00_1 q0 ++ [S0]) [] j'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
Qed.

Lemma gso_1RB0RB_0LC1RB_1LC1LD_1LA0RA : forall p j, cview p = (S (S j), None) ->
  Cc p = cden [] [] j B0_1RB0RB_0LC1RB_1LC1LD_1LA0RA.
Proof.
  intros p j E. destruct (Alph_11_00_1.cview_none_Alph_11_00_1 p (S j) E) as (H1 & _).
  unfold Cc_1RB0RB_0LC1RB_1LC1LD_1LA0RA, cden, B0_1RB0RB_0LC1RB_1LC1LD_1LA0RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB0RB_0LC1RB_1LC1LD_1LA0RA : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB0RB_0LC1RB_1LC1LD_1LA0RA : forall p j, cview p = (S (S j), None) ->
  lift (cden [] [] j B1_1RB0RB_0LC1RB_1LC1LD_1LA0RA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (Alph_11_00_1.cview_none_Alph_11_00_1 p (S j) E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB0RB_0LC1RB_1LC1LD_1LA0RA
             = (StB, (rep [S1;S1] (S (S j)) ++ [S1], S0, []))).
  { unfold cden, B1_1RB0RB_0LC1RB_1LC1LD_1LA0RA, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StB, ((rep [S1;S1] (S (S j)) ++ [S1]) ++ [S0], S0, []))).
  { unfold Cc_1RB0RB_0LC1RB_1LC1LD_1LA0RA. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_1RB0RB_0LC1RB_1LC1LD_1LA0RA. reflexivity.
Qed.

(** The smallest overflow anchor, [p = 1]: one concrete run.  The peeled
    branch below states its chain at [j = S j'], so this case is what the
    reindex leaves behind -- the [j = 0] device of the offset route, at the
    OUTER anchor. *)
Lemma lapz_1RB0RB_0LC1RB_1LC1LD_1LA0RA : exists n c', csteps tm n (Cc 1) = Some c'
  /\ lift c' = lift (Cc 2) /\ 0 < n.
Proof.
  exists 6.
  assert (H : match csteps tm 6 (Cc 1) with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 6 (Cc 1)) as [c|] eqn:Ez; [|discriminate].
  exists c. split; [reflexivity|]. split; [apply ceqb_lift; exact H | lia].
Qed.

(** State StA's visit witness at the peeled branch's [p = 1] case. *)
Lemma visz_StA_1RB0RB_0LC1RB_1LC1LD_1LA0RA : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StA.
Proof. exists 3. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StC's visit witness at the peeled branch's [p = 1] case. *)
Lemma visz_StC_1RB0RB_0LC1RB_1LC1LD_1LA0RA : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StC.
Proof. exists 1. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StD's visit witness at the peeled branch's [p = 1] case. *)
Lemma visz_StD_1RB0RB_0LC1RB_1LC1LD_1LA0RA : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StD.
Proof. exists 2. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** ** The lap *)

Lemma lap_1RB0RB_0LC1RB_1LC1LD_1LA0RA : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB0RB_0LC1RB_1LC1LD_1LA0RA p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    destruct j' as [|j''].
    + rewrite (cview_none_shape p 0 E). exact lapz_1RB0RB_0LC1RB_1LC1LD_1LA0RA.
    + apply (lap_of_run tm Cc true true cho_1RB0RB_0LC1RB_1LC1LD_1LA0RA B0_1RB0RB_0LC1RB_1LC1LD_1LA0RA B1_1RB0RB_0LC1RB_1LC1LD_1LA0RA 4 10 p j'' [] []).
      * exact run_ovf_1RB0RB_0LC1RB_1LC1LD_1LA0RA.
      * reflexivity.
      * reflexivity.
      * exact (gso_1RB0RB_0LC1RB_1LC1LD_1LA0RA p j'' E).
      * exact (geo_1RB0RB_0LC1RB_1LC1LD_1LA0RA p j'' E).
      * lia.
Qed.

(** ** Bootstrap *)

Lemma boot_1RB0RB_0LC1RB_1LC1LD_1LA0RA : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 1.
  assert (H : match csteps tm 1 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 1 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma viso_1RB0RB_0LC1RB_1LC1LD_1LA0RA : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_1RB0RB_0LC1RB_1LC1LD_1LA0RA = Some q ->
  forall p j, cview p = (S (S j), None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_1RB0RB_0LC1RB_1LC1LD_1LA0RA p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB0RB_0LC1RB_1LC1LD_1LA0RA p j E)].
Qed.

Lemma vis_1RB0RB_0LC1RB_1LC1LD_1LA0RA : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_1RB0RB_0LC1RB_1LC1LD_1LA0RA.
  destruct q.

  - (* StA *)
    apply (vis_via_ovf tm Cc Hi StA).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1). exact visz_StA_1RB0RB_0LC1RB_1LC1LD_1LA0RA.
    + exact (viso_1RB0RB_0LC1RB_1LC1LD_1LA0RA [SWin 2; SCycL 2 0; SWin 2; SWinL 1] StA ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* StB: the anchor state *)
    exists 0. eexists. split; reflexivity.
  - (* StC *)
    apply (vis_via_ovf tm Cc Hi StC).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1). exact visz_StC_1RB0RB_0LC1RB_1LC1LD_1LA0RA.
    + exact (viso_1RB0RB_0LC1RB_1LC1LD_1LA0RA [SWin 1] StC ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* StD *)
    apply (vis_via_ovf tm Cc Hi StD).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1). exact visz_StD_1RB0RB_0LC1RB_1LC1LD_1LA0RA.
    + exact (viso_1RB0RB_0LC1RB_1LC1LD_1LA0RA [SWin 2; SCycL 2 0; SWin 2] StD ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
Qed.

Theorem nqh_1RB0RB_0LC1RB_1LC1LD_1LA0RA : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 1). - exact boot_1RB0RB_0LC1RB_1LC1LD_1LA0RA. - intros p _. apply lap_1RB0RB_0LC1RB_1LC1LD_1LA0RA. - intros p q _. apply vis_1RB0RB_0LC1RB_1LC1LD_1LA0RA. Qed.

Theorem nonhalt_1RB0RB_0LC1RB_1LC1LD_1LA0RA : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_1RB0RB_0LC1RB_1LC1LD_1LA0RA. Qed.
