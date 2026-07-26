(** * LAPC_1RB0RC_1LA0RA_0LD1RC_1LD1LB: machine 1RB0RC_1LA0RA_0LD1RC_1LD1LB, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Ap_Alph_11_00_001 digit alphabet (Alph_11_00_001.v), anchored at

      Cc p = (StC, (Ap_Alph_11_00_001 p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  j=0: 4 ; j=S j': 4*j'+8 steps
      overflow  (cview p = (S j, None)):   4*j+10 steps

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 198 anchors.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH MonoCounter
                                  JpCounter Alph_11_00_001 LapCertGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_1RB0RC_1LA0RA_0LD1RC_1LD1LB (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB0RC_1LA0RA_0LD1RC_1LD1LB.

(** 1RB0RC_1LA0RA_0LD1RC_1LD1LB *)
Definition tm_1RB0RC_1LA0RA_0LD1RC_1LD1LB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DR StC
  | StB, S0 => mk S1 DL StA | StB, S1 => mk S0 DR StA
  | StC, S0 => mk S0 DL StD | StC, S1 => mk S1 DR StC
  | StD, S0 => mk S1 DL StD | StD, S1 => mk S1 DL StB end.
Local Notation tm := tm_1RB0RC_1LA0RA_0LD1RC_1LD1LB.

Definition Cc_1RB0RC_1LA0RA_0LD1RC_1LD1LB (p : positive) : cconf := (StC, (Ap_Alph_11_00_001 p ++ [S0], S0, [])).
Local Notation Cc := Cc_1RB0RC_1LA0RA_0LD1RC_1LD1LB.

(** ** The certificate *)

(** j = 0: the repeated block is absent, so the whole lap is concrete. *)
Definition Z0_1RB0RC_1LA0RA_0LD1RC_1LD1LB : sconf := mkC StC (mkS [S1;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition Z1_1RB0RC_1LA0RA_0LD1RC_1LD1LB : sconf := mkC StC (mkS [S0;S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition chz_1RB0RC_1LA0RA_0LD1RC_1LD1LB : list lstep := [SWin 4].

Lemma run_z_1RB0RC_1LA0RA_0LD1RC_1LD1LB : srun tm false true chz_1RB0RC_1LA0RA_0LD1RC_1LD1LB Z0_1RB0RC_1LA0RA_0LD1RC_1LD1LB = Some (Z1_1RB0RC_1LA0RA_0LD1RC_1LD1LB, 0, 4).
Proof. vm_compute. reflexivity. Qed.

(** j = S j': one copy of the unit sits in the PREFIX, so the head always has
    a concrete cell to step onto. *)
Definition P0_1RB0RC_1LA0RA_0LD1RC_1LD1LB : sconf := mkC StC (mkS [S0;S0] [S0;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition P1_1RB0RC_1LA0RA_0LD1RC_1LD1LB : sconf := mkC StC (mkS [S1;S1] [S1;S1] 1 0 [S0;S0]) S0 (mkS [] [] 0 0 []).
Definition chp_1RB0RC_1LA0RA_0LD1RC_1LD1LB : list lstep := [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 2].

Lemma run_p_1RB0RC_1LA0RA_0LD1RC_1LD1LB : srun tm false true chp_1RB0RC_1LA0RA_0LD1RC_1LD1LB P0_1RB0RC_1LA0RA_0LD1RC_1LD1LB = Some (P1_1RB0RC_1LA0RA_0LD1RC_1LD1LB, 4, 8).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB0RC_1LA0RA_0LD1RC_1LD1LB : sconf := mkC StC (mkS [] [S0;S0] 1 0 [S0;S0;S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_1RB0RC_1LA0RA_0LD1RC_1LD1LB : sconf := mkC StC (mkS [] [S1;S1] 1 1 [S0;S0;S1]) S0 (mkS [] [] 0 0 []).
Definition cho_1RB0RC_1LA0RA_0LD1RC_1LD1LB : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 3; SWinL 5; SCycR 2; SWin 1; SRotL 1; SFoldL 1].

Lemma run_ovf_1RB0RC_1LA0RA_0LD1RC_1LD1LB : srun tm true true cho_1RB0RC_1LA0RA_0LD1RC_1LD1LB B0_1RB0RC_1LA0RA_0LD1RC_1LD1LB = Some (B1_1RB0RC_1LA0RA_0LD1RC_1LD1LB, 4, 10).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gz_1RB0RC_1LA0RA_0LD1RC_1LD1LB : forall p q0, cview p = (0, Some q0) ->
  Cc p = cden (Ap_Alph_11_00_001 q0 ++ [S0]) [] 0 Z0_1RB0RC_1LA0RA_0LD1RC_1LD1LB /\
  cden (Ap_Alph_11_00_001 q0 ++ [S0]) [] 0 Z1_1RB0RC_1LA0RA_0LD1RC_1LD1LB = Cc (Pos.succ p).
Proof.
  intros p q0 E. destruct (Alph_11_00_001.cview_some_Alph_11_00_001 p 0 q0 E) as (H1 & H2).
  unfold Cc_1RB0RC_1LA0RA_0LD1RC_1LD1LB, cden, Z0_1RB0RC_1LA0RA_0LD1RC_1LD1LB, Z1_1RB0RC_1LA0RA_0LD1RC_1LD1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gp_1RB0RC_1LA0RA_0LD1RC_1LD1LB : forall p j q0, cview p = (S j, Some q0) ->
  Cc p = cden (Ap_Alph_11_00_001 q0 ++ [S0]) [] j P0_1RB0RC_1LA0RA_0LD1RC_1LD1LB /\
  cden (Ap_Alph_11_00_001 q0 ++ [S0]) [] j P1_1RB0RC_1LA0RA_0LD1RC_1LD1LB = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (Alph_11_00_001.cview_some_Alph_11_00_001 p (S j) q0 E) as (H1 & H2).
  unfold Cc_1RB0RC_1LA0RA_0LD1RC_1LD1LB, cden, P0_1RB0RC_1LA0RA_0LD1RC_1LD1LB, P1_1RB0RC_1LA0RA_0LD1RC_1LD1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB0RC_1LA0RA_0LD1RC_1LD1LB : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct j as [|j'].
  - destruct (gz_1RB0RC_1LA0RA_0LD1RC_1LD1LB p q0 E) as (HA & HB).
    exists (0 * 0 + 4). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chz_1RB0RC_1LA0RA_0LD1RC_1LD1LB Z0_1RB0RC_1LA0RA_0LD1RC_1LD1LB Z1_1RB0RC_1LA0RA_0LD1RC_1LD1LB 0 4
               run_z_1RB0RC_1LA0RA_0LD1RC_1LD1LB (Ap_Alph_11_00_001 q0 ++ [S0]) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gp_1RB0RC_1LA0RA_0LD1RC_1LD1LB p j' q0 E) as (HA & HB).
    exists (4 * j' + 8). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chp_1RB0RC_1LA0RA_0LD1RC_1LD1LB P0_1RB0RC_1LA0RA_0LD1RC_1LD1LB P1_1RB0RC_1LA0RA_0LD1RC_1LD1LB 4 8
               run_p_1RB0RC_1LA0RA_0LD1RC_1LD1LB (Ap_Alph_11_00_001 q0 ++ [S0]) [] j'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
Qed.

Lemma gso_1RB0RC_1LA0RA_0LD1RC_1LD1LB : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_1RB0RC_1LA0RA_0LD1RC_1LD1LB.
Proof.
  intros p j E. destruct (Alph_11_00_001.cview_none_Alph_11_00_001 p j E) as (H1 & _).
  unfold Cc_1RB0RC_1LA0RA_0LD1RC_1LD1LB, cden, B0_1RB0RC_1LA0RA_0LD1RC_1LD1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB0RC_1LA0RA_0LD1RC_1LD1LB : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB0RC_1LA0RA_0LD1RC_1LD1LB : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB0RC_1LA0RA_0LD1RC_1LD1LB) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (Alph_11_00_001.cview_none_Alph_11_00_001 p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB0RC_1LA0RA_0LD1RC_1LD1LB
             = (StC, (rep [S1;S1] (S j) ++ [S0;S0;S1], S0, []))).
  { unfold cden, B1_1RB0RC_1LA0RA_0LD1RC_1LD1LB, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. reflexivity. }
  assert (HC : Cc (Pos.succ p) = (StC, ((rep [S1;S1] (S j) ++ [S0;S0;S1]) ++ [S0], S0, []))).
  { unfold Cc_1RB0RC_1LA0RA_0LD1RC_1LD1LB. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_1RB0RC_1LA0RA_0LD1RC_1LD1LB. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_1RB0RC_1LA0RA_0LD1RC_1LD1LB : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB0RC_1LA0RA_0LD1RC_1LD1LB p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_1RB0RC_1LA0RA_0LD1RC_1LD1LB B0_1RB0RC_1LA0RA_0LD1RC_1LD1LB B1_1RB0RC_1LA0RA_0LD1RC_1LD1LB 4 10 p j' [] []).
    + exact run_ovf_1RB0RC_1LA0RA_0LD1RC_1LD1LB.
    + reflexivity.
    + reflexivity.
    + exact (gso_1RB0RC_1LA0RA_0LD1RC_1LD1LB p j' E).
    + exact (geo_1RB0RC_1LA0RA_0LD1RC_1LD1LB p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_1RB0RC_1LA0RA_0LD1RC_1LD1LB : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 10.
  assert (H : match csteps tm 10 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 10 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma viso_1RB0RC_1LA0RA_0LD1RC_1LD1LB : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_1RB0RC_1LA0RA_0LD1RC_1LD1LB = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_1RB0RC_1LA0RA_0LD1RC_1LD1LB p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB0RC_1LA0RA_0LD1RC_1LD1LB p j E)].
Qed.

Lemma vis_1RB0RC_1LA0RA_0LD1RC_1LD1LB : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_1RB0RC_1LA0RA_0LD1RC_1LD1LB.
  destruct q.

  - (* StA *)
    apply (vis_via_ovf tm Cc Hi StA), viso_1RB0RC_1LA0RA_0LD1RC_1LD1LB
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 3; SWinL 1]).
    vm_compute; reflexivity.
  - (* StB *)
    apply (vis_via_ovf tm Cc Hi StB), viso_1RB0RC_1LA0RA_0LD1RC_1LD1LB
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 3]).
    vm_compute; reflexivity.
  - (* StC: the anchor state *)
    exists 0. eexists. split; reflexivity.
  - (* StD *)
    apply (vis_via_ovf tm Cc Hi StD), viso_1RB0RC_1LA0RA_0LD1RC_1LD1LB
      with (l := [SRotL 1; SWin 1]).
    vm_compute; reflexivity.
Qed.

Theorem nqh_1RB0RC_1LA0RA_0LD1RC_1LD1LB : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 1). - exact boot_1RB0RC_1LA0RA_0LD1RC_1LD1LB. - intros p _. apply lap_1RB0RC_1LA0RA_0LD1RC_1LD1LB. - intros p q _. apply vis_1RB0RC_1LA0RA_0LD1RC_1LD1LB. Qed.

Theorem nonhalt_1RB0RC_1LA0RA_0LD1RC_1LD1LB : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_1RB0RC_1LA0RA_0LD1RC_1LD1LB. Qed.
