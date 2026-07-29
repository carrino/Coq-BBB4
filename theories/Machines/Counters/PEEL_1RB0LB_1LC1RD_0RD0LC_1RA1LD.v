(** * PEEL_1RB0LB_1LC1RD_0RD0LC_1RA1LD: machine 1RB0LB_1LC1RD_0RD0LC_1RA1LD, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Ap_Alph_000_001_1 digit alphabet (Alph_000_001_1.v), anchored at

      Cc p = (StC, (Ap_Alph_000_001_1 p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  6*j+6 steps
      overflow  (cview p = (S j, None)):   18*j+29 steps at j = S j', 11 at p = 1

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 199 anchors (overflow PEELED at j = S j', p = 1 concrete).
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter Alph_000_001_1 LapCertGlue IXPGadgets.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_1RB0LB_1LC1RD_0RD0LC_1RA1LD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB0LB_1LC1RD_0RD0LC_1RA1LD.

(** 1RB0LB_1LC1RD_0RD0LC_1RA1LD *)
(** 1RB0LB_1LC1RD_0RD0LC_1RA1LD -- the real machine (its counter grows RIGHT). *)
Definition tm_1RB0LB_1LC1RD_0RD0LC_1RA1LD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StB
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S0 DR StD | StC, S1 => mk S0 DL StC
  | StD, S0 => mk S1 DR StA | StD, S1 => mk S1 DL StD end.

(** Its mirror 1LB0RB_1RC1LD_0LD0RC_1LA1RD: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_1RB0LB_1LC1RD_0RD0LC_1RA1LD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => mk S0 DR StB
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DL StD
  | StC, S0 => mk S0 DL StD | StC, S1 => mk S0 DR StC
  | StD, S0 => mk S1 DL StA | StD, S1 => mk S1 DR StD end.
Local Notation tm := tmm_1RB0LB_1LC1RD_0RD0LC_1RA1LD.

Lemma mirror_ok_1RB0LB_1LC1RD_0RD0LC_1RA1LD : mirror_tm tm_1RB0LB_1LC1RD_0RD0LC_1RA1LD = tmm_1RB0LB_1LC1RD_0RD0LC_1RA1LD.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_1RB0LB_1LC1RD_0RD0LC_1RA1LD (p : positive) : cconf := (StC, (Ap_Alph_000_001_1 p ++ [S0], S0, [])).
Local Notation Cc := Cc_1RB0LB_1LC1RD_0RD0LC_1RA1LD.

(** ** The certificate *)

Definition A0_1RB0LB_1LC1RD_0RD0LC_1RA1LD : sconf := mkC StC (mkS [] [S0;S0;S1] 1 0 [S0;S0;S0]) S0 (mkS [] [] 0 0 []).
Definition A1_1RB0LB_1LC1RD_0RD0LC_1RA1LD : sconf := mkC StC (mkS [] [S0;S0;S0] 1 0 [S0;S0;S1]) S0 (mkS [] [] 0 0 []).
Definition chi_1RB0LB_1LC1RD_0RD0LC_1RA1LD : list lstep := [SRotL 1; SWin 1; SCycL 3 0; SWin 4; SCycR 3; SWin 1; SUnrotL 1].

Lemma run_int_1RB0LB_1LC1RD_0RD0LC_1RA1LD : srun tm false true chi_1RB0LB_1LC1RD_0RD0LC_1RA1LD A0_1RB0LB_1LC1RD_0RD0LC_1RA1LD = Some (A1_1RB0LB_1LC1RD_0RD0LC_1RA1LD, 6, 6).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB0LB_1LC1RD_0RD0LC_1RA1LD : sconf := mkC StC (mkS [S0;S0;S1] [S0;S0;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_1RB0LB_1LC1RD_0RD0LC_1RA1LD : sconf := mkC StC (mkS [S0;S0;S0] [S0;S0;S0] 1 1 [S1]) S0 (mkS [] [] 0 0 []).
Definition cho_1RB0LB_1LC1RD_0RD0LC_1RA1LD : list lstep := [SWin 3; SCycL 3 0; SWin 2; SCycR 3; SWin 10; SWin 2; SCycL 9 0; SWin 4; SWinL 4; SCycR 3; SWin 3; SWinR 1; SRotL 2; SFoldL 1].

Lemma run_ovf_1RB0LB_1LC1RD_0RD0LC_1RA1LD : srun tm true true cho_1RB0LB_1LC1RD_0RD0LC_1RA1LD B0_1RB0LB_1LC1RD_0RD0LC_1RA1LD = Some (B1_1RB0LB_1LC1RD_0RD0LC_1RA1LD, 18, 29).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_1RB0LB_1LC1RD_0RD0LC_1RA1LD : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Ap_Alph_000_001_1 q0 ++ [S0]) [] j A0_1RB0LB_1LC1RD_0RD0LC_1RA1LD.
Proof.
  intros p j q0 E. destruct (Alph_000_001_1.cview_some_Alph_000_001_1 p j q0 E) as (H1 & _).
  unfold Cc_1RB0LB_1LC1RD_0RD0LC_1RA1LD, cden, A0_1RB0LB_1LC1RD_0RD0LC_1RA1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S0;S0;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gei_1RB0LB_1LC1RD_0RD0LC_1RA1LD : forall p j q0, cview p = (j, Some q0) ->
  cden (Ap_Alph_000_001_1 q0 ++ [S0]) [] j A1_1RB0LB_1LC1RD_0RD0LC_1RA1LD = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (Alph_000_001_1.cview_some_Alph_000_001_1 p j q0 E) as (_ & H2).
  unfold Cc_1RB0LB_1LC1RD_0RD0LC_1RA1LD, cden, A1_1RB0LB_1LC1RD_0RD0LC_1RA1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S0;S0;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB0LB_1LC1RD_0RD0LC_1RA1LD : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (6 * j + 6). split; [lia|].
  rewrite (gsi_1RB0LB_1LC1RD_0RD0LC_1RA1LD p j q0 E).
  rewrite (srun_sound tm false true chi_1RB0LB_1LC1RD_0RD0LC_1RA1LD A0_1RB0LB_1LC1RD_0RD0LC_1RA1LD A1_1RB0LB_1LC1RD_0RD0LC_1RA1LD 6 6
             run_int_1RB0LB_1LC1RD_0RD0LC_1RA1LD (Ap_Alph_000_001_1 q0 ++ [S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_1RB0LB_1LC1RD_0RD0LC_1RA1LD p j q0 E).
Qed.

Lemma gso_1RB0LB_1LC1RD_0RD0LC_1RA1LD : forall p j, cview p = (S (S j), None) ->
  Cc p = cden [] [] j B0_1RB0LB_1LC1RD_0RD0LC_1RA1LD.
Proof.
  intros p j E. destruct (Alph_000_001_1.cview_none_Alph_000_001_1 p (S j) E) as (H1 & _).
  unfold Cc_1RB0LB_1LC1RD_0RD0LC_1RA1LD, cden, B0_1RB0LB_1LC1RD_0RD0LC_1RA1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB0LB_1LC1RD_0RD0LC_1RA1LD : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB0LB_1LC1RD_0RD0LC_1RA1LD : forall p j, cview p = (S (S j), None) ->
  lift (cden [] [] j B1_1RB0LB_1LC1RD_0RD0LC_1RA1LD) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (Alph_000_001_1.cview_none_Alph_000_001_1 p (S j) E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB0LB_1LC1RD_0RD0LC_1RA1LD
             = (StC, (rep [S0;S0;S0] (S (S j)) ++ [S1], S0, []))).
  { unfold cden, B1_1RB0LB_1LC1RD_0RD0LC_1RA1LD, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StC, ((rep [S0;S0;S0] (S (S j)) ++ [S1]) ++ [S0], S0, []))).
  { unfold Cc_1RB0LB_1LC1RD_0RD0LC_1RA1LD. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_1RB0LB_1LC1RD_0RD0LC_1RA1LD. reflexivity.
Qed.

(** The smallest overflow anchor, [p = 1]: one concrete run.  The peeled
    branch below states its chain at [j = S j'], so this case is what the
    reindex leaves behind -- the [j = 0] device of the offset route, at the
    OUTER anchor. *)
Lemma lapz_1RB0LB_1LC1RD_0RD0LC_1RA1LD : exists n c', csteps tm n (Cc 1) = Some c'
  /\ lift c' = lift (Cc 2) /\ 0 < n.
Proof.
  exists 11.
  assert (H : match csteps tm 11 (Cc 1) with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 11 (Cc 1)) as [c|] eqn:Ez; [|discriminate].
  exists c. split; [reflexivity|]. split; [apply ceqb_lift; exact H | lia].
Qed.

(** State StA's visit witness at the peeled branch's [p = 1] case. *)
Lemma visz_StA_1RB0LB_1LC1RD_0RD0LC_1RA1LD : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StA.
Proof. exists 3. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StB's visit witness at the peeled branch's [p = 1] case. *)
Lemma visz_StB_1RB0LB_1LC1RD_0RD0LC_1RA1LD : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StB.
Proof. exists 4. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StD's visit witness at the peeled branch's [p = 1] case. *)
Lemma visz_StD_1RB0LB_1LC1RD_0RD0LC_1RA1LD : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StD.
Proof. exists 1. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** ** The lap *)

Lemma lap_1RB0LB_1LC1RD_0RD0LC_1RA1LD : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB0LB_1LC1RD_0RD0LC_1RA1LD p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    destruct j' as [|j''].
    + rewrite (cview_none_shape p 0 E). exact lapz_1RB0LB_1LC1RD_0RD0LC_1RA1LD.
    + apply (lap_of_run tm Cc true true cho_1RB0LB_1LC1RD_0RD0LC_1RA1LD B0_1RB0LB_1LC1RD_0RD0LC_1RA1LD B1_1RB0LB_1LC1RD_0RD0LC_1RA1LD 18 29 p j'' [] []).
      * exact run_ovf_1RB0LB_1LC1RD_0RD0LC_1RA1LD.
      * reflexivity.
      * reflexivity.
      * exact (gso_1RB0LB_1LC1RD_0RD0LC_1RA1LD p j'' E).
      * exact (geo_1RB0LB_1LC1RD_0RD0LC_1RA1LD p j'' E).
      * lia.
Qed.

(** ** Bootstrap *)

Lemma boot_1RB0LB_1LC1RD_0RD0LC_1RA1LD : exists t0, stepn tm t0 InitES = Some (lift (Cc 2)).
Proof.
  exists 13.
  assert (H : match csteps tm 13 c0 with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 13 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma viso_1RB0LB_1LC1RD_0RD0LC_1RA1LD : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_1RB0LB_1LC1RD_0RD0LC_1RA1LD = Some q ->
  forall p j, cview p = (S (S j), None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_1RB0LB_1LC1RD_0RD0LC_1RA1LD p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB0LB_1LC1RD_0RD0LC_1RA1LD p j E)].
Qed.

Lemma vis_1RB0LB_1LC1RD_0RD0LC_1RA1LD : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_1RB0LB_1LC1RD_0RD0LC_1RA1LD.
  destruct q.

  - (* StA *)
    apply (vis_via_ovf tm Cc Hi StA).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1). exact visz_StA_1RB0LB_1LC1RD_0RD0LC_1RA1LD.
    + exact (viso_1RB0LB_1LC1RD_0RD0LC_1RA1LD [SWin 2] StA ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* StB *)
    apply (vis_via_ovf tm Cc Hi StB).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1). exact visz_StB_1RB0LB_1LC1RD_0RD0LC_1RA1LD.
    + exact (viso_1RB0LB_1LC1RD_0RD0LC_1RA1LD [SWin 3] StB ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* StC: the anchor state *)
    exists 0. eexists. split; reflexivity.
  - (* StD *)
    apply (vis_via_ovf tm Cc Hi StD).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1). exact visz_StD_1RB0LB_1LC1RD_0RD0LC_1RA1LD.
    + exact (viso_1RB0LB_1LC1RD_0RD0LC_1RA1LD [SWin 1] StD ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
Qed.

Theorem nqhm_1RB0LB_1LC1RD_0RD0LC_1RA1LD : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 2). - exact boot_1RB0LB_1LC1RD_0RD0LC_1RA1LD. - intros p _. apply lap_1RB0LB_1LC1RD_0RD0LC_1RA1LD. - intros p q _. apply vis_1RB0LB_1LC1RD_0RD0LC_1RA1LD. Qed.

Theorem nqh_1RB0LB_1LC1RD_0RD0LC_1RA1LD : NeverQuasiHaltsSt tm_1RB0LB_1LC1RD_0RD0LC_1RA1LD.
Proof. apply (mirror_never_qh tm_1RB0LB_1LC1RD_0RD0LC_1RA1LD). rewrite mirror_ok_1RB0LB_1LC1RD_0RD0LC_1RA1LD. exact nqhm_1RB0LB_1LC1RD_0RD0LC_1RA1LD. Qed.

Theorem nonhalt_1RB0LB_1LC1RD_0RD0LC_1RA1LD : NonHalt tm_1RB0LB_1LC1RD_0RD0LC_1RA1LD.
Proof. apply never_qh_nonhalt, nqh_1RB0LB_1LC1RD_0RD0LC_1RA1LD. Qed.
