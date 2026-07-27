(** * LAPC_0RB1LC_1LA1RB_1LA0RD_0LC1RD: machine 0RB1LC_1LA1RB_1LA0RD_0LC1RD, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Jp digit alphabet (JpCounter.v), anchored at

      Cc p = (StC, (Jp p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  4*j+20 steps
      overflow  (cview p = (S j, None)):   4*j+19 steps

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 198 anchors.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter JpCounter LapCertGlue LapCertGlueLift.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_0RB1LC_1LA1RB_1LA0RD_0LC1RD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB1LC_1LA1RB_1LA0RD_0LC1RD.

(** 0RB1LC_1LA1RB_1LA0RD_0LC1RD *)
Definition tm_0RB1LC_1LA1RB_1LA0RD_0LC1RD : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S1 DL StC
  | StB, S0 => mk S1 DL StA | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S1 DL StA | StC, S1 => mk S0 DR StD
  | StD, S0 => mk S0 DL StC | StD, S1 => mk S1 DR StD end.
Local Notation tm := tm_0RB1LC_1LA1RB_1LA0RD_0LC1RD.

Definition Cc_0RB1LC_1LA1RB_1LA0RD_0LC1RD (p : positive) : cconf := (StC, (Jp p ++ [S0], S0, [S1;S1])).
Local Notation Cc := Cc_0RB1LC_1LA1RB_1LA0RD_0LC1RD.

(** ** The certificate *)

Definition A0_0RB1LC_1LA1RB_1LA0RD_0LC1RD : sconf := mkC StC (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1;S1] [] 0 0 []).
Definition A1_0RB1LC_1LA1RB_1LA0RD_0LC1RD : sconf := mkC StC (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S1;S1;S0] [] 0 0 []).
Definition chi_0RB1LC_1LA1RB_1LA0RD_0LC1RD : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWin 2; SWinR 14].

Lemma run_int_0RB1LC_1LA1RB_1LA0RD_0LC1RD : srun tm false true chi_0RB1LC_1LA1RB_1LA0RD_0LC1RD A0_0RB1LC_1LA1RB_1LA0RD_0LC1RD = Some (A1_0RB1LC_1LA1RB_1LA0RD_0LC1RD, 4, 20).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB1LC_1LA1RB_1LA0RD_0LC1RD : sconf := mkC StC (mkS [] [S1;S0] 1 0 [S1;S0]) S0 (mkS [S1;S1] [] 0 0 []).
Definition B1_0RB1LC_1LA1RB_1LA0RD_0LC1RD : sconf := mkC StC (mkS [] [S1;S1] 1 1 [S1;S0]) S0 (mkS [S1;S1;S0] [] 0 0 []).
Definition cho_0RB1LC_1LA1RB_1LA0RD_0LC1RD : list lstep := [SCycL 2 0; SWin 2; SWinL 4; SCycR 2; SWin 2; SWinR 11; SRotL 1; SFoldL 1].

Lemma run_ovf_0RB1LC_1LA1RB_1LA0RD_0LC1RD : srun tm true true cho_0RB1LC_1LA1RB_1LA0RD_0LC1RD B0_0RB1LC_1LA1RB_1LA0RD_0LC1RD = Some (B1_0RB1LC_1LA1RB_1LA0RD_0LC1RD, 4, 19).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_0RB1LC_1LA1RB_1LA0RD_0LC1RD : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Jp q0 ++ [S0]) [] j A0_0RB1LC_1LA1RB_1LA0RD_0LC1RD.
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (H1 & _).
  unfold Cc_0RB1LC_1LA1RB_1LA0RD_0LC1RD, cden, A0_0RB1LC_1LA1RB_1LA0RD_0LC1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

(** The lap ends on [S1;S1;S0] where the anchor has [S1;S1] -- one trailing blank,
    which [lift] cannot see. *)
Lemma gei_0RB1LC_1LA1RB_1LA0RD_0LC1RD : forall p j q0, cview p = (j, Some q0) ->
  lift (cden (Jp q0 ++ [S0]) [] j A1_0RB1LC_1LA1RB_1LA0RD_0LC1RD) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (_ & H2).
  unfold Cc_0RB1LC_1LA1RB_1LA0RD_0LC1RD, cden, A1_0RB1LC_1LA1RB_1LA0RD_0LC1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S1;S1;S0]) with ([S1;S1] ++ [S0]).
  rewrite lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_0RB1LC_1LA1RB_1LA0RD_0LC1RD : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  exists (4 * j + 20), (cden (Jp q0 ++ [S0]) [] j A1_0RB1LC_1LA1RB_1LA0RD_0LC1RD).
  split; [lia|]. split; [| exact (gei_0RB1LC_1LA1RB_1LA0RD_0LC1RD p j q0 E)].
  rewrite (gsi_0RB1LC_1LA1RB_1LA0RD_0LC1RD p j q0 E).
  exact (srun_sound tm false true chi_0RB1LC_1LA1RB_1LA0RD_0LC1RD A0_0RB1LC_1LA1RB_1LA0RD_0LC1RD A1_0RB1LC_1LA1RB_1LA0RD_0LC1RD 4 20
           run_int_0RB1LC_1LA1RB_1LA0RD_0LC1RD (Jp q0 ++ [S0]) [] j
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma gso_0RB1LC_1LA1RB_1LA0RD_0LC1RD : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_0RB1LC_1LA1RB_1LA0RD_0LC1RD.
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (H1 & _).
  unfold Cc_0RB1LC_1LA1RB_1LA0RD_0LC1RD, cden, B0_0RB1LC_1LA1RB_1LA0RD_0LC1RD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_0RB1LC_1LA1RB_1LA0RD_0LC1RD : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_0RB1LC_1LA1RB_1LA0RD_0LC1RD : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB1LC_1LA1RB_1LA0RD_0LC1RD) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_0RB1LC_1LA1RB_1LA0RD_0LC1RD
             = (StC, (rep [S1;S1] (S j) ++ [S1;S0], S0, [S1;S1] ++ [S0]))).
  { unfold cden, B1_0RB1LC_1LA1RB_1LA0RD_0LC1RD, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. reflexivity. }
  assert (HC : Cc (Pos.succ p) = (StC, (rep [S1;S1] (S j) ++ [S1;S0], S0, [S1;S1]))).
  { unfold Cc_0RB1LC_1LA1RB_1LA0RD_0LC1RD. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite lift_app_blank. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_0RB1LC_1LA1RB_1LA0RD_0LC1RD : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB1LC_1LA1RB_1LA0RD_0LC1RD p j q0 E) as (n & c' & Hn & Hrun & Hlift).
    exists n, c'. split; [exact Hrun | split; [exact Hlift | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_0RB1LC_1LA1RB_1LA0RD_0LC1RD B0_0RB1LC_1LA1RB_1LA0RD_0LC1RD B1_0RB1LC_1LA1RB_1LA0RD_0LC1RD 4 19 p j' [] []).
    + exact run_ovf_0RB1LC_1LA1RB_1LA0RD_0LC1RD.
    + reflexivity.
    + reflexivity.
    + exact (gso_0RB1LC_1LA1RB_1LA0RD_0LC1RD p j' E).
    + exact (geo_0RB1LC_1LA1RB_1LA0RD_0LC1RD p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_0RB1LC_1LA1RB_1LA0RD_0LC1RD : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 21.
  assert (H : match csteps tm 21 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 21 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma viso_0RB1LC_1LA1RB_1LA0RD_0LC1RD : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_0RB1LC_1LA1RB_1LA0RD_0LC1RD = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_0RB1LC_1LA1RB_1LA0RD_0LC1RD p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB1LC_1LA1RB_1LA0RD_0LC1RD p j E)].
Qed.

Lemma vis_0RB1LC_1LA1RB_1LA0RD_0LC1RD : forall p q, exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros p q.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n c', 0 < n /\ csteps tm n (Cc p0) = Some c'
                         /\ lift c' = lift (Cc (Pos.succ p0)))
    by exact lapi_0RB1LC_1LA1RB_1LA0RD_0LC1RD.
  destruct q.

  - (* StA *)
    apply (vis_via_ovf_lift tm Cc Hi StA).
    intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
    apply (viso_0RB1LC_1LA1RB_1LA0RD_0LC1RD [SCycL 2 0; SWin 1] StA ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* StB *)
    apply (vis_via_ovf_lift tm Cc Hi StB).
    intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
    apply (viso_0RB1LC_1LA1RB_1LA0RD_0LC1RD [SCycL 2 0; SWin 2; SWinL 2] StB ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* StC: the anchor state *)
    exists 0. eexists. split; reflexivity.
  - (* StD *)
    apply (vis_via_ovf_lift tm Cc Hi StD).
    intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
    apply (viso_0RB1LC_1LA1RB_1LA0RD_0LC1RD [SCycL 2 0; SWin 2; SWinL 4; SCycR 2; SWin 2; SWinR 4] StD ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
Qed.

(** The interior lap closes only up to [lift] (one trailing blank past the
    anchor's far side), so the closer is [LapCertGlueLift.glue_neverqh_lift]:
    [LapGlue.glue_neverqh] with the visit premise in [stepn] space, which is
    what its own proof consumes. *)
Theorem nqh_0RB1LC_1LA1RB_1LA0RD_0LC1RD : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh_lift tm Cc 1). - exact boot_0RB1LC_1LA1RB_1LA0RD_0LC1RD. - intros p _. apply lap_0RB1LC_1LA1RB_1LA0RD_0LC1RD. - intros p q _. apply vis_0RB1LC_1LA1RB_1LA0RD_0LC1RD. Qed.

Theorem nonhalt_0RB1LC_1LA1RB_1LA0RD_0LC1RD : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_0RB1LC_1LA1RB_1LA0RD_0LC1RD. Qed.
