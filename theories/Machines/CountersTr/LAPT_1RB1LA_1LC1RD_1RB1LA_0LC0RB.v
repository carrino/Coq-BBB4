(** * LAPT_1RB1LA_1LC1RD_1RB1LA_0LC0RB: TRANSITION-LEVEL board for machine 1RB1LA_1LC1RD_1RB1LA_0LC0RB, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Ap_Alph_10_11_11 digit alphabet (Alph_10_11_11.v), anchored at

      Cc p = (StA, (Ap_Alph_10_11_11 p ++ [S0], S1, [S1]))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  4*j+12 steps
      overflow  (cview p = (S j, None)):   4*j+13 steps

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 198 anchors.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter Alph_10_11_11 LapCertGlue LapCertGlueLift.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
From BBB4 Require Import BBBT4_Statement.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
Import ListNotations.

Definition mk_1RB1LA_1LC1RD_1RB1LA_0LC0RB (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1LA_1LC1RD_1RB1LA_0LC0RB.

(** 1RB1LA_1LC1RD_1RB1LA_0LC0RB *)
Definition tm_1RB1LA_1LC1RD_1RB1LA_0LC0RB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StA
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S1 DR StB | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S0 DL StC | StD, S1 => mk S0 DR StB end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_1RB1LA_1LC1RD_1RB1LA_0LC0RB : list Instr := [].
Definition tmw_1RB1LA_1LC1RD_1RB1LA_0LC0RB : TM := tm_wrap_trs tm_1RB1LA_1LC1RD_1RB1LA_0LC0RB pins_1RB1LA_1LC1RD_1RB1LA_0LC0RB.
Local Notation tm := tmw_1RB1LA_1LC1RD_1RB1LA_0LC0RB.

Definition Cc_1RB1LA_1LC1RD_1RB1LA_0LC0RB (p : positive) : cconf := (StA, (Ap_Alph_10_11_11 p ++ [S0], S1, [S1])).
Local Notation Cc := Cc_1RB1LA_1LC1RD_1RB1LA_0LC0RB.

(** ** The certificate *)

Definition A0_1RB1LA_1LC1RD_1RB1LA_0LC0RB : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S1 (mkS [S1] [] 0 0 []).
Definition A1_1RB1LA_1LC1RD_1RB1LA_0LC0RB : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S1 (mkS [S1;S0] [] 0 0 []).
Definition chi_1RB1LA_1LC1RD_1RB1LA_0LC0RB : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWin 1; SWinR 7].

Lemma run_int_1RB1LA_1LC1RD_1RB1LA_0LC0RB : srun tm false true chi_1RB1LA_1LC1RD_1RB1LA_0LC0RB A0_1RB1LA_1LC1RD_1RB1LA_0LC0RB = Some (A1_1RB1LA_1LC1RD_1RB1LA_0LC0RB, 4, 12).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB1LA_1LC1RD_1RB1LA_0LC0RB : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S1;S0]) S1 (mkS [S1] [] 0 0 []).
Definition B1_1RB1LA_1LC1RD_1RB1LA_0LC0RB : sconf := mkC StA (mkS [] [S1;S0] 1 1 [S1;S1]) S1 (mkS [S1;S0] [] 0 0 []).
Definition cho_1RB1LA_1LC1RD_1RB1LA_0LC0RB : list lstep := [SCycL 2 0; SWin 6; SCycR 2; SWin 1; SWinR 6; SRotL 1; SFoldL 1].

Lemma run_ovf_1RB1LA_1LC1RD_1RB1LA_0LC0RB : srun tm true true cho_1RB1LA_1LC1RD_1RB1LA_0LC0RB B0_1RB1LA_1LC1RD_1RB1LA_0LC0RB = Some (B1_1RB1LA_1LC1RD_1RB1LA_0LC0RB, 4, 13).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_1RB1LA_1LC1RD_1RB1LA_0LC0RB : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Ap_Alph_10_11_11 q0 ++ [S0]) [] j A0_1RB1LA_1LC1RD_1RB1LA_0LC0RB.
Proof.
  intros p j q0 E. destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (H1 & _).
  unfold Cc_1RB1LA_1LC1RD_1RB1LA_0LC0RB, cden, A0_1RB1LA_1LC1RD_1RB1LA_0LC0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

(** The lap ends on [S1;S0] where the anchor has [S1] -- one trailing blank,
    which [lift] cannot see. *)
Lemma gei_1RB1LA_1LC1RD_1RB1LA_0LC0RB : forall p j q0, cview p = (j, Some q0) ->
  lift (cden (Ap_Alph_10_11_11 q0 ++ [S0]) [] j A1_1RB1LA_1LC1RD_1RB1LA_0LC0RB) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (_ & H2).
  unfold Cc_1RB1LA_1LC1RD_1RB1LA_0LC0RB, cden, A1_1RB1LA_1LC1RD_1RB1LA_0LC0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S1;S0]) with (([S1]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB1LA_1LC1RD_1RB1LA_0LC0RB : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  exists (4 * j + 12), (cden (Ap_Alph_10_11_11 q0 ++ [S0]) [] j A1_1RB1LA_1LC1RD_1RB1LA_0LC0RB).
  split; [lia|]. split; [| exact (gei_1RB1LA_1LC1RD_1RB1LA_0LC0RB p j q0 E)].
  rewrite (gsi_1RB1LA_1LC1RD_1RB1LA_0LC0RB p j q0 E).
  exact (srun_sound tm false true chi_1RB1LA_1LC1RD_1RB1LA_0LC0RB A0_1RB1LA_1LC1RD_1RB1LA_0LC0RB A1_1RB1LA_1LC1RD_1RB1LA_0LC0RB 4 12
           run_int_1RB1LA_1LC1RD_1RB1LA_0LC0RB (Ap_Alph_10_11_11 q0 ++ [S0]) [] j
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma gso_1RB1LA_1LC1RD_1RB1LA_0LC0RB : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_1RB1LA_1LC1RD_1RB1LA_0LC0RB.
Proof.
  intros p j E. destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p j E) as (H1 & _).
  unfold Cc_1RB1LA_1LC1RD_1RB1LA_0LC0RB, cden, B0_1RB1LA_1LC1RD_1RB1LA_0LC0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB1LA_1LC1RD_1RB1LA_0LC0RB : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB1LA_1LC1RD_1RB1LA_0LC0RB : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB1LA_1LC1RD_1RB1LA_0LC0RB) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB1LA_1LC1RD_1RB1LA_0LC0RB
             = (StA, (rep [S1;S0] (S j) ++ [S1;S1], S1, ([S1]) ++ [S0]))).
  { unfold cden, B1_1RB1LA_1LC1RD_1RB1LA_0LC0RB, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StA, ((rep [S1;S0] (S j) ++ [S1;S1]) ++ [S0], S1, [S1]))).
  { unfold Cc_1RB1LA_1LC1RD_1RB1LA_0LC0RB. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lift_app_blank. rewrite !lbl_1RB1LA_1LC1RD_1RB1LA_0LC0RB. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_1RB1LA_1LC1RD_1RB1LA_0LC0RB : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB1LA_1LC1RD_1RB1LA_0LC0RB p j q0 E) as (n & c' & Hn & Hrun & Hlift).
    exists n, c'. split; [exact Hrun | split; [exact Hlift | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_1RB1LA_1LC1RD_1RB1LA_0LC0RB B0_1RB1LA_1LC1RD_1RB1LA_0LC0RB B1_1RB1LA_1LC1RD_1RB1LA_0LC0RB 4 13 p j' [] []).
    + exact run_ovf_1RB1LA_1LC1RD_1RB1LA_0LC0RB.
    + reflexivity.
    + reflexivity.
    + exact (gso_1RB1LA_1LC1RD_1RB1LA_0LC0RB p j' E).
    + exact (geo_1RB1LA_1LC1RD_1RB1LA_0LC0RB p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_1RB1LA_1LC1RD_1RB1LA_0LC0RB : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 11.
  assert (H : match csteps tm 11 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 11 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_1RB1LA_1LC1RD_1RB1LA_0LC0RB : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_1RB1LA_1LC1RD_1RB1LA_0LC0RB = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_1RB1LA_1LC1RD_1RB1LA_0LC0RB p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB1LA_1LC1RD_1RB1LA_0LC0RB p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_1RB1LA_1LC1RD_1RB1LA_0LC0RB : forall t, ~ In t pins_1RB1LA_1LC1RD_1RB1LA_0LC0RB ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n c', 0 < n /\ csteps tm n (Cc p0) = Some c'
                         /\ lift c' = lift (Cc (Pos.succ p0)))
    by exact lapi_1RB1LA_1LC1RD_1RB1LA_0LC0RB.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StA, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB1LA_1LC1RD_1RB1LA_0LC0RB [SCycL 2 0; SWin 3] (StA, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* A1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StA, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB1LA_1LC1RD_1RB1LA_0LC0RB [] (StA, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* B0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StB, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB1LA_1LC1RD_1RB1LA_0LC0RB [SCycL 2 0; SWin 6; SCycR 2; SWin 1; SWinR 1] (StB, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* B1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StB, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB1LA_1LC1RD_1RB1LA_0LC0RB [SCycL 2 0; SWin 4] (StB, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* C0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StC, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB1LA_1LC1RD_1RB1LA_0LC0RB [SCycL 2 0; SWin 6; SCycR 2; SWin 1; SWinR 2] (StC, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* C1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StC, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB1LA_1LC1RD_1RB1LA_0LC0RB [SCycL 2 0; SWin 6; SCycR 2; SWin 1; SWinR 5] (StC, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* D0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StD, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB1LA_1LC1RD_1RB1LA_0LC0RB [SCycL 2 0; SWin 6; SCycR 2; SWin 1; SWinR 4] (StD, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* D1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StD, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB1LA_1LC1RD_1RB1LA_0LC0RB [SCycL 2 0; SWin 5] (StD, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
Qed.

Theorem nqhtr_1RB1LA_1LC1RD_1RB1LA_0LC0RB : NeverQuasiHaltsTr tm_1RB1LA_1LC1RD_1RB1LA_0LC0RB.
Proof.
  apply (glue_neverqhtr tm_1RB1LA_1LC1RD_1RB1LA_0LC0RB pins_1RB1LA_1LC1RD_1RB1LA_0LC0RB Cc 1).
  - exact boot_1RB1LA_1LC1RD_1RB1LA_0LC0RB.
  - intros p _. apply lap_1RB1LA_1LC1RD_1RB1LA_0LC0RB.
  - intros t Ht p _. apply fire_1RB1LA_1LC1RD_1RB1LA_0LC0RB. exact Ht.
Qed.

Theorem nonhalt_1RB1LA_1LC1RD_1RB1LA_0LC0RB : NonHalt tm_1RB1LA_1LC1RD_1RB1LA_0LC0RB.
Proof. apply never_qh_tr_nonhalt, nqhtr_1RB1LA_1LC1RD_1RB1LA_0LC0RB. Qed.
