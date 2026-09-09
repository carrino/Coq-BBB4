(** * LAPQ_1RB0LB_1LC1RD_0RD0LC_1RA1RA: TRANSITION-LEVEL QUASIHALTING-side board for machine 1RB0LB_1LC1RD_0RD0LC_1RA1RA, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Ap_Alph_000_010_01 digit alphabet (Alph_000_010_01.v), anchored at

      Cc p = (StD, (Ap_Alph_000_010_01 p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  6*j+6 steps
      overflow  (cview p = (S j, None)):   6*j+12 steps

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 198 anchors.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter Alph_000_010_01 LapCertGlue LapCertGlueLift.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
From BBB4 Require Import BBBT4_Statement.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr.
From BBB4 Require Import ClosureTr.
From BBB4.Counters Require Import LapGlueQHTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

Definition mk_1RB0LB_1LC1RD_0RD0LC_1RA1RA (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB0LB_1LC1RD_0RD0LC_1RA1RA.

(** 1RB0LB_1LC1RD_0RD0LC_1RA1RA *)
(** 1RB0LB_1LC1RD_0RD0LC_1RA1RA -- the real machine (its counter grows RIGHT). *)
Definition tm_1RB0LB_1LC1RD_0RD0LC_1RA1RA : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StB
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S0 DR StD | StC, S1 => mk S0 DL StC
  | StD, S0 => mk S1 DR StA | StD, S1 => mk S1 DR StA end.

(** Its mirror 1LB0RB_1RC1LD_0LD0RC_1LA1LA: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_1RB0LB_1LC1RD_0RD0LC_1RA1RA : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => mk S0 DR StB
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DL StD
  | StC, S0 => mk S0 DL StD | StC, S1 => mk S0 DR StC
  | StD, S0 => mk S1 DL StA | StD, S1 => mk S1 DL StA end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_1RB0LB_1LC1RD_0RD0LC_1RA1RA : list Instr := [(StA, S1); (StD, S1)].
Definition tmw_1RB0LB_1LC1RD_0RD0LC_1RA1RA : TM := tm_wrap_trs tmm_1RB0LB_1LC1RD_0RD0LC_1RA1RA pins_1RB0LB_1LC1RD_0RD0LC_1RA1RA.
Local Notation tm := tmw_1RB0LB_1LC1RD_0RD0LC_1RA1RA.

Lemma mirror_ok_1RB0LB_1LC1RD_0RD0LC_1RA1RA : mirror_tm tm_1RB0LB_1LC1RD_0RD0LC_1RA1RA = tmm_1RB0LB_1LC1RD_0RD0LC_1RA1RA.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_1RB0LB_1LC1RD_0RD0LC_1RA1RA (p : positive) : cconf := (StD, (Ap_Alph_000_010_01 p ++ [S0], S0, [])).
Local Notation Cc := Cc_1RB0LB_1LC1RD_0RD0LC_1RA1RA.

(** ** The certificate *)

Definition A0_1RB0LB_1LC1RD_0RD0LC_1RA1RA : sconf := mkC StD (mkS [] [S0;S1;S0] 1 0 [S0;S0;S0]) S0 (mkS [] [] 0 0 []).
Definition A1_1RB0LB_1LC1RD_0RD0LC_1RA1RA : sconf := mkC StD (mkS [] [S0;S0;S0] 1 0 [S0;S1;S0]) S0 (mkS [S0] [] 0 0 []).
Definition chi_1RB0LB_1LC1RD_0RD0LC_1RA1RA : list lstep := [SCycL 3 0; SWin 4; SCycR 3; SWinR 2].

Lemma run_int_1RB0LB_1LC1RD_0RD0LC_1RA1RA : srun tm false true chi_1RB0LB_1LC1RD_0RD0LC_1RA1RA A0_1RB0LB_1LC1RD_0RD0LC_1RA1RA = Some (A1_1RB0LB_1LC1RD_0RD0LC_1RA1RA, 6, 6).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB0LB_1LC1RD_0RD0LC_1RA1RA : sconf := mkC StD (mkS [] [S0;S1;S0] 1 0 [S0;S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_1RB0LB_1LC1RD_0RD0LC_1RA1RA : sconf := mkC StD (mkS [] [S0;S0;S0] 1 1 [S0;S1]) S0 (mkS [S0] [] 0 0 []).
Definition cho_1RB0LB_1LC1RD_0RD0LC_1RA1RA : list lstep := [SCycL 3 0; SWin 3; SWinL 7; SCycR 3; SWinR 2; SRotL 3; SFoldL 1].

Lemma run_ovf_1RB0LB_1LC1RD_0RD0LC_1RA1RA : srun tm true true cho_1RB0LB_1LC1RD_0RD0LC_1RA1RA B0_1RB0LB_1LC1RD_0RD0LC_1RA1RA = Some (B1_1RB0LB_1LC1RD_0RD0LC_1RA1RA, 6, 12).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_1RB0LB_1LC1RD_0RD0LC_1RA1RA : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Ap_Alph_000_010_01 q0 ++ [S0]) [] j A0_1RB0LB_1LC1RD_0RD0LC_1RA1RA.
Proof.
  intros p j q0 E. destruct (Alph_000_010_01.cview_some_Alph_000_010_01 p j q0 E) as (H1 & _).
  unfold Cc_1RB0LB_1LC1RD_0RD0LC_1RA1RA, cden, A0_1RB0LB_1LC1RD_0RD0LC_1RA1RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S0;S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

(** The lap ends on [S0] where the anchor has [] -- one trailing blank,
    which [lift] cannot see. *)
Lemma gei_1RB0LB_1LC1RD_0RD0LC_1RA1RA : forall p j q0, cview p = (j, Some q0) ->
  lift (cden (Ap_Alph_000_010_01 q0 ++ [S0]) [] j A1_1RB0LB_1LC1RD_0RD0LC_1RA1RA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (Alph_000_010_01.cview_some_Alph_000_010_01 p j q0 E) as (_ & H2).
  unfold Cc_1RB0LB_1LC1RD_0RD0LC_1RA1RA, cden, A1_1RB0LB_1LC1RD_0RD0LC_1RA1RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S0]) with (([]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S0;S0;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB0LB_1LC1RD_0RD0LC_1RA1RA : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  exists (6 * j + 6), (cden (Ap_Alph_000_010_01 q0 ++ [S0]) [] j A1_1RB0LB_1LC1RD_0RD0LC_1RA1RA).
  split; [lia|]. split; [| exact (gei_1RB0LB_1LC1RD_0RD0LC_1RA1RA p j q0 E)].
  rewrite (gsi_1RB0LB_1LC1RD_0RD0LC_1RA1RA p j q0 E).
  exact (srun_sound tm false true chi_1RB0LB_1LC1RD_0RD0LC_1RA1RA A0_1RB0LB_1LC1RD_0RD0LC_1RA1RA A1_1RB0LB_1LC1RD_0RD0LC_1RA1RA 6 6
           run_int_1RB0LB_1LC1RD_0RD0LC_1RA1RA (Ap_Alph_000_010_01 q0 ++ [S0]) [] j
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma gso_1RB0LB_1LC1RD_0RD0LC_1RA1RA : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_1RB0LB_1LC1RD_0RD0LC_1RA1RA.
Proof.
  intros p j E. destruct (Alph_000_010_01.cview_none_Alph_000_010_01 p j E) as (H1 & _).
  unfold Cc_1RB0LB_1LC1RD_0RD0LC_1RA1RA, cden, B0_1RB0LB_1LC1RD_0RD0LC_1RA1RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB0LB_1LC1RD_0RD0LC_1RA1RA : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB0LB_1LC1RD_0RD0LC_1RA1RA : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB0LB_1LC1RD_0RD0LC_1RA1RA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (Alph_000_010_01.cview_none_Alph_000_010_01 p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB0LB_1LC1RD_0RD0LC_1RA1RA
             = (StD, (rep [S0;S0;S0] (S j) ++ [S0;S1], S0, ([]) ++ [S0]))).
  { unfold cden, B1_1RB0LB_1LC1RD_0RD0LC_1RA1RA, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StD, ((rep [S0;S0;S0] (S j) ++ [S0;S1]) ++ [S0], S0, []))).
  { unfold Cc_1RB0LB_1LC1RD_0RD0LC_1RA1RA. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lift_app_blank. rewrite !lbl_1RB0LB_1LC1RD_0RD0LC_1RA1RA. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_1RB0LB_1LC1RD_0RD0LC_1RA1RA : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB0LB_1LC1RD_0RD0LC_1RA1RA p j q0 E) as (n & c' & Hn & Hrun & Hlift).
    exists n, c'. split; [exact Hrun | split; [exact Hlift | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_1RB0LB_1LC1RD_0RD0LC_1RA1RA B0_1RB0LB_1LC1RD_0RD0LC_1RA1RA B1_1RB0LB_1LC1RD_0RD0LC_1RA1RA 6 12 p j' [] []).
    + exact run_ovf_1RB0LB_1LC1RD_0RD0LC_1RA1RA.
    + reflexivity.
    + reflexivity.
    + exact (gso_1RB0LB_1LC1RD_0RD0LC_1RA1RA p j' E).
    + exact (geo_1RB0LB_1LC1RD_0RD0LC_1RA1RA p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma bootq_1RB0LB_1LC1RD_0RD0LC_1RA1RA : stepn tmm_1RB0LB_1LC1RD_0RD0LC_1RA1RA 32 InitES = Some (lift (Cc 2)).
Proof.
  assert (H : match csteps tmm_1RB0LB_1LC1RD_0RD0LC_1RA1RA 32 c0 with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tmm_1RB0LB_1LC1RD_0RD0LC_1RA1RA 32 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** the quasihalt witness: a pinned instruction fired in the prefix *)
Lemma wit_1RB0LB_1LC1RD_0RD0LC_1RA1RA : existsb (fun tg => cfires tmm_1RB0LB_1LC1RD_0RD0LC_1RA1RA c0 32 tg) pins_1RB0LB_1LC1RD_0RD0LC_1RA1RA = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_1RB0LB_1LC1RD_0RD0LC_1RA1RA : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_1RB0LB_1LC1RD_0RD0LC_1RA1RA = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_1RB0LB_1LC1RD_0RD0LC_1RA1RA p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB0LB_1LC1RD_0RD0LC_1RA1RA p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_1RB0LB_1LC1RD_0RD0LC_1RA1RA : forall t, ~ In t pins_1RB0LB_1LC1RD_0RD0LC_1RA1RA ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n c', 0 < n /\ csteps tm n (Cc p0) = Some c'
                         /\ lift c' = lift (Cc (Pos.succ p0)))
    by exact lapi_1RB0LB_1LC1RD_0RD0LC_1RA1RA.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StA, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB0LB_1LC1RD_0RD0LC_1RA1RA [SCycL 3 0; SWin 1] (StA, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* A1: pinned *)
    exfalso. apply Hnp. apply tr_inb_spec. reflexivity.
  - (* B0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StB, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB0LB_1LC1RD_0RD0LC_1RA1RA [SCycL 3 0; SWin 3; SWinL 2] (StB, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* B1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StB, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB0LB_1LC1RD_0RD0LC_1RA1RA [SCycL 3 0; SWin 2] (StB, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* C0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StC, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB0LB_1LC1RD_0RD0LC_1RA1RA [SCycL 3 0; SWin 3; SWinL 7; SCycR 3; SWinR 1] (StC, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* C1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StC, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB0LB_1LC1RD_0RD0LC_1RA1RA [SCycL 3 0; SWin 3; SWinL 3] (StC, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* D0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StD, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_1RB0LB_1LC1RD_0RD0LC_1RA1RA [] (StD, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* D1: pinned *)
    exfalso. apply Hnp. apply tr_inb_spec. reflexivity.
Qed.

Theorem qhtrm_1RB0LB_1LC1RD_0RD0LC_1RA1RA : NonHalt tmm_1RB0LB_1LC1RD_0RD0LC_1RA1RA /\ QHBoundTr 32779478 tmm_1RB0LB_1LC1RD_0RD0LC_1RA1RA /\ QuasiHaltsTr tmm_1RB0LB_1LC1RD_0RD0LC_1RA1RA.
Proof.
  apply (lap_qh_stage tmm_1RB0LB_1LC1RD_0RD0LC_1RA1RA pins_1RB0LB_1LC1RD_0RD0LC_1RA1RA Cc 2 32 32779478).
  - exact bootq_1RB0LB_1LC1RD_0RD0LC_1RA1RA.
  - intros p _. apply lap_1RB0LB_1LC1RD_0RD0LC_1RA1RA.
  - intros t Ht p _. apply fire_1RB0LB_1LC1RD_0RD0LC_1RA1RA. exact Ht.
  - exact wit_1RB0LB_1LC1RD_0RD0LC_1RA1RA.
  - vm_cast_no_check (eq_refl true).
Qed.

Theorem qhtr_1RB0LB_1LC1RD_0RD0LC_1RA1RA : NonHalt tm_1RB0LB_1LC1RD_0RD0LC_1RA1RA /\ QHBoundTr 32779478 tm_1RB0LB_1LC1RD_0RD0LC_1RA1RA /\ QuasiHaltsTr tm_1RB0LB_1LC1RD_0RD0LC_1RA1RA.
Proof. apply (qh_triple_unmirror 32779478 tm_1RB0LB_1LC1RD_0RD0LC_1RA1RA). rewrite mirror_ok_1RB0LB_1LC1RD_0RD0LC_1RA1RA. exact qhtrm_1RB0LB_1LC1RD_0RD0LC_1RA1RA. Qed.
