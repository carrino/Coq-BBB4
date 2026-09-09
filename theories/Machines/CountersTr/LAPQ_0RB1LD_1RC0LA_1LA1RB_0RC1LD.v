(** * LAPQ_0RB1LD_1RC0LA_1LA1RB_0RC1LD: TRANSITION-LEVEL QUASIHALTING-side board for machine 0RB1LD_1RC0LA_1LA1RB_0RC1LD, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Jp digit alphabet (JpCounter.v), anchored at

      Cc p = (StB, (Jp p ++ [S0], S0, [S1]))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  4*j+12 steps
      overflow  (cview p = (S j, None)):   4*j+14 steps

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
                                  MonoCounter JpCounter JpCounter LapCertGlue LapCertGlueLift.
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

Definition mk_0RB1LD_1RC0LA_1LA1RB_0RC1LD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB1LD_1RC0LA_1LA1RB_0RC1LD.

(** 0RB1LD_1RC0LA_1LA1RB_0RC1LD *)
(** 0RB1LD_1RC0LA_1LA1RB_0RC1LD -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB1LD_1RC0LA_1LA1RB_0RC1LD : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S1 DL StD
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S0 DL StA
  | StC, S0 => mk S1 DL StA | StC, S1 => mk S1 DR StB
  | StD, S0 => mk S0 DR StC | StD, S1 => mk S1 DL StD end.

(** Its mirror 0LB1RD_1LC0RA_1RA1LB_0LC1RD: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB1LD_1RC0LA_1LA1RB_0RC1LD : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S1 DR StD
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DR StA
  | StC, S0 => mk S1 DR StA | StC, S1 => mk S1 DL StB
  | StD, S0 => mk S0 DL StC | StD, S1 => mk S1 DR StD end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_0RB1LD_1RC0LA_1LA1RB_0RC1LD : list Instr := [(StA, S0)].
Definition tmw_0RB1LD_1RC0LA_1LA1RB_0RC1LD : TM := tm_wrap_trs tmm_0RB1LD_1RC0LA_1LA1RB_0RC1LD pins_0RB1LD_1RC0LA_1LA1RB_0RC1LD.
Local Notation tm := tmw_0RB1LD_1RC0LA_1LA1RB_0RC1LD.

Lemma mirror_ok_0RB1LD_1RC0LA_1LA1RB_0RC1LD : mirror_tm tm_0RB1LD_1RC0LA_1LA1RB_0RC1LD = tmm_0RB1LD_1RC0LA_1LA1RB_0RC1LD.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_0RB1LD_1RC0LA_1LA1RB_0RC1LD (p : positive) : cconf := (StB, (Jp p ++ [S0], S0, [S1])).
Local Notation Cc := Cc_0RB1LD_1RC0LA_1LA1RB_0RC1LD.

(** ** The certificate *)

Definition A0_0RB1LD_1RC0LA_1LA1RB_0RC1LD : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition A1_0RB1LD_1RC0LA_1LA1RB_0RC1LD : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S1;S0] [] 0 0 []).
Definition chi_0RB1LD_1RC0LA_1LA1RB_0RC1LD : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWin 1; SWinR 7].

Lemma run_int_0RB1LD_1RC0LA_1LA1RB_0RC1LD : srun tm false true chi_0RB1LD_1RC0LA_1LA1RB_0RC1LD A0_0RB1LD_1RC0LA_1LA1RB_0RC1LD = Some (A1_0RB1LD_1RC0LA_1LA1RB_0RC1LD, 4, 12).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB1LD_1RC0LA_1LA1RB_0RC1LD : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S0]) S0 (mkS [S1] [] 0 0 []).
Definition B1_0RB1LD_1RC0LA_1LA1RB_0RC1LD : sconf := mkC StB (mkS [] [S1;S1] 1 1 [S1]) S0 (mkS [S1;S0] [] 0 0 []).
Definition cho_0RB1LD_1RC0LA_1LA1RB_0RC1LD : list lstep := [SCycL 2 0; SWin 2; SWinL 4; SCycR 2; SWin 1; SWinR 7; SRotL 2; SFoldL 1].

Lemma run_ovf_0RB1LD_1RC0LA_1LA1RB_0RC1LD : srun tm true true cho_0RB1LD_1RC0LA_1LA1RB_0RC1LD B0_0RB1LD_1RC0LA_1LA1RB_0RC1LD = Some (B1_0RB1LD_1RC0LA_1LA1RB_0RC1LD, 4, 14).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_0RB1LD_1RC0LA_1LA1RB_0RC1LD : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Jp q0 ++ [S0]) [] j A0_0RB1LD_1RC0LA_1LA1RB_0RC1LD.
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (H1 & _).
  unfold Cc_0RB1LD_1RC0LA_1LA1RB_0RC1LD, cden, A0_0RB1LD_1RC0LA_1LA1RB_0RC1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

(** The lap ends on [S1;S0] where the anchor has [S1] -- one trailing blank,
    which [lift] cannot see. *)
Lemma gei_0RB1LD_1RC0LA_1LA1RB_0RC1LD : forall p j q0, cview p = (j, Some q0) ->
  lift (cden (Jp q0 ++ [S0]) [] j A1_0RB1LD_1RC0LA_1LA1RB_0RC1LD) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (_ & H2).
  unfold Cc_0RB1LD_1RC0LA_1LA1RB_0RC1LD, cden, A1_0RB1LD_1RC0LA_1LA1RB_0RC1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S1;S0]) with (([S1]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_0RB1LD_1RC0LA_1LA1RB_0RC1LD : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  exists (4 * j + 12), (cden (Jp q0 ++ [S0]) [] j A1_0RB1LD_1RC0LA_1LA1RB_0RC1LD).
  split; [lia|]. split; [| exact (gei_0RB1LD_1RC0LA_1LA1RB_0RC1LD p j q0 E)].
  rewrite (gsi_0RB1LD_1RC0LA_1LA1RB_0RC1LD p j q0 E).
  exact (srun_sound tm false true chi_0RB1LD_1RC0LA_1LA1RB_0RC1LD A0_0RB1LD_1RC0LA_1LA1RB_0RC1LD A1_0RB1LD_1RC0LA_1LA1RB_0RC1LD 4 12
           run_int_0RB1LD_1RC0LA_1LA1RB_0RC1LD (Jp q0 ++ [S0]) [] j
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma gso_0RB1LD_1RC0LA_1LA1RB_0RC1LD : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_0RB1LD_1RC0LA_1LA1RB_0RC1LD.
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (H1 & _).
  unfold Cc_0RB1LD_1RC0LA_1LA1RB_0RC1LD, cden, B0_0RB1LD_1RC0LA_1LA1RB_0RC1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_0RB1LD_1RC0LA_1LA1RB_0RC1LD : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_0RB1LD_1RC0LA_1LA1RB_0RC1LD : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB1LD_1RC0LA_1LA1RB_0RC1LD) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (JpCounter.cview_none_J p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_0RB1LD_1RC0LA_1LA1RB_0RC1LD
             = (StB, (rep [S1;S1] (S j) ++ [S1], S0, ([S1]) ++ [S0]))).
  { unfold cden, B1_0RB1LD_1RC0LA_1LA1RB_0RC1LD, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StB, ((rep [S1;S1] (S j) ++ [S1]) ++ [S0], S0, [S1]))).
  { unfold Cc_0RB1LD_1RC0LA_1LA1RB_0RC1LD. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lift_app_blank. rewrite !lbl_0RB1LD_1RC0LA_1LA1RB_0RC1LD. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_0RB1LD_1RC0LA_1LA1RB_0RC1LD : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB1LD_1RC0LA_1LA1RB_0RC1LD p j q0 E) as (n & c' & Hn & Hrun & Hlift).
    exists n, c'. split; [exact Hrun | split; [exact Hlift | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_0RB1LD_1RC0LA_1LA1RB_0RC1LD B0_0RB1LD_1RC0LA_1LA1RB_0RC1LD B1_0RB1LD_1RC0LA_1LA1RB_0RC1LD 4 14 p j' [] []).
    + exact run_ovf_0RB1LD_1RC0LA_1LA1RB_0RC1LD.
    + reflexivity.
    + reflexivity.
    + exact (gso_0RB1LD_1RC0LA_1LA1RB_0RC1LD p j' E).
    + exact (geo_0RB1LD_1RC0LA_1LA1RB_0RC1LD p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma bootq_0RB1LD_1RC0LA_1LA1RB_0RC1LD : stepn tmm_0RB1LD_1RC0LA_1LA1RB_0RC1LD 20 InitES = Some (lift (Cc 1)).
Proof.
  assert (H : match csteps tmm_0RB1LD_1RC0LA_1LA1RB_0RC1LD 20 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tmm_0RB1LD_1RC0LA_1LA1RB_0RC1LD 20 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** the quasihalt witness: a pinned instruction fired in the prefix *)
Lemma wit_0RB1LD_1RC0LA_1LA1RB_0RC1LD : existsb (fun tg => cfires tmm_0RB1LD_1RC0LA_1LA1RB_0RC1LD c0 20 tg) pins_0RB1LD_1RC0LA_1LA1RB_0RC1LD = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_0RB1LD_1RC0LA_1LA1RB_0RC1LD : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_0RB1LD_1RC0LA_1LA1RB_0RC1LD = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_0RB1LD_1RC0LA_1LA1RB_0RC1LD p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB1LD_1RC0LA_1LA1RB_0RC1LD p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_0RB1LD_1RC0LA_1LA1RB_0RC1LD : forall t, ~ In t pins_0RB1LD_1RC0LA_1LA1RB_0RC1LD ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n c', 0 < n /\ csteps tm n (Cc p0) = Some c'
                         /\ lift c' = lift (Cc (Pos.succ p0)))
    by exact lapi_0RB1LD_1RC0LA_1LA1RB_0RC1LD.
  destruct t as [q b]; destruct q, b.
  - (* A0: pinned *)
    exfalso. apply Hnp. apply tr_inb_spec. reflexivity.
  - (* A1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StA, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1LD_1RC0LA_1LA1RB_0RC1LD [SCycL 2 0; SWin 2; SWinL 2] (StA, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* B0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StB, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1LD_1RC0LA_1LA1RB_0RC1LD [] (StB, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* B1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StB, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1LD_1RC0LA_1LA1RB_0RC1LD [SCycL 2 0; SWin 2; SWinL 4; SCycR 2; SWin 1; SWinR 3] (StB, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* C0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StC, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1LD_1RC0LA_1LA1RB_0RC1LD [SCycL 2 0; SWin 2; SWinL 1] (StC, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* C1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StC, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1LD_1RC0LA_1LA1RB_0RC1LD [SCycL 2 0; SWin 1] (StC, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* D0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StD, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1LD_1RC0LA_1LA1RB_0RC1LD [SCycL 2 0; SWin 2; SWinL 4; SCycR 2; SWin 1; SWinR 1] (StD, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* D1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StD, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1LD_1RC0LA_1LA1RB_0RC1LD [SCycL 2 0; SWin 2; SWinL 3] (StD, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
Qed.

Theorem qhtrm_0RB1LD_1RC0LA_1LA1RB_0RC1LD : NonHalt tmm_0RB1LD_1RC0LA_1LA1RB_0RC1LD /\ QHBoundTr 32779478 tmm_0RB1LD_1RC0LA_1LA1RB_0RC1LD /\ QuasiHaltsTr tmm_0RB1LD_1RC0LA_1LA1RB_0RC1LD.
Proof.
  apply (lap_qh_stage tmm_0RB1LD_1RC0LA_1LA1RB_0RC1LD pins_0RB1LD_1RC0LA_1LA1RB_0RC1LD Cc 1 20 32779478).
  - exact bootq_0RB1LD_1RC0LA_1LA1RB_0RC1LD.
  - intros p _. apply lap_0RB1LD_1RC0LA_1LA1RB_0RC1LD.
  - intros t Ht p _. apply fire_0RB1LD_1RC0LA_1LA1RB_0RC1LD. exact Ht.
  - exact wit_0RB1LD_1RC0LA_1LA1RB_0RC1LD.
  - vm_cast_no_check (eq_refl true).
Qed.

Theorem qhtr_0RB1LD_1RC0LA_1LA1RB_0RC1LD : NonHalt tm_0RB1LD_1RC0LA_1LA1RB_0RC1LD /\ QHBoundTr 32779478 tm_0RB1LD_1RC0LA_1LA1RB_0RC1LD /\ QuasiHaltsTr tm_0RB1LD_1RC0LA_1LA1RB_0RC1LD.
Proof. apply (qh_triple_unmirror 32779478 tm_0RB1LD_1RC0LA_1LA1RB_0RC1LD). rewrite mirror_ok_0RB1LD_1RC0LA_1LA1RB_0RC1LD. exact qhtrm_0RB1LD_1RC0LA_1LA1RB_0RC1LD. Qed.
