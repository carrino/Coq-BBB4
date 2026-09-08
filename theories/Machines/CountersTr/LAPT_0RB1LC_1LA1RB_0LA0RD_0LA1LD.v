(** * LAPT_0RB1LC_1LA1RB_0LA0RD_0LA1LD: TRANSITION-LEVEL board for machine 0RB1LC_1LA1RB_0LA0RD_0LA1LD, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Ap_Alph_10_11_11 digit alphabet (Alph_10_11_11.v), anchored at

      Cc p = (StB, (Ap_Alph_10_11_11 p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  6*j+10 steps
      overflow  (cview p = (S j, None)):   6*j+13 steps

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
                                  MonoCounter JpCounter Alph_10_11_11 LapCertGlue LapCertGlueLift.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
From BBB4 Require Import BBBT4_Statement.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr.
Import ListNotations.

Definition mk_0RB1LC_1LA1RB_0LA0RD_0LA1LD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB1LC_1LA1RB_0LA0RD_0LA1LD.

(** 0RB1LC_1LA1RB_0LA0RD_0LA1LD *)
(** 0RB1LC_1LA1RB_0LA0RD_0LA1LD -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB1LC_1LA1RB_0LA0RD_0LA1LD : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S1 DL StC
  | StB, S0 => mk S1 DL StA | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S0 DL StA | StC, S1 => mk S0 DR StD
  | StD, S0 => mk S0 DL StA | StD, S1 => mk S1 DL StD end.

(** Its mirror 0LB1RC_1RA1LB_0RA0LD_0RA1RD: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB1LC_1LA1RB_0LA0RD_0LA1LD : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S1 DR StC
  | StB, S0 => mk S1 DR StA | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S0 DR StA | StC, S1 => mk S0 DL StD
  | StD, S0 => mk S0 DR StA | StD, S1 => mk S1 DR StD end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_0RB1LC_1LA1RB_0LA0RD_0LA1LD : list Instr := [].
Definition tmw_0RB1LC_1LA1RB_0LA0RD_0LA1LD : TM := tm_wrap_trs tmm_0RB1LC_1LA1RB_0LA0RD_0LA1LD pins_0RB1LC_1LA1RB_0LA0RD_0LA1LD.
Local Notation tm := tmw_0RB1LC_1LA1RB_0LA0RD_0LA1LD.

Lemma mirror_ok_0RB1LC_1LA1RB_0LA0RD_0LA1LD : mirror_tm tm_0RB1LC_1LA1RB_0LA0RD_0LA1LD = tmm_0RB1LC_1LA1RB_0LA0RD_0LA1LD.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_0RB1LC_1LA1RB_0LA0RD_0LA1LD (p : positive) : cconf := (StB, (Ap_Alph_10_11_11 p ++ [S0], S0, [])).
Local Notation Cc := Cc_0RB1LC_1LA1RB_0LA0RD_0LA1LD.

(** ** The certificate *)

Definition A0_0RB1LC_1LA1RB_0LA0RD_0LA1LD : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition A1_0RB1LC_1LA1RB_0LA0RD_0LA1LD : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S0] [] 0 0 []).
Definition chi_0RB1LC_1LA1RB_0LA0RD_0LA1LD : list lstep := [SWinR 2; SCycL 2 0; SWin 6; SCycR 4; SWin 2].

Lemma run_int_0RB1LC_1LA1RB_0LA0RD_0LA1LD : srun tm false true chi_0RB1LC_1LA1RB_0LA0RD_0LA1LD A0_0RB1LC_1LA1RB_0LA0RD_0LA1LD = Some (A1_0RB1LC_1LA1RB_0LA0RD_0LA1LD, 6, 10).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB1LC_1LA1RB_0LA0RD_0LA1LD : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_0RB1LC_1LA1RB_0LA0RD_0LA1LD : sconf := mkC StB (mkS [] [S1;S0] 1 1 [S1;S1]) S0 (mkS [S0] [] 0 0 []).
Definition cho_0RB1LC_1LA1RB_0LA0RD_0LA1LD : list lstep := [SWinR 2; SCycL 2 0; SWin 8; SCycR 4; SWin 1; SWinR 2; SRotL 1; SFoldL 1].

Lemma run_ovf_0RB1LC_1LA1RB_0LA0RD_0LA1LD : srun tm true true cho_0RB1LC_1LA1RB_0LA0RD_0LA1LD B0_0RB1LC_1LA1RB_0LA0RD_0LA1LD = Some (B1_0RB1LC_1LA1RB_0LA0RD_0LA1LD, 6, 13).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_0RB1LC_1LA1RB_0LA0RD_0LA1LD : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Ap_Alph_10_11_11 q0 ++ [S0]) [] j A0_0RB1LC_1LA1RB_0LA0RD_0LA1LD.
Proof.
  intros p j q0 E. destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (H1 & _).
  unfold Cc_0RB1LC_1LA1RB_0LA0RD_0LA1LD, cden, A0_0RB1LC_1LA1RB_0LA0RD_0LA1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

(** The lap ends on [S0] where the anchor has [] -- one trailing blank,
    which [lift] cannot see. *)
Lemma gei_0RB1LC_1LA1RB_0LA0RD_0LA1LD : forall p j q0, cview p = (j, Some q0) ->
  lift (cden (Ap_Alph_10_11_11 q0 ++ [S0]) [] j A1_0RB1LC_1LA1RB_0LA0RD_0LA1LD) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (_ & H2).
  unfold Cc_0RB1LC_1LA1RB_0LA0RD_0LA1LD, cden, A1_0RB1LC_1LA1RB_0LA0RD_0LA1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S0]) with (([]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_0RB1LC_1LA1RB_0LA0RD_0LA1LD : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  exists (6 * j + 10), (cden (Ap_Alph_10_11_11 q0 ++ [S0]) [] j A1_0RB1LC_1LA1RB_0LA0RD_0LA1LD).
  split; [lia|]. split; [| exact (gei_0RB1LC_1LA1RB_0LA0RD_0LA1LD p j q0 E)].
  rewrite (gsi_0RB1LC_1LA1RB_0LA0RD_0LA1LD p j q0 E).
  exact (srun_sound tm false true chi_0RB1LC_1LA1RB_0LA0RD_0LA1LD A0_0RB1LC_1LA1RB_0LA0RD_0LA1LD A1_0RB1LC_1LA1RB_0LA0RD_0LA1LD 6 10
           run_int_0RB1LC_1LA1RB_0LA0RD_0LA1LD (Ap_Alph_10_11_11 q0 ++ [S0]) [] j
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma gso_0RB1LC_1LA1RB_0LA0RD_0LA1LD : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_0RB1LC_1LA1RB_0LA0RD_0LA1LD.
Proof.
  intros p j E. destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p j E) as (H1 & _).
  unfold Cc_0RB1LC_1LA1RB_0LA0RD_0LA1LD, cden, B0_0RB1LC_1LA1RB_0LA0RD_0LA1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_0RB1LC_1LA1RB_0LA0RD_0LA1LD : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_0RB1LC_1LA1RB_0LA0RD_0LA1LD : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB1LC_1LA1RB_0LA0RD_0LA1LD) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_0RB1LC_1LA1RB_0LA0RD_0LA1LD
             = (StB, (rep [S1;S0] (S j) ++ [S1;S1], S0, ([]) ++ [S0]))).
  { unfold cden, B1_0RB1LC_1LA1RB_0LA0RD_0LA1LD, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StB, ((rep [S1;S0] (S j) ++ [S1;S1]) ++ [S0], S0, []))).
  { unfold Cc_0RB1LC_1LA1RB_0LA0RD_0LA1LD. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lift_app_blank. rewrite !lbl_0RB1LC_1LA1RB_0LA0RD_0LA1LD. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_0RB1LC_1LA1RB_0LA0RD_0LA1LD : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB1LC_1LA1RB_0LA0RD_0LA1LD p j q0 E) as (n & c' & Hn & Hrun & Hlift).
    exists n, c'. split; [exact Hrun | split; [exact Hlift | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_0RB1LC_1LA1RB_0LA0RD_0LA1LD B0_0RB1LC_1LA1RB_0LA0RD_0LA1LD B1_0RB1LC_1LA1RB_0LA0RD_0LA1LD 6 13 p j' [] []).
    + exact run_ovf_0RB1LC_1LA1RB_0LA0RD_0LA1LD.
    + reflexivity.
    + reflexivity.
    + exact (gso_0RB1LC_1LA1RB_0LA0RD_0LA1LD p j' E).
    + exact (geo_0RB1LC_1LA1RB_0LA0RD_0LA1LD p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_0RB1LC_1LA1RB_0LA0RD_0LA1LD : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 8.
  assert (H : match csteps tm 8 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 8 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_0RB1LC_1LA1RB_0LA0RD_0LA1LD : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_0RB1LC_1LA1RB_0LA0RD_0LA1LD = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_0RB1LC_1LA1RB_0LA0RD_0LA1LD p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB1LC_1LA1RB_0LA0RD_0LA1LD p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_0RB1LC_1LA1RB_0LA0RD_0LA1LD : forall t, ~ In t pins_0RB1LC_1LA1RB_0LA0RD_0LA1LD ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n c', 0 < n /\ csteps tm n (Cc p0) = Some c'
                         /\ lift c' = lift (Cc (Pos.succ p0)))
    by exact lapi_0RB1LC_1LA1RB_0LA0RD_0LA1LD.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StA, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1LC_1LA1RB_0LA0RD_0LA1LD [SWinR 1] (StA, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* A1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StA, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1LC_1LA1RB_0LA0RD_0LA1LD [SWinR 2; SCycL 2 0; SWin 4] (StA, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* B0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StB, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1LC_1LA1RB_0LA0RD_0LA1LD [] (StB, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* B1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StB, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1LC_1LA1RB_0LA0RD_0LA1LD [SWinR 2] (StB, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* C0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StC, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1LC_1LA1RB_0LA0RD_0LA1LD [SWinR 2; SCycL 2 0; SWin 8; SCycR 4; SWin 1] (StC, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* C1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StC, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1LC_1LA1RB_0LA0RD_0LA1LD [SWinR 2; SCycL 2 0; SWin 5] (StC, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* D0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StD, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1LC_1LA1RB_0LA0RD_0LA1LD [SWinR 2; SCycL 2 0; SWin 7] (StD, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* D1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StD, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1LC_1LA1RB_0LA0RD_0LA1LD [SWinR 2; SCycL 2 0; SWin 6] (StD, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
Qed.

Theorem nqhtrm_0RB1LC_1LA1RB_0LA0RD_0LA1LD : NeverQuasiHaltsTr tmm_0RB1LC_1LA1RB_0LA0RD_0LA1LD.
Proof.
  apply (glue_neverqhtr tmm_0RB1LC_1LA1RB_0LA0RD_0LA1LD pins_0RB1LC_1LA1RB_0LA0RD_0LA1LD Cc 1).
  - exact boot_0RB1LC_1LA1RB_0LA0RD_0LA1LD.
  - intros p _. apply lap_0RB1LC_1LA1RB_0LA0RD_0LA1LD.
  - intros t Ht p _. apply fire_0RB1LC_1LA1RB_0LA0RD_0LA1LD. exact Ht.
Qed.

Theorem nqhtr_0RB1LC_1LA1RB_0LA0RD_0LA1LD : NeverQuasiHaltsTr tm_0RB1LC_1LA1RB_0LA0RD_0LA1LD.
Proof. apply (neverqhtr_mirror tm_0RB1LC_1LA1RB_0LA0RD_0LA1LD). rewrite mirror_ok_0RB1LC_1LA1RB_0LA0RD_0LA1LD. exact nqhtrm_0RB1LC_1LA1RB_0LA0RD_0LA1LD. Qed.

Theorem nonhalt_0RB1LC_1LA1RB_0LA0RD_0LA1LD : NonHalt tm_0RB1LC_1LA1RB_0LA0RD_0LA1LD.
Proof. apply never_qh_tr_nonhalt, nqhtr_0RB1LC_1LA1RB_0LA0RD_0LA1LD. Qed.
