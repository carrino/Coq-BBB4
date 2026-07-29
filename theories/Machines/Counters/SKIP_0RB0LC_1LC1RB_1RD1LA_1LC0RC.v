(** * SKIP_0RB0LC_1LC1RB_1RD1LA_1LC0RC: machine 0RB0LC_1LC1RB_1RD1LA_1LC0RC, boarded by CERTIFICATE (SKIP route).

    Auto-emitted by tools/counters/skipcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  A left-growth binary
    counter under the Ap_Alph_10_11_11 digit alphabet (Alph_10_11_11.v) that NEVER RESTS AT
    A POWER OF TWO: the overflow lap runs fill(2^K - 1) -> 2^K + 1, so the
    skipped value exists only as the machine's transient form
    (WAVE26 section 8).  The anchor family carries VIRTUAL anchors there:

      Cc p = VIRT k at p = 2^(S k), else E p ++ tail

    Laps are DATA for [Checkers/LapDecider.v], run by the kernel through
    [vm_compute] and discharged by [srun_sound]:

      interior  (pexp p = None):   4*j+4 steps, exact
      fill      (cview (S j, None)): 0*j+1 steps, exact, onto the VIRTUAL anchor
      virt      (pexp p = Some (S k)): 4*k+8 steps, up to [lift]

    [Counters/SkipGlue.v] supplies the power-of-two view and the reach/vis
    plumbing; the closer is [LapGlue.glue_neverqh] directly.

    Differentially validated against the raw simulator on EVERY branch --
    step counts AND configurations -- for 198 anchors (s=1).
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape LapGlue MonoCounter JpCounter
                                  Alph_10_11_11 LapCertGlue LapCertGlueLift
                                  IXPGadgets SkipGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_0RB0LC_1LC1RB_1RD1LA_1LC0RC (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB0LC_1LC1RB_1RD1LA_1LC0RC.

(** 0RB0LC_1LC1RB_1RD1LA_1LC0RC *)
(** 0RB0LC_1LC1RB_1RD1LA_1LC0RC -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB0LC_1LC1RB_1RD1LA_1LC0RC : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S0 DL StC
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S1 DL StC | StD, S1 => mk S0 DR StC end.

(** Its mirror 0LB0RC_1RC1LB_1LD1RA_1RC0LC: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB0LC_1LC1RB_1RD1LA_1LC0RC : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S0 DR StC
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S1 DL StD | StC, S1 => mk S1 DR StA
  | StD, S0 => mk S1 DR StC | StD, S1 => mk S0 DL StC end.
Local Notation tm := tmm_0RB0LC_1LC1RB_1RD1LA_1LC0RC.

Lemma mirror_ok_0RB0LC_1LC1RB_1RD1LA_1LC0RC : mirror_tm tm_0RB0LC_1LC1RB_1RD1LA_1LC0RC = tmm_0RB0LC_1LC1RB_1RD1LA_1LC0RC.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_0RB0LC_1LC1RB_1RD1LA_1LC0RC (p : positive) : cconf :=
  match pexp p with
  | Some (S k) => (StB, ([] ++ rep [S1;S1] k ++ [S1;S0], S1, [S0]))
  | _ => (StA, (Ap_Alph_10_11_11 p ++ [S0], S0, []))
  end.
Local Notation Cc := Cc_0RB0LC_1LC1RB_1RD1LA_1LC0RC.

Definition virt_0RB0LC_1LC1RB_1RD1LA_1LC0RC (p : positive) : bool := match pexp p with Some (S _) => true | _ => false end.
Local Notation virt := virt_0RB0LC_1LC1RB_1RD1LA_1LC0RC.

(** ** The certificate *)

Definition A0_0RB0LC_1LC1RB_1RD1LA_1LC0RC : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition A1_0RB0LC_1LC1RB_1RD1LA_1LC0RC : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chi_0RB0LC_1LC1RB_1RD1LA_1LC0RC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_int_0RB0LC_1LC1RB_1RD1LA_1LC0RC : srun tm false true chi_0RB0LC_1LC1RB_1RD1LA_1LC0RC A0_0RB0LC_1LC1RB_1RD1LA_1LC0RC = Some (A1_0RB0LC_1LC1RB_1RD1LA_1LC0RC, 4, 4).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB0LC_1LC1RB_1RD1LA_1LC0RC : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S1;S0]) S0 (mkS [] [] 0 0 []).
Definition V0_0RB0LC_1LC1RB_1RD1LA_1LC0RC : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S0]) S1 (mkS [S0] [] 0 0 []).
Definition chf_0RB0LC_1LC1RB_1RD1LA_1LC0RC : list lstep := [SRotL 1; SWin 1].

Lemma run_fill_0RB0LC_1LC1RB_1RD1LA_1LC0RC : srun tm true true chf_0RB0LC_1LC1RB_1RD1LA_1LC0RC B0_0RB0LC_1LC1RB_1RD1LA_1LC0RC = Some (V0_0RB0LC_1LC1RB_1RD1LA_1LC0RC, 0, 1).
Proof. vm_compute. reflexivity. Qed.

Definition E1_0RB0LC_1LC1RB_1RD1LA_1LC0RC : sconf := mkC StA (mkS [S1;S1] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chv_0RB0LC_1LC1RB_1RD1LA_1LC0RC : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWin 3; SWinR 1].

Lemma run_virt_0RB0LC_1LC1RB_1RD1LA_1LC0RC : srun tm true true chv_0RB0LC_1LC1RB_1RD1LA_1LC0RC V0_0RB0LC_1LC1RB_1RD1LA_1LC0RC = Some (E1_0RB0LC_1LC1RB_1RD1LA_1LC0RC, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

(** The alphabet at a power of two: all digits clear over the terminator. *)
Lemma apow_0RB0LC_1LC1RB_1RD1LA_1LC0RC : forall r k, pexp r = Some k -> Ap_Alph_10_11_11 r = rep [S1;S0] k ++ [S1;S1].
Proof.
  induction r; intros k H; simpl in H.
  - discriminate.
  - destruct (pexp r) as [k'|] eqn:E; [|discriminate].
    injection H as <-. simpl. rewrite (IHr k' eq_refl). reflexivity.
  - injection H as <-. reflexivity.
Qed.

Lemma gsi_0RB0LC_1LC1RB_1RD1LA_1LC0RC : forall p j q0, cview p = (j, Some q0) -> pexp p = None ->
  Cc p = cden (Ap_Alph_10_11_11 q0 ++ [S0]) [] j A0_0RB0LC_1LC1RB_1RD1LA_1LC0RC.
Proof.
  intros p j q0 E Hx . unfold Cc_0RB0LC_1LC1RB_1RD1LA_1LC0RC. rewrite Hx.
  destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (H1 & _).
  unfold cden, A0_0RB0LC_1LC1RB_1RD1LA_1LC0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gei_0RB0LC_1LC1RB_1RD1LA_1LC0RC : forall p j q0, cview p = (j, Some q0) -> pexp p = None ->
  cden (Ap_Alph_10_11_11 q0 ++ [S0]) [] j A1_0RB0LC_1LC1RB_1RD1LA_1LC0RC = Cc (Pos.succ p).
Proof.
  intros p j q0 E Hx . unfold Cc_0RB0LC_1LC1RB_1RD1LA_1LC0RC.
  rewrite (pexp_succ_int p j q0 E).
  destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (_ & H2).
  unfold cden, A1_0RB0LC_1LC1RB_1RD1LA_1LC0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_0RB0LC_1LC1RB_1RD1LA_1LC0RC : forall p j q0, cview p = (j, Some q0) -> pexp p = None ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hx . exists (4 * j + 4). split; [lia|].
  rewrite (gsi_0RB0LC_1LC1RB_1RD1LA_1LC0RC p j q0 E Hx ).
  rewrite (srun_sound tm false true chi_0RB0LC_1LC1RB_1RD1LA_1LC0RC A0_0RB0LC_1LC1RB_1RD1LA_1LC0RC A1_0RB0LC_1LC1RB_1RD1LA_1LC0RC 4 4
             run_int_0RB0LC_1LC1RB_1RD1LA_1LC0RC (Ap_Alph_10_11_11 q0 ++ [S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_0RB0LC_1LC1RB_1RD1LA_1LC0RC p j q0 E Hx ).
Qed.

Lemma gso_0RB0LC_1LC1RB_1RD1LA_1LC0RC : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_0RB0LC_1LC1RB_1RD1LA_1LC0RC.
Proof.
  intros p j E . unfold Cc_0RB0LC_1LC1RB_1RD1LA_1LC0RC.
  destruct (pexp p) as [[|k]|] eqn:Epx.
  - rewrite (pexp_zero p Epx) in E |- *.
    cbn in E. injection E as <-. reflexivity.
  - exfalso. exact (pexp_not_fill p j k E Epx).
  - destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p j E) as (H1 & _).
    unfold cden, B0_0RB0LC_1LC1RB_1RD1LA_1LC0RC; cbn [c_st c_l c_h c_r].
    unfold sden; cbn [s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

(** The fill lap lands EXACTLY on the virtual anchor. *)
Lemma geov_0RB0LC_1LC1RB_1RD1LA_1LC0RC : forall p j, cview p = (S j, None) ->
  cden [] [] j V0_0RB0LC_1LC1RB_1RD1LA_1LC0RC = Cc (Pos.succ p).
Proof.
  intros p j E. unfold Cc_0RB0LC_1LC1RB_1RD1LA_1LC0RC.
  rewrite (pexp_succ_fill p (S j) E).
  unfold cden, V0_0RB0LC_1LC1RB_1RD1LA_1LC0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  first [ reflexivity
        | cbn [rep app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapf_0RB0LC_1LC1RB_1RD1LA_1LC0RC : forall p j, cview p = (S j, None) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j E . exists (0 * j + 1). split; [lia|].
  rewrite (gso_0RB0LC_1LC1RB_1RD1LA_1LC0RC p j E ).
  rewrite (srun_sound tm true true chf_0RB0LC_1LC1RB_1RD1LA_1LC0RC B0_0RB0LC_1LC1RB_1RD1LA_1LC0RC V0_0RB0LC_1LC1RB_1RD1LA_1LC0RC 0 1
             run_fill_0RB0LC_1LC1RB_1RD1LA_1LC0RC [] [] j
             ltac:(reflexivity) ltac:(reflexivity)).
  f_equal. exact (geov_0RB0LC_1LC1RB_1RD1LA_1LC0RC p j E).
Qed.

Lemma lbl_0RB0LC_1LC1RB_1RD1LA_1LC0RC : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma gsv_0RB0LC_1LC1RB_1RD1LA_1LC0RC : forall p k, pexp p = Some (S k) ->
  Cc p = cden [] [] k V0_0RB0LC_1LC1RB_1RD1LA_1LC0RC.
Proof.
  intros p k Hx. unfold Cc_0RB0LC_1LC1RB_1RD1LA_1LC0RC. rewrite Hx.
  unfold cden, V0_0RB0LC_1LC1RB_1RD1LA_1LC0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia.
  first [ reflexivity
        | cbn [rep app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

(** The landing: E(2^(S k) + 1) = uS ++ rep uD k ++ soD, one trailing
    blank short of the anchor tail -- invisible to [lift]. *)
Lemma gev_0RB0LC_1LC1RB_1RD1LA_1LC0RC : forall p k, pexp p = Some (S k) ->
  lift (cden [] [] k E1_0RB0LC_1LC1RB_1RD1LA_1LC0RC) = lift (Cc (Pos.succ p)).
Proof.
  intros p k Hx.
  destruct (pexp_shape p k Hx) as (r & -> & Hr).
  unfold Cc_0RB0LC_1LC1RB_1RD1LA_1LC0RC. cbn [Pos.succ pexp].
  assert (HD : cden [] [] k E1_0RB0LC_1LC1RB_1RD1LA_1LC0RC = (StA, ([S1;S1] ++ rep [S1;S0] k ++ [S1;S1], S0, []))).
  { unfold cden, E1_0RB0LC_1LC1RB_1RD1LA_1LC0RC, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * k + 0) with k by lia.
    first [ reflexivity
      | cbn [rep app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : (StA, (Ap_Alph_10_11_11 (xI r) ++ [S0], S0, []))
             = (StA, (([S1;S1] ++ rep [S1;S0] k ++ [S1;S1]) ++ [S0], S0, [])) :> cconf).
  { simpl Ap_Alph_10_11_11. rewrite (apow_0RB0LC_1LC1RB_1RD1LA_1LC0RC r k Hr).
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_0RB0LC_1LC1RB_1RD1LA_1LC0RC. reflexivity.
Qed.

Lemma lapv_0RB0LC_1LC1RB_1RD1LA_1LC0RC : forall p k, pexp p = Some (S k) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p k Hx.
  exists (4 * k + 8), (cden [] [] k E1_0RB0LC_1LC1RB_1RD1LA_1LC0RC).
  split; [lia|]. split; [| exact (gev_0RB0LC_1LC1RB_1RD1LA_1LC0RC p k Hx)].
  rewrite (gsv_0RB0LC_1LC1RB_1RD1LA_1LC0RC p k Hx).
  exact (srun_sound tm true true chv_0RB0LC_1LC1RB_1RD1LA_1LC0RC V0_0RB0LC_1LC1RB_1RD1LA_1LC0RC E1_0RB0LC_1LC1RB_1RD1LA_1LC0RC 4 8
           run_virt_0RB0LC_1LC1RB_1RD1LA_1LC0RC [] [] k ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** ** The lap *)

Lemma lap_0RB0LC_1LC1RB_1RD1LA_1LC0RC : forall p, (9 <= p)%positive -> exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p Hp. destruct (cview p) as [j oq] eqn:E; destruct oq as [q0|].
  - destruct (pexp p) as [[|k]|] eqn:Epx.
    + rewrite (pexp_zero p Epx) in E. cbn in E. discriminate.
    + destruct (lapv_0RB0LC_1LC1RB_1RD1LA_1LC0RC p k Epx) as (n & c' & Hn & Hrun & Hl).
      exists n, c'. split; [exact Hrun | split; [exact Hl | exact Hn]].
    + destruct (lapi_0RB0LC_1LC1RB_1RD1LA_1LC0RC p j q0 E Epx) as (n & Hn & Hrun).
      exists n, (Cc (Pos.succ p)).
      split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    destruct (lapf_0RB0LC_1LC1RB_1RD1LA_1LC0RC p j' E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
Qed.

(** ** SkipGlue's hypotheses *)

Lemma hint_0RB0LC_1LC1RB_1RD1LA_1LC0RC : forall p j q0, (9 <= p)%positive ->
  cview p = (j, Some q0) -> virt p = false ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 _ E Hv. unfold virt_0RB0LC_1LC1RB_1RD1LA_1LC0RC in Hv.
  destruct (pexp p) as [[|k]|] eqn:Epx.
  - rewrite (pexp_zero p Epx) in E. cbn in E. discriminate.
  - discriminate Hv.
  - exact (lapi_0RB0LC_1LC1RB_1RD1LA_1LC0RC p j q0 E Epx).
Qed.

Lemma hsucc_0RB0LC_1LC1RB_1RD1LA_1LC0RC : forall p j q0, cview p = (j, Some q0) ->
  virt p = false -> virt (Pos.succ p) = false.
Proof.
  intros p j q0 E _. unfold virt_0RB0LC_1LC1RB_1RD1LA_1LC0RC.
  rewrite (pexp_succ_int p j q0 E). reflexivity.
Qed.

Lemma hvlap_0RB0LC_1LC1RB_1RD1LA_1LC0RC : forall p, (9 <= p)%positive -> virt p = true ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p _ Hv. unfold virt_0RB0LC_1LC1RB_1RD1LA_1LC0RC in Hv.
  destruct (pexp p) as [[|k]|] eqn:Epx; try discriminate.
  exact (lapv_0RB0LC_1LC1RB_1RD1LA_1LC0RC p k Epx).
Qed.

Lemma hvrun_0RB0LC_1LC1RB_1RD1LA_1LC0RC : forall p, (9 <= p)%positive -> virt p = true ->
  virt (Pos.succ p) = true -> virt (Pos.succ (Pos.succ p)) = false.
Proof.
  intros p _ H1 H2. exfalso. unfold virt_0RB0LC_1LC1RB_1RD1LA_1LC0RC in *.
  destruct (pexp p) as [[|k]|] eqn:E1; try discriminate.
  rewrite (pexp_succ_virt p k E1) in H2. discriminate.
Qed.

(** ** Bootstrap *)

Lemma boot_0RB0LC_1LC1RB_1RD1LA_1LC0RC : exists t0, stepn tm t0 InitES = Some (lift (Cc 9)).
Proof.
  exists 37.
  assert (H : match csteps tm 37 c0 with
              | Some c => ceqb c (Cc 9) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 37 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the overflow sweep (fill chain) or in the
    virtual laps behind it; [SkipGlue.vis_via_skip] carries the fill-anchor
    witnesses to every anchor at or above p0. *)

Lemma viso_0RB0LC_1LC1RB_1RD1LA_1LC0RC : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_0RB0LC_1LC1RB_1RD1LA_1LC0RC = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E .
  apply (vis_of_run tm Cc true true l B0_0RB0LC_1LC1RB_1RD1LA_1LC0RC p j [] []);
    [exact Hst | ltac:(intro; reflexivity) | reflexivity
     | exact (gso_0RB0LC_1LC1RB_1RD1LA_1LC0RC p j E )].
Qed.



Lemma vis_0RB0LC_1LC1RB_1RD1LA_1LC0RC : forall p q, (9 <= p)%positive ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q Hp.
  apply (vis_via_skip tm Cc virt 9 hint_0RB0LC_1LC1RB_1RD1LA_1LC0RC hsucc_0RB0LC_1LC1RB_1RD1LA_1LC0RC hvlap_0RB0LC_1LC1RB_1RD1LA_1LC0RC
           hvrun_0RB0LC_1LC1RB_1RD1LA_1LC0RC q); [| exact Hp].
  intros p1 j1 Hp1 E1.

  destruct q.
  - (* StA: the anchor state *)
    rewrite (gso_0RB0LC_1LC1RB_1RD1LA_1LC0RC p1 j1 E1).
    exists 0. eexists. split; reflexivity.
  - (* StB *)
    exact (viso_0RB0LC_1LC1RB_1RD1LA_1LC0RC [SRotL 1; SWin 1] StB
             ltac:(vm_compute; reflexivity) p1 j1 E1).
  - (* StC *)
    exact (viso_0RB0LC_1LC1RB_1RD1LA_1LC0RC [SRotL 1; SWin 1; SCycL 2 0; SWin 3] StC
             ltac:(vm_compute; reflexivity) p1 j1 E1).
  - (* StD *)
    exact (viso_0RB0LC_1LC1RB_1RD1LA_1LC0RC [SRotL 1; SWin 1; SCycL 2 0; SWin 4; SCycR 2; SWin 2] StD
             ltac:(vm_compute; reflexivity) p1 j1 E1).
Qed.

Theorem nqhm_0RB0LC_1LC1RB_1RD1LA_1LC0RC : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 9). - exact boot_0RB0LC_1LC1RB_1RD1LA_1LC0RC. - intros p Hp. apply (lap_0RB0LC_1LC1RB_1RD1LA_1LC0RC p Hp). - intros p q Hp. apply (vis_0RB0LC_1LC1RB_1RD1LA_1LC0RC p q Hp). Qed.

Theorem nqh_0RB0LC_1LC1RB_1RD1LA_1LC0RC : NeverQuasiHaltsSt tm_0RB0LC_1LC1RB_1RD1LA_1LC0RC.
Proof. apply (mirror_never_qh tm_0RB0LC_1LC1RB_1RD1LA_1LC0RC). rewrite mirror_ok_0RB0LC_1LC1RB_1RD1LA_1LC0RC. exact nqhm_0RB0LC_1LC1RB_1RD1LA_1LC0RC. Qed.

Theorem nonhalt_0RB0LC_1LC1RB_1RD1LA_1LC0RC : NonHalt tm_0RB0LC_1LC1RB_1RD1LA_1LC0RC.
Proof. apply never_qh_nonhalt, nqh_0RB0LC_1LC1RB_1RD1LA_1LC0RC. Qed.
