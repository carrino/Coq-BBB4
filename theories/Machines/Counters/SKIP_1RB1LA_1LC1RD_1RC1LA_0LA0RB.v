(** * SKIP_1RB1LA_1LC1RD_1RC1LA_0LA0RB: machine 1RB1LA_1LC1RD_1RC1LA_0LA0RB, boarded by CERTIFICATE (SKIP route).

    Auto-emitted by tools/counters/skipcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  A left-growth binary
    counter under the Ap_Alph_10_11_11 digit alphabet (Alph_10_11_11.v) that NEVER RESTS AT
    A POWER OF TWO: the overflow lap runs fill(2^K - 1) -> 2^K + 2, so the
    skipped values exist only as the machine's transient forms
    (WAVE26 section 8).  The anchor family carries VIRTUAL anchors there:

      Cc p = VIRT anchors at p = 2^(S k) and 2^(S k)+1, else E p ++ tail

    Laps are DATA for [Checkers/LapDecider.v], run by the kernel through
    [vm_compute] and discharged by [srun_sound]:

      interior  (pexp p = None):   4*j+4 steps, exact
      fill      (cview (S j, None)): 0*j+1 steps, exact, onto the VIRTUAL anchor
      virt      (pexp p = Some (S k)): 0*k+1 steps, exact, onto the SECOND virtual anchor
      virt2     (pexpi p = Some (S k)): 4*k+17 steps, up to [lift]

    [Counters/SkipGlue.v] supplies the power-of-two view and the reach/vis
    plumbing; the closer is [LapGlue.glue_neverqh] directly.

    Differentially validated against the raw simulator on EVERY branch --
    step counts AND configurations -- for 197 anchors (s=2).
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter JpCounter
                                  Alph_10_11_11 LapCertGlue LapCertGlueLift
                                  IXPGadgets SkipGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_1RB1LA_1LC1RD_1RC1LA_0LA0RB (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1LA_1LC1RD_1RC1LA_0LA0RB.

(** 1RB1LA_1LC1RD_1RC1LA_0LA0RB *)
Definition tm_1RB1LA_1LC1RD_1RC1LA_0LA0RB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StA
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S1 DR StC | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S0 DL StA | StD, S1 => mk S0 DR StB end.
Local Notation tm := tm_1RB1LA_1LC1RD_1RC1LA_0LA0RB.

Definition Cc_1RB1LA_1LC1RD_1RC1LA_0LA0RB (p : positive) : cconf :=
  match pexp p with
  | Some (S k) => (StA, ([] ++ rep [S1;S1] k ++ [S1;S0], S1, [S0]))
  | _ =>
    match pexpi p with
    | Some k => (StA, ([] ++ rep [S1;S1] k ++ [S0], S1, [S1;S0]))
    | None => (StD, (Ap_Alph_10_11_11 p ++ [S0], S0, []))
    end
  end.
Local Notation Cc := Cc_1RB1LA_1LC1RD_1RC1LA_0LA0RB.

Definition virt_1RB1LA_1LC1RD_1RC1LA_0LA0RB (p : positive) : bool := match pexp p with
  | Some (S _) => true
  | _ => match pexpi p with Some _ => true | None => false end
  end.
Local Notation virt := virt_1RB1LA_1LC1RD_1RC1LA_0LA0RB.

(** ** The certificate *)

Definition A0_1RB1LA_1LC1RD_1RC1LA_0LA0RB : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition A1_1RB1LA_1LC1RD_1RC1LA_0LA0RB : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chi_1RB1LA_1LC1RD_1RC1LA_0LA0RB : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_int_1RB1LA_1LC1RD_1RC1LA_0LA0RB : srun tm false true chi_1RB1LA_1LC1RD_1RC1LA_0LA0RB A0_1RB1LA_1LC1RD_1RC1LA_0LA0RB = Some (A1_1RB1LA_1LC1RD_1RC1LA_0LA0RB, 4, 4).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB1LA_1LC1RD_1RC1LA_0LA0RB : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S1;S0]) S0 (mkS [] [] 0 0 []).
Definition V0_1RB1LA_1LC1RD_1RC1LA_0LA0RB : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S1 (mkS [S0] [] 0 0 []).
Definition chf_1RB1LA_1LC1RD_1RC1LA_0LA0RB : list lstep := [SRotL 1; SWin 1].

Lemma run_fill_1RB1LA_1LC1RD_1RC1LA_0LA0RB : srun tm true true chf_1RB1LA_1LC1RD_1RC1LA_0LA0RB B0_1RB1LA_1LC1RD_1RC1LA_0LA0RB = Some (V0_1RB1LA_1LC1RD_1RC1LA_0LA0RB, 0, 1).
Proof. vm_compute. reflexivity. Qed.

Definition W0_1RB1LA_1LC1RD_1RC1LA_0LA0RB : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S0]) S1 (mkS [S1;S0] [] 0 0 []).
Definition chv_1RB1LA_1LC1RD_1RC1LA_0LA0RB : list lstep := [SRotL 1; SWin 1].

Lemma run_virt_1RB1LA_1LC1RD_1RC1LA_0LA0RB : srun tm true true chv_1RB1LA_1LC1RD_1RC1LA_0LA0RB V0_1RB1LA_1LC1RD_1RC1LA_0LA0RB = Some (W0_1RB1LA_1LC1RD_1RC1LA_0LA0RB, 0, 1).
Proof. vm_compute. reflexivity. Qed.

(** The second virtual lap, from the REINDEXED W anchor (one unit copy in
    the prefix, so the source covers k = S k' only; k = 0 is p = 3 < p0). *)
Definition WS_1RB1LA_1LC1RD_1RC1LA_0LA0RB : sconf := mkC StA (mkS [S1;S1] [S1;S1] 1 0 [S0]) S1 (mkS [S1;S0] [] 0 0 []).
Definition E2_1RB1LA_1LC1RD_1RC1LA_0LA0RB : sconf := mkC StD (mkS [S1;S0;S1;S1] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chw_1RB1LA_1LC1RD_1RC1LA_0LA0RB : list lstep := [SWin 2; SCycL 2 0; SWin 2; SCycR 2; SWin 12; SWinR 1; SUnrotL 1].

Lemma run_virt2_1RB1LA_1LC1RD_1RC1LA_0LA0RB : srun tm true true chw_1RB1LA_1LC1RD_1RC1LA_0LA0RB WS_1RB1LA_1LC1RD_1RC1LA_0LA0RB = Some (E2_1RB1LA_1LC1RD_1RC1LA_0LA0RB, 4, 17).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

(** The alphabet at a power of two: all digits clear over the terminator. *)
Lemma apow_1RB1LA_1LC1RD_1RC1LA_0LA0RB : forall r k, pexp r = Some k -> Ap_Alph_10_11_11 r = rep [S1;S0] k ++ [S1;S1].
Proof.
  induction r; intros k H; simpl in H.
  - discriminate.
  - destruct (pexp r) as [k'|] eqn:E; [|discriminate].
    injection H as <-. simpl. rewrite (IHr k' eq_refl). reflexivity.
  - injection H as <-. reflexivity.
Qed.

Lemma gsi_1RB1LA_1LC1RD_1RC1LA_0LA0RB : forall p j q0, cview p = (j, Some q0) -> pexp p = None -> pexpi p = None ->
  Cc p = cden (Ap_Alph_10_11_11 q0 ++ [S0]) [] j A0_1RB1LA_1LC1RD_1RC1LA_0LA0RB.
Proof.
  intros p j q0 E Hx Hxi. unfold Cc_1RB1LA_1LC1RD_1RC1LA_0LA0RB. rewrite Hx. rewrite Hxi.
  destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (H1 & _).
  unfold cden, A0_1RB1LA_1LC1RD_1RC1LA_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gei_1RB1LA_1LC1RD_1RC1LA_0LA0RB : forall p j q0, cview p = (j, Some q0) -> pexp p = None -> pexpi p = None ->
  cden (Ap_Alph_10_11_11 q0 ++ [S0]) [] j A1_1RB1LA_1LC1RD_1RC1LA_0LA0RB = Cc (Pos.succ p).
Proof.
  intros p j q0 E Hx Hxi. unfold Cc_1RB1LA_1LC1RD_1RC1LA_0LA0RB.
  rewrite (pexp_succ_int p j q0 E). rewrite (pexpi_succ_int p j q0 E Hx).
  destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (_ & H2).
  unfold cden, A1_1RB1LA_1LC1RD_1RC1LA_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB1LA_1LC1RD_1RC1LA_0LA0RB : forall p j q0, cview p = (j, Some q0) -> pexp p = None -> pexpi p = None ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hx Hxi. exists (4 * j + 4). split; [lia|].
  rewrite (gsi_1RB1LA_1LC1RD_1RC1LA_0LA0RB p j q0 E Hx Hxi).
  rewrite (srun_sound tm false true chi_1RB1LA_1LC1RD_1RC1LA_0LA0RB A0_1RB1LA_1LC1RD_1RC1LA_0LA0RB A1_1RB1LA_1LC1RD_1RC1LA_0LA0RB 4 4
             run_int_1RB1LA_1LC1RD_1RC1LA_0LA0RB (Ap_Alph_10_11_11 q0 ++ [S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_1RB1LA_1LC1RD_1RC1LA_0LA0RB p j q0 E Hx Hxi).
Qed.

Lemma gso_1RB1LA_1LC1RD_1RC1LA_0LA0RB : forall p j, cview p = (S j, None) -> pexpi p = None ->
  Cc p = cden [] [] j B0_1RB1LA_1LC1RD_1RC1LA_0LA0RB.
Proof.
  intros p j E Hxi. unfold Cc_1RB1LA_1LC1RD_1RC1LA_0LA0RB.
  destruct (pexp p) as [[|k]|] eqn:Epx.
  - rewrite (pexp_zero p Epx) in E |- *.
    cbn in E. injection E as <-. reflexivity.
  - exfalso. exact (pexp_not_fill p j k E Epx).
  - rewrite Hxi. destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p j E) as (H1 & _).
    unfold cden, B0_1RB1LA_1LC1RD_1RC1LA_0LA0RB; cbn [c_st c_l c_h c_r].
    unfold sden; cbn [s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

(** The fill lap lands EXACTLY on the virtual anchor. *)
Lemma geov_1RB1LA_1LC1RD_1RC1LA_0LA0RB : forall p j, cview p = (S j, None) ->
  cden [] [] j V0_1RB1LA_1LC1RD_1RC1LA_0LA0RB = Cc (Pos.succ p).
Proof.
  intros p j E. unfold Cc_1RB1LA_1LC1RD_1RC1LA_0LA0RB.
  rewrite (pexp_succ_fill p (S j) E).
  unfold cden, V0_1RB1LA_1LC1RD_1RC1LA_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  first [ reflexivity
        | cbn [rep app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapf_1RB1LA_1LC1RD_1RC1LA_0LA0RB : forall p j, cview p = (S j, None) -> pexpi p = None ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j E Hxi. exists (0 * j + 1). split; [lia|].
  rewrite (gso_1RB1LA_1LC1RD_1RC1LA_0LA0RB p j E Hxi).
  rewrite (srun_sound tm true true chf_1RB1LA_1LC1RD_1RC1LA_0LA0RB B0_1RB1LA_1LC1RD_1RC1LA_0LA0RB V0_1RB1LA_1LC1RD_1RC1LA_0LA0RB 0 1
             run_fill_1RB1LA_1LC1RD_1RC1LA_0LA0RB [] [] j
             ltac:(reflexivity) ltac:(reflexivity)).
  f_equal. exact (geov_1RB1LA_1LC1RD_1RC1LA_0LA0RB p j E).
Qed.

Lemma lbl_1RB1LA_1LC1RD_1RC1LA_0LA0RB : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma gsv_1RB1LA_1LC1RD_1RC1LA_0LA0RB : forall p k, pexp p = Some (S k) ->
  Cc p = cden [] [] k V0_1RB1LA_1LC1RD_1RC1LA_0LA0RB.
Proof.
  intros p k Hx. unfold Cc_1RB1LA_1LC1RD_1RC1LA_0LA0RB. rewrite Hx.
  unfold cden, V0_1RB1LA_1LC1RD_1RC1LA_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia.
  first [ reflexivity
        | cbn [rep app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

(** The V lap lands EXACTLY on the second virtual anchor. *)
Lemma gew_1RB1LA_1LC1RD_1RC1LA_0LA0RB : forall p k, pexp p = Some (S k) ->
  cden [] [] k W0_1RB1LA_1LC1RD_1RC1LA_0LA0RB = Cc (Pos.succ p).
Proof.
  intros p k Hx. unfold Cc_1RB1LA_1LC1RD_1RC1LA_0LA0RB.
  rewrite (pexp_succ_virt p k Hx), (pexpi_succ_virt p k Hx).
  unfold cden, W0_1RB1LA_1LC1RD_1RC1LA_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia.
  first [ reflexivity
        | cbn [rep app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapv_1RB1LA_1LC1RD_1RC1LA_0LA0RB : forall p k, pexp p = Some (S k) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p k Hx. exists (0 * k + 1). split; [lia|].
  rewrite (gsv_1RB1LA_1LC1RD_1RC1LA_0LA0RB p k Hx).
  rewrite (srun_sound tm true true chv_1RB1LA_1LC1RD_1RC1LA_0LA0RB V0_1RB1LA_1LC1RD_1RC1LA_0LA0RB W0_1RB1LA_1LC1RD_1RC1LA_0LA0RB 0 1
             run_virt_1RB1LA_1LC1RD_1RC1LA_0LA0RB [] [] k ltac:(reflexivity) ltac:(reflexivity)).
  f_equal. exact (gew_1RB1LA_1LC1RD_1RC1LA_0LA0RB p k Hx).
Qed.

Lemma gsw_1RB1LA_1LC1RD_1RC1LA_0LA0RB : forall p k, pexpi p = Some (S k) ->
  Cc p = cden [] [] k WS_1RB1LA_1LC1RD_1RC1LA_0LA0RB.
Proof.
  intros p k Hxi.
  rewrite (pexpi_some p (S k) Hxi).
  unfold Cc_1RB1LA_1LC1RD_1RC1LA_0LA0RB. cbn [pexp pexpi]. rewrite (pexp_pow2 (S k)).
  unfold cden, WS_1RB1LA_1LC1RD_1RC1LA_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia.
  cbn [rep]. first [ rewrite <- ?app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

(** The landing: E(2^(S (S k)) + 2) = uD ++ uS ++ rep uD k ++ soD, up to
    trailing blanks. *)
Lemma gew2_1RB1LA_1LC1RD_1RC1LA_0LA0RB : forall p k, pexpi p = Some (S k) ->
  lift (cden [] [] k E2_1RB1LA_1LC1RD_1RC1LA_0LA0RB) = lift (Cc (Pos.succ p)).
Proof.
  intros p k Hxi.
  rewrite (pexpi_succ_shape p k Hxi).
  unfold Cc_1RB1LA_1LC1RD_1RC1LA_0LA0RB. cbn [pexp pexpi].
  assert (HD : cden [] [] k E2_1RB1LA_1LC1RD_1RC1LA_0LA0RB = (StD, ([S1;S0;S1;S1] ++ rep [S1;S0] k ++ [S1;S1], S0, []))).
  { unfold cden, E2_1RB1LA_1LC1RD_1RC1LA_0LA0RB, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * k + 0) with k by lia.
    first [ reflexivity
      | cbn [rep app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Ap_Alph_10_11_11 (xO (xI (pow2 k))) ++ [S0] = ([S1;S0;S1;S1] ++ rep [S1;S0] k ++ [S1;S1]) ++ [S0]).
  { simpl Ap_Alph_10_11_11. rewrite (apow_1RB1LA_1LC1RD_1RC1LA_0LA0RB (pow2 k) k (pexp_pow2 k)).
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_1RB1LA_1LC1RD_1RC1LA_0LA0RB. reflexivity.
Qed.

Lemma lapw_1RB1LA_1LC1RD_1RC1LA_0LA0RB : forall p k, pexpi p = Some (S k) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p k Hxi.
  exists (4 * k + 17), (cden [] [] k E2_1RB1LA_1LC1RD_1RC1LA_0LA0RB).
  split; [lia|]. split; [| exact (gew2_1RB1LA_1LC1RD_1RC1LA_0LA0RB p k Hxi)].
  rewrite (gsw_1RB1LA_1LC1RD_1RC1LA_0LA0RB p k Hxi).
  exact (srun_sound tm true true chw_1RB1LA_1LC1RD_1RC1LA_0LA0RB WS_1RB1LA_1LC1RD_1RC1LA_0LA0RB E2_1RB1LA_1LC1RD_1RC1LA_0LA0RB 4 17
           run_virt2_1RB1LA_1LC1RD_1RC1LA_0LA0RB [] [] k ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** ** The lap *)

Lemma lap_1RB1LA_1LC1RD_1RC1LA_0LA0RB : forall p, (10 <= p)%positive -> exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p Hp. destruct (cview p) as [j oq] eqn:E; destruct oq as [q0|].
  - destruct (pexp p) as [[|k]|] eqn:Epx.
    + rewrite (pexp_zero p Epx) in E. cbn in E. discriminate.
    + destruct (lapv_1RB1LA_1LC1RD_1RC1LA_0LA0RB p k Epx) as (n & Hn & Hrun).
      exists n, (Cc (Pos.succ p)).
      split; [exact Hrun | split; [reflexivity | exact Hn]].
    + destruct (pexpi p) as [[|m]|] eqn:Exi.
      * rewrite (pexpi_some p 0 Exi) in Hp.
        exfalso. apply Hp. vm_compute. reflexivity.
      * destruct (lapw_1RB1LA_1LC1RD_1RC1LA_0LA0RB p m Exi) as (n & c' & Hn & Hrun & Hl).
        exists n, c'. split; [exact Hrun | split; [exact Hl | exact Hn]].
      * destruct (lapi_1RB1LA_1LC1RD_1RC1LA_0LA0RB p j q0 E Epx Exi) as (n & Hn & Hrun).
        exists n, (Cc (Pos.succ p)).
        split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    destruct (pexpi p) as [[|m]|] eqn:Exi.
    + rewrite (pexpi_some p 0 Exi) in Hp.
      exfalso. apply Hp. vm_compute. reflexivity.
    + rewrite (pexpi_cview p m Exi) in E. discriminate.
    + destruct (lapf_1RB1LA_1LC1RD_1RC1LA_0LA0RB p j' E Exi) as (n & Hn & Hrun).
      exists n, (Cc (Pos.succ p)).
      split; [exact Hrun | split; [reflexivity | exact Hn]].
Qed.

(** ** SkipGlue's hypotheses *)

Lemma hint_1RB1LA_1LC1RD_1RC1LA_0LA0RB : forall p j q0, (10 <= p)%positive ->
  cview p = (j, Some q0) -> virt p = false ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 _ E Hv. unfold virt_1RB1LA_1LC1RD_1RC1LA_0LA0RB in Hv.
  destruct (pexp p) as [[|k]|] eqn:Epx.
  - rewrite (pexp_zero p Epx) in E. cbn in E. discriminate.
  - discriminate Hv.
  - destruct (pexpi p) as [m|] eqn:Exi; [discriminate Hv|].
    exact (lapi_1RB1LA_1LC1RD_1RC1LA_0LA0RB p j q0 E Epx Exi).
Qed.

Lemma hsucc_1RB1LA_1LC1RD_1RC1LA_0LA0RB : forall p j q0, cview p = (j, Some q0) ->
  virt p = false -> virt (Pos.succ p) = false.
Proof.
  intros p j q0 E Hv. unfold virt_1RB1LA_1LC1RD_1RC1LA_0LA0RB in *.
  rewrite (pexp_succ_int p j q0 E).
  destruct (pexp p) as [[|k]|] eqn:Epx.
  - rewrite (pexp_zero p Epx) in E. cbn in E. discriminate.
  - discriminate Hv.
  - rewrite (pexpi_succ_int p j q0 E Epx). reflexivity.
Qed.

Lemma hvlap_1RB1LA_1LC1RD_1RC1LA_0LA0RB : forall p, (10 <= p)%positive -> virt p = true ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p Hp Hv. unfold virt_1RB1LA_1LC1RD_1RC1LA_0LA0RB in Hv.
  destruct (pexp p) as [[|k]|] eqn:Epx.
  - destruct (pexpi p) as [m|] eqn:Exi; [| discriminate Hv].
    rewrite (pexp_zero p Epx) in Exi. cbn in Exi. discriminate.
  - destruct (lapv_1RB1LA_1LC1RD_1RC1LA_0LA0RB p k Epx) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hn | split; [exact Hrun | reflexivity]].
  - destruct (pexpi p) as [[|m]|] eqn:Exi; try discriminate Hv.
    + rewrite (pexpi_some p 0 Exi) in Hp.
      exfalso. apply Hp. vm_compute. reflexivity.
    + destruct (lapw_1RB1LA_1LC1RD_1RC1LA_0LA0RB p m Exi) as (n & c' & Hn & Hrun & Hl).
      exists n, c'. split; [exact Hn | split; [exact Hrun | exact Hl]].
Qed.

Lemma hvrun_1RB1LA_1LC1RD_1RC1LA_0LA0RB : forall p, (10 <= p)%positive -> virt p = true ->
  virt (Pos.succ p) = true -> virt (Pos.succ (Pos.succ p)) = false.
Proof.
  intros p Hp H1 H2. unfold virt_1RB1LA_1LC1RD_1RC1LA_0LA0RB in *.
  destruct (pexp p) as [[|k]|] eqn:E1.
  - destruct (pexpi p) as [m|] eqn:E2; [| discriminate H1].
    rewrite (pexp_zero p E1) in E2. cbn in E2. discriminate.
  - destruct (pexp_shape p k E1) as (r & -> & Hr).
    change (Pos.succ (Pos.succ (xO r))) with (xO (Pos.succ r)).
    destruct k as [|k'].
    + rewrite (pexp_zero r Hr) in Hp.
      exfalso. apply Hp. vm_compute. reflexivity.
    + destruct (pexp_shape r k' Hr) as (r2 & -> & _).
      change (Pos.succ (xO r2)) with (xI r2).
      cbn [pexp pexpi]. reflexivity.
  - destruct (pexpi p) as [[|m]|] eqn:E2; try discriminate H1.
    + rewrite (pexpi_some p 0 E2) in Hp.
      exfalso. apply Hp. vm_compute. reflexivity.
    + exfalso. rewrite (pexpi_succ_shape p m E2) in H2.
      cbn [pexp pexpi] in H2. discriminate.
Qed.

(** ** Bootstrap *)

Lemma boot_1RB1LA_1LC1RD_1RC1LA_0LA0RB : exists t0, stepn tm t0 InitES = Some (lift (Cc 10)).
Proof.
  exists 53.
  assert (H : match csteps tm 53 c0 with
              | Some c => ceqb c (Cc 10) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 53 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the overflow sweep (fill chain) or in the
    virtual laps behind it; [SkipGlue.vis_via_skip] carries the fill-anchor
    witnesses to every anchor at or above p0. *)

Lemma viso_1RB1LA_1LC1RD_1RC1LA_0LA0RB : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_1RB1LA_1LC1RD_1RC1LA_0LA0RB = Some q ->
  forall p j, cview p = (S j, None) -> pexpi p = None ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E Hxi.
  apply (vis_of_run tm Cc true true l B0_1RB1LA_1LC1RD_1RC1LA_0LA0RB p j [] []);
    [exact Hst | ltac:(intro; reflexivity) | reflexivity
     | exact (gso_1RB1LA_1LC1RD_1RC1LA_0LA0RB p j E Hxi)].
Qed.



Lemma vis_1RB1LA_1LC1RD_1RC1LA_0LA0RB : forall p q, (10 <= p)%positive ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q Hp.
  apply (vis_via_skip tm Cc virt 10 hint_1RB1LA_1LC1RD_1RC1LA_0LA0RB hsucc_1RB1LA_1LC1RD_1RC1LA_0LA0RB hvlap_1RB1LA_1LC1RD_1RC1LA_0LA0RB
           hvrun_1RB1LA_1LC1RD_1RC1LA_0LA0RB q); [| exact Hp].
  intros p1 j1 Hp1 E1.
  assert (Exi1 : pexpi p1 = None).
  { destruct (pexpi p1) as [[|m]|] eqn:Exi; [| | reflexivity].
    - rewrite (pexpi_some p1 0 Exi) in Hp1.
      exfalso. apply Hp1. vm_compute. reflexivity.
    - rewrite (pexpi_cview p1 m Exi) in E1. discriminate. }
  destruct q.
  - (* StA *)
    exact (viso_1RB1LA_1LC1RD_1RC1LA_0LA0RB [SRotL 1; SWin 1] StA
             ltac:(vm_compute; reflexivity) p1 j1 E1 Exi1).
  - (* StB *)
    exact (viso_1RB1LA_1LC1RD_1RC1LA_0LA0RB [SRotL 1; SWin 1; SCycL 2 0; SWin 3] StB
             ltac:(vm_compute; reflexivity) p1 j1 E1 Exi1).
  - (* StC *)
    exact (viso_1RB1LA_1LC1RD_1RC1LA_0LA0RB [SRotL 1; SWin 1; SCycL 2 0; SWin 4; SCycR 2; SWin 2] StC
             ltac:(vm_compute; reflexivity) p1 j1 E1 Exi1).
  - (* StD: the anchor state *)
    rewrite (gso_1RB1LA_1LC1RD_1RC1LA_0LA0RB p1 j1 E1 Exi1).
    exists 0. eexists. split; reflexivity.
Qed.

Theorem nqh_1RB1LA_1LC1RD_1RC1LA_0LA0RB : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 10). - exact boot_1RB1LA_1LC1RD_1RC1LA_0LA0RB. - intros p Hp. apply (lap_1RB1LA_1LC1RD_1RC1LA_0LA0RB p Hp). - intros p q Hp. apply (vis_1RB1LA_1LC1RD_1RC1LA_0LA0RB p q Hp). Qed.

Theorem nonhalt_1RB1LA_1LC1RD_1RC1LA_0LA0RB : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_1RB1LA_1LC1RD_1RC1LA_0LA0RB. Qed.
