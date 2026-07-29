(** * QMG_1RB1LC_0LC1RB_1RD1LA_0LC0RD: machine 1RB1LC_0LC1RB_1RD1LA_0LC0RD, boarded by CERTIFICATE (QUAD route).

    Auto-emitted by tools/counters/quad_emit.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  A linear-search-carry
    binary counter (WAVE26 section 7) under the Ap_Alph_00_10_1 alphabet: the interior
    lap makes Theta(j) micro excursions -- one round trip per digit -- so no
    single chain is the lap; each ROUND TRIP is a chain, and
    [Counters/QuadGlue.quad_lap] (MeasureGlue.mrun at abstract state
    (probe depth k, unprobed count m)) composes them into the quadratic lap.

      anchor    Cc p = (StD, (Ap_Alph_00_10_1 p ++ [S0;S0], S0, []))
      family    Cq W k m: k probed digits right of the head, m unprobed
                behind it, the deep word W OPAQUE
      hop       Cq W k (S m) -> Cq W (S k) m   (chains MC*, exact)
      terminal  Cq W k 0 -> the incremented word (chains TC*, exact)

    The interior lap composes boot + j hops + terminal; the OVERFLOW lap is
    the SAME composition with j+1 probes (the carry lands on the tail cell).
    Both close up to [lift], so the closer is
    [LapCertGlueLift.glue_neverqh_lift].

    Differentially validated against the raw simulator -- 18 laps, interior+overflow, exact marks and totals (j=2..10).
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter JpCounter
                                  Alph_00_10_1 LapCertGlue LapCertGlueLift
                                  MeasureGlue QuadGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_1RB1LC_0LC1RB_1RD1LA_0LC0RD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1LC_0LC1RB_1RD1LA_0LC0RD.

(** 1RB1LC_0LC1RB_1RD1LA_0LC0RD *)
Definition tm_1RB1LC_0LC1RB_1RD1LA_0LC0RD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StC
  | StB, S0 => mk S0 DL StC | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S0 DL StC | StD, S1 => mk S0 DR StD end.
Local Notation tm := tm_1RB1LC_0LC1RB_1RD1LA_0LC0RD.

Definition Cc_1RB1LC_0LC1RB_1RD1LA_0LC0RD (p : positive) : cconf := (StD, (Ap_Alph_00_10_1 p ++ [S0;S0], S0, [])).
Local Notation Cc := Cc_1RB1LC_0LC1RB_1RD1LA_0LC0RD.

(** The two-index probe family (WAVE26 7d): k probed digits, m unprobed,
    deep word W opaque. *)
Definition Cq_1RB1LC_0LC1RB_1RD1LA_0LC0RD (W : list Sym) (k m : nat) : cconf :=
  match m with
  | O => (StC, (W, S0, rep [S1;S1] k ++ [S0]))
  | S m' => (StC, (rep [S0;S1] m' ++ [S0;S0] ++ W, S1, rep [S1;S1] k ++ [S0]))
  end.
Local Notation Cq := Cq_1RB1LC_0LC1RB_1RD1LA_0LC0RD.

(** ** The certificate: nine chains, all run by the kernel *)

Definition c_MC1p0_1RB1LC_0LC1RB_1RD1LA_0LC0RD : sconf := mkC StC (mkS [S0;S1] [] 0 0 []) S1 (mkS [S1;S1] [S1;S1] 1 0 [S0]).
Definition c_MC1p1_1RB1LC_0LC1RB_1RD1LA_0LC0RD : sconf := mkC StC (mkS [] [] 0 0 []) S1 (mkS [S1;S1] [S1;S1] 1 1 [S0]).
Definition ch_MC1p_1RB1LC_0LC1RB_1RD1LA_0LC0RD : list lstep := [SWin 4; SCycR 2; SWin 2; SCycL 2 0; SWin 4; SFoldR 1].

Lemma run_MC1p_1RB1LC_0LC1RB_1RD1LA_0LC0RD : srun tm false true ch_MC1p_1RB1LC_0LC1RB_1RD1LA_0LC0RD c_MC1p0_1RB1LC_0LC1RB_1RD1LA_0LC0RD = Some (c_MC1p1_1RB1LC_0LC1RB_1RD1LA_0LC0RD, 4, 10).
Proof. vm_compute. reflexivity. Qed.

Definition c_MC0p0_1RB1LC_0LC1RB_1RD1LA_0LC0RD : sconf := mkC StC (mkS [S0;S0] [] 0 0 []) S1 (mkS [S1;S1] [S1;S1] 1 0 [S0]).
Definition c_MC0p1_1RB1LC_0LC1RB_1RD1LA_0LC0RD : sconf := mkC StC (mkS [] [] 0 0 []) S0 (mkS [S1;S1] [S1;S1] 1 1 [S0]).
Definition ch_MC0p_1RB1LC_0LC1RB_1RD1LA_0LC0RD : list lstep := [SWin 4; SCycR 2; SWin 2; SCycL 2 0; SWin 4; SFoldR 1].

Lemma run_MC0p_1RB1LC_0LC1RB_1RD1LA_0LC0RD : srun tm false true ch_MC0p_1RB1LC_0LC1RB_1RD1LA_0LC0RD c_MC0p0_1RB1LC_0LC1RB_1RD1LA_0LC0RD = Some (c_MC0p1_1RB1LC_0LC1RB_1RD1LA_0LC0RD, 4, 10).
Proof. vm_compute. reflexivity. Qed.

Definition c_MC1z0_1RB1LC_0LC1RB_1RD1LA_0LC0RD : sconf := mkC StC (mkS [S0;S1] [] 0 0 []) S1 (mkS [S0] [] 0 0 []).
Definition c_MC1z1_1RB1LC_0LC1RB_1RD1LA_0LC0RD : sconf := mkC StC (mkS [] [] 0 0 []) S1 (mkS [S1;S1;S0] [] 0 0 []).
Definition ch_MC1z_1RB1LC_0LC1RB_1RD1LA_0LC0RD : list lstep := [SWin 6].

Lemma run_MC1z_1RB1LC_0LC1RB_1RD1LA_0LC0RD : srun tm false true ch_MC1z_1RB1LC_0LC1RB_1RD1LA_0LC0RD c_MC1z0_1RB1LC_0LC1RB_1RD1LA_0LC0RD = Some (c_MC1z1_1RB1LC_0LC1RB_1RD1LA_0LC0RD, 0, 6).
Proof. vm_compute. reflexivity. Qed.

Definition c_MC0z0_1RB1LC_0LC1RB_1RD1LA_0LC0RD : sconf := mkC StC (mkS [S0;S0] [] 0 0 []) S1 (mkS [S0] [] 0 0 []).
Definition c_MC0z1_1RB1LC_0LC1RB_1RD1LA_0LC0RD : sconf := mkC StC (mkS [] [] 0 0 []) S0 (mkS [S1;S1;S0] [] 0 0 []).
Definition ch_MC0z_1RB1LC_0LC1RB_1RD1LA_0LC0RD : list lstep := [SWin 6].

Lemma run_MC0z_1RB1LC_0LC1RB_1RD1LA_0LC0RD : srun tm false true ch_MC0z_1RB1LC_0LC1RB_1RD1LA_0LC0RD c_MC0z0_1RB1LC_0LC1RB_1RD1LA_0LC0RD = Some (c_MC0z1_1RB1LC_0LC1RB_1RD1LA_0LC0RD, 0, 6).
Proof. vm_compute. reflexivity. Qed.

Definition c_TCp0_1RB1LC_0LC1RB_1RD1LA_0LC0RD : sconf := mkC StC (mkS [] [] 0 0 []) S0 (mkS [S1;S1] [S1;S1] 1 0 [S0]).
Definition c_TCp1_1RB1LC_0LC1RB_1RD1LA_0LC0RD : sconf := mkC StD (mkS [] [S0;S0] 1 1 [S1]) S0 (mkS [] [] 0 0 []).
Definition ch_TCp_1RB1LC_0LC1RB_1RD1LA_0LC0RD : list lstep := [SWin 2; SCycR 2; SWin 1; SRotL 1; SFoldL 1].

Lemma run_TCp_1RB1LC_0LC1RB_1RD1LA_0LC0RD : srun tm false true ch_TCp_1RB1LC_0LC1RB_1RD1LA_0LC0RD c_TCp0_1RB1LC_0LC1RB_1RD1LA_0LC0RD = Some (c_TCp1_1RB1LC_0LC1RB_1RD1LA_0LC0RD, 2, 3).
Proof. vm_compute. reflexivity. Qed.

Definition c_TCz0_1RB1LC_0LC1RB_1RD1LA_0LC0RD : sconf := mkC StC (mkS [] [] 0 0 []) S0 (mkS [S0] [] 0 0 []).
Definition c_TCz1_1RB1LC_0LC1RB_1RD1LA_0LC0RD : sconf := mkC StD (mkS [S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition ch_TCz_1RB1LC_0LC1RB_1RD1LA_0LC0RD : list lstep := [SWin 1].

Lemma run_TCz_1RB1LC_0LC1RB_1RD1LA_0LC0RD : srun tm false true ch_TCz_1RB1LC_0LC1RB_1RD1LA_0LC0RD c_TCz0_1RB1LC_0LC1RB_1RD1LA_0LC0RD = Some (c_TCz1_1RB1LC_0LC1RB_1RD1LA_0LC0RD, 0, 1).
Proof. vm_compute. reflexivity. Qed.

Definition c_BOOT10_1RB1LC_0LC1RB_1RD1LA_0LC0RD : sconf := mkC StD (mkS [S1;S0] [S1;S0] 1 0 [S0]) S0 (mkS [] [] 0 0 []).
Definition c_BOOT11_1RB1LC_0LC1RB_1RD1LA_0LC0RD : sconf := mkC StC (mkS [] [S0;S1] 1 0 [S0;S0]) S1 (mkS [S0] [] 0 0 []).
Definition ch_BOOT1_1RB1LC_0LC1RB_1RD1LA_0LC0RD : list lstep := [SWin 1; SUnrotL 1].

Lemma run_BOOT1_1RB1LC_0LC1RB_1RD1LA_0LC0RD : srun tm false true ch_BOOT1_1RB1LC_0LC1RB_1RD1LA_0LC0RD c_BOOT10_1RB1LC_0LC1RB_1RD1LA_0LC0RD = Some (c_BOOT11_1RB1LC_0LC1RB_1RD1LA_0LC0RD, 0, 1).
Proof. vm_compute. reflexivity. Qed.

Definition c_BOOT00_1RB1LC_0LC1RB_1RD1LA_0LC0RD : sconf := mkC StD (mkS [S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition c_BOOT01_1RB1LC_0LC1RB_1RD1LA_0LC0RD : sconf := mkC StC (mkS [] [] 0 0 []) S0 (mkS [S0] [] 0 0 []).
Definition ch_BOOT0_1RB1LC_0LC1RB_1RD1LA_0LC0RD : list lstep := [SWin 1].

Lemma run_BOOT0_1RB1LC_0LC1RB_1RD1LA_0LC0RD : srun tm false true ch_BOOT0_1RB1LC_0LC1RB_1RD1LA_0LC0RD c_BOOT00_1RB1LC_0LC1RB_1RD1LA_0LC0RD = Some (c_BOOT01_1RB1LC_0LC1RB_1RD1LA_0LC0RD, 0, 1).
Proof. vm_compute. reflexivity. Qed.

Definition c_BOOTO0_1RB1LC_0LC1RB_1RD1LA_0LC0RD : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S0;S0]) S0 (mkS [] [] 0 0 []).
Definition c_BOOTO1_1RB1LC_0LC1RB_1RD1LA_0LC0RD : sconf := mkC StC (mkS [] [S0;S1] 1 0 [S0;S0]) S1 (mkS [S0] [] 0 0 []).
Definition ch_BOOTO_1RB1LC_0LC1RB_1RD1LA_0LC0RD : list lstep := [SRotL 1; SWin 1].

Lemma run_BOOTO_1RB1LC_0LC1RB_1RD1LA_0LC0RD : srun tm false true ch_BOOTO_1RB1LC_0LC1RB_1RD1LA_0LC0RD c_BOOTO0_1RB1LC_0LC1RB_1RD1LA_0LC0RD = Some (c_BOOTO1_1RB1LC_0LC1RB_1RD1LA_0LC0RD, 0, 1).
Proof. vm_compute. reflexivity. Qed.

(** ** The micro hop *)

Lemma hop_1RB1LC_0LC1RB_1RD1LA_0LC0RD : forall W k m, exists n,
  csteps tm n (Cq W k (S m)) = Some (Cq W (S k) m) /\ 0 < n.
Proof.
  intros W k m.
  destruct m as [|m']; destruct k as [|k'].
  - (* k = 0, landing on the stop cell *)
    exists (0 * 0 + 6). split; [|lia].
    change (Cq W 0 1) with (cden W [] 0 c_MC0z0_1RB1LC_0LC1RB_1RD1LA_0LC0RD).
    rewrite (srun_sound tm false true ch_MC0z_1RB1LC_0LC1RB_1RD1LA_0LC0RD c_MC0z0_1RB1LC_0LC1RB_1RD1LA_0LC0RD c_MC0z1_1RB1LC_0LC1RB_1RD1LA_0LC0RD
               0 6 run_MC0z_1RB1LC_0LC1RB_1RD1LA_0LC0RD W [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    reflexivity.
  - (* k = S k', landing on the stop cell *)
    exists (4 * k' + 10). split; [|lia].
    assert (HS : Cq W (S k') 1 = cden W [] k' c_MC0p0_1RB1LC_0LC1RB_1RD1LA_0LC0RD).
    { unfold Cq_1RB1LC_0LC1RB_1RD1LA_0LC0RD, cden, c_MC0p0_1RB1LC_0LC1RB_1RD1LA_0LC0RD, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      replace (1 * k' + 0) with k' by lia.
      cbn [rep app]. rewrite <- ?app_assoc. reflexivity. }
    rewrite HS.
    rewrite (srun_sound tm false true ch_MC0p_1RB1LC_0LC1RB_1RD1LA_0LC0RD c_MC0p0_1RB1LC_0LC1RB_1RD1LA_0LC0RD c_MC0p1_1RB1LC_0LC1RB_1RD1LA_0LC0RD
               4 10 run_MC0p_1RB1LC_0LC1RB_1RD1LA_0LC0RD W [] k'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal; first
      [ reflexivity
      | unfold cden, c_MC0p1_1RB1LC_0LC1RB_1RD1LA_0LC0RD, Cq_1RB1LC_0LC1RB_1RD1LA_0LC0RD, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post];
        replace (1 * k' + 1) with (S k') by lia;
        cbn [rep app]; rewrite <- ?app_assoc; reflexivity ].
  - (* k = 0, landing on a digit *)
    exists (0 * 0 + 6). split; [|lia].
    change (Cq W 0 (S (S m')))
      with (cden (rep [S0;S1] m' ++ [S0;S0] ++ W) [] 0 c_MC1z0_1RB1LC_0LC1RB_1RD1LA_0LC0RD).
    rewrite (srun_sound tm false true ch_MC1z_1RB1LC_0LC1RB_1RD1LA_0LC0RD c_MC1z0_1RB1LC_0LC1RB_1RD1LA_0LC0RD c_MC1z1_1RB1LC_0LC1RB_1RD1LA_0LC0RD
               0 6 run_MC1z_1RB1LC_0LC1RB_1RD1LA_0LC0RD (rep [S0;S1] m' ++ [S0;S0] ++ W) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    reflexivity.
  - (* k = S k', landing on a digit *)
    exists (4 * k' + 10). split; [|lia].
    assert (HS : Cq W (S k') (S (S m'))
                 = cden (rep [S0;S1] m' ++ [S0;S0] ++ W) [] k' c_MC1p0_1RB1LC_0LC1RB_1RD1LA_0LC0RD).
    { unfold Cq_1RB1LC_0LC1RB_1RD1LA_0LC0RD, cden, c_MC1p0_1RB1LC_0LC1RB_1RD1LA_0LC0RD, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      replace (1 * k' + 0) with k' by lia.
      cbn [rep app]. rewrite <- ?app_assoc. reflexivity. }
    rewrite HS.
    rewrite (srun_sound tm false true ch_MC1p_1RB1LC_0LC1RB_1RD1LA_0LC0RD c_MC1p0_1RB1LC_0LC1RB_1RD1LA_0LC0RD c_MC1p1_1RB1LC_0LC1RB_1RD1LA_0LC0RD
               4 10 run_MC1p_1RB1LC_0LC1RB_1RD1LA_0LC0RD (rep [S0;S1] m' ++ [S0;S0] ++ W) [] k'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal; first
      [ reflexivity
      | unfold cden, c_MC1p1_1RB1LC_0LC1RB_1RD1LA_0LC0RD, Cq_1RB1LC_0LC1RB_1RD1LA_0LC0RD, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post];
        replace (1 * k' + 1) with (S k') by lia;
        cbn [rep app]; rewrite <- ?app_assoc; reflexivity ].
Qed.

(** ** The terminal: the carry write and the clearing sweep.  Its chain
    count is the FINAL probe depth k -- the anchor's carry index. *)

Lemma term_1RB1LC_0LC1RB_1RD1LA_0LC0RD : forall W k, exists n c',
  csteps tm n (Cq W k 0) = Some c'
  /\ c' = (StD, (rep [S0;S0] k ++ [S1] ++ W, S0, [])) /\ 0 < n.
Proof.
  intros W k. destruct k as [|k'].
  - exists (0 * 0 + 1). eexists. split; [|split; [reflexivity | lia]].
    change (Cq W 0 0) with (cden W [] 0 c_TCz0_1RB1LC_0LC1RB_1RD1LA_0LC0RD).
    rewrite (srun_sound tm false true ch_TCz_1RB1LC_0LC1RB_1RD1LA_0LC0RD c_TCz0_1RB1LC_0LC1RB_1RD1LA_0LC0RD c_TCz1_1RB1LC_0LC1RB_1RD1LA_0LC0RD
               0 1 run_TCz_1RB1LC_0LC1RB_1RD1LA_0LC0RD W [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal; first
      [ reflexivity
      | unfold cden, c_TCz1_1RB1LC_0LC1RB_1RD1LA_0LC0RD, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post];
        cbn [rep app]; rewrite ?app_nil_r, <- ?app_assoc; reflexivity ].
  - exists (2 * k' + 3). eexists.
    split; [|split; [reflexivity | lia]].
    assert (HS : Cq W (S k') 0 = cden W [] k' c_TCp0_1RB1LC_0LC1RB_1RD1LA_0LC0RD).
    { unfold Cq_1RB1LC_0LC1RB_1RD1LA_0LC0RD, cden, c_TCp0_1RB1LC_0LC1RB_1RD1LA_0LC0RD, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      replace (1 * k' + 0) with k' by lia.
      cbn [rep app]. rewrite <- ?app_assoc. reflexivity. }
    rewrite HS.
    rewrite (srun_sound tm false true ch_TCp_1RB1LC_0LC1RB_1RD1LA_0LC0RD c_TCp0_1RB1LC_0LC1RB_1RD1LA_0LC0RD c_TCp1_1RB1LC_0LC1RB_1RD1LA_0LC0RD
               2 3 run_TCp_1RB1LC_0LC1RB_1RD1LA_0LC0RD W [] k'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal; first
      [ reflexivity
      | unfold cden, c_TCp1_1RB1LC_0LC1RB_1RD1LA_0LC0RD, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post];
        replace (1 * k' + 1) with (S k') by lia;
        cbn [rep app]; rewrite ?app_nil_r, <- ?app_assoc; reflexivity ].
Qed.

(** ** The composed lap: boot + Theta(j) hops + terminal *)

Lemma qrun_1RB1LC_0LC1RB_1RD1LA_0LC0RD : forall W j, exists n c',
  csteps tm n (Cq W 0 j) = Some c'
  /\ lift c' = lift ((StD, (rep [S0;S0] j ++ [S1] ++ W, S0, [])) : cconf)
  /\ 0 < n.
Proof.
  intros W j.
  apply (quad_lap tm j (Cq_1RB1LC_0LC1RB_1RD1LA_0LC0RD W)).
  - intros k m _. exact (hop_1RB1LC_0LC1RB_1RD1LA_0LC0RD W k m).
  - intros k Hk. rewrite Nat.add_0_r in Hk. subst k.
    destruct (term_1RB1LC_0LC1RB_1RD1LA_0LC0RD W j) as (n & c' & Hrun & -> & Hn).
    exists n. eexists. split; [exact Hrun | split; [reflexivity | exact Hn]].
Qed.

(** ** The interior lap *)

Lemma lapi_1RB1LC_0LC1RB_1RD1LA_0LC0RD : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  destruct (Alph_00_10_1.cview_some_Alph_00_10_1 p j q0 E) as (H1 & H2).
  destruct j as [|j''].
  - (* j = 0: the boot lands directly on the stop cell *)
    destruct (qrun_1RB1LC_0LC1RB_1RD1LA_0LC0RD ([S0] ++ Ap_Alph_00_10_1 q0 ++ [S0;S0]) 0) as (n & c' & Hrun & Hl & Hn).
    exists ((0 * 0 + 1) + n), c'. split; [lia|]. split.
    { rewrite csteps_add.
      assert (HB : Cc p = cden ([S0] ++ Ap_Alph_00_10_1 q0 ++ [S0;S0]) [] 0 c_BOOT00_1RB1LC_0LC1RB_1RD1LA_0LC0RD).
      { unfold Cc_1RB1LC_0LC1RB_1RD1LA_0LC0RD, cden, c_BOOT00_1RB1LC_0LC1RB_1RD1LA_0LC0RD, sden;
          cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
        rewrite H1. cbn [rep app]. rewrite <- ?app_assoc. reflexivity. }
      rewrite HB.
      rewrite (srun_sound tm false true ch_BOOT0_1RB1LC_0LC1RB_1RD1LA_0LC0RD c_BOOT00_1RB1LC_0LC1RB_1RD1LA_0LC0RD
                 c_BOOT01_1RB1LC_0LC1RB_1RD1LA_0LC0RD 0 1 run_BOOT0_1RB1LC_0LC1RB_1RD1LA_0LC0RD
                 ([S0] ++ Ap_Alph_00_10_1 q0 ++ [S0;S0]) [] 0 ltac:(discriminate) ltac:(reflexivity)).
      assert (HQ : cden ([S0] ++ Ap_Alph_00_10_1 q0 ++ [S0;S0]) [] 0 c_BOOT01_1RB1LC_0LC1RB_1RD1LA_0LC0RD
                   = Cq ([S0] ++ Ap_Alph_00_10_1 q0 ++ [S0;S0]) 0 0).
      { unfold cden, c_BOOT01_1RB1LC_0LC1RB_1RD1LA_0LC0RD, Cq_1RB1LC_0LC1RB_1RD1LA_0LC0RD, sden;
          cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
        cbn [rep app]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity. }
      rewrite HQ. exact Hrun. }
    { rewrite Hl. unfold Cc_1RB1LC_0LC1RB_1RD1LA_0LC0RD. rewrite H2. cbn [rep app].
      first [ reflexivity
            | rewrite <- ?app_assoc; cbn [app]; reflexivity ]. }
  - (* j = S j'': the boot lands on the first digit *)
    destruct (qrun_1RB1LC_0LC1RB_1RD1LA_0LC0RD ([S0] ++ Ap_Alph_00_10_1 q0 ++ [S0;S0]) (S j''))
      as (n & c' & Hrun & Hl & Hn).
    exists ((0 * j'' + 1) + n), c'. split; [lia|]. split.
    { rewrite csteps_add.
      assert (HB : Cc p = cden ([S0] ++ Ap_Alph_00_10_1 q0 ++ [S0;S0]) [] j'' c_BOOT10_1RB1LC_0LC1RB_1RD1LA_0LC0RD).
      { unfold Cc_1RB1LC_0LC1RB_1RD1LA_0LC0RD, cden, c_BOOT10_1RB1LC_0LC1RB_1RD1LA_0LC0RD, sden;
          cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
        replace (1 * j'' + 0) with j'' by lia.
        rewrite H1. cbn [rep app]. rewrite <- ?app_assoc. reflexivity. }
      rewrite HB.
      rewrite (srun_sound tm false true ch_BOOT1_1RB1LC_0LC1RB_1RD1LA_0LC0RD c_BOOT10_1RB1LC_0LC1RB_1RD1LA_0LC0RD
                 c_BOOT11_1RB1LC_0LC1RB_1RD1LA_0LC0RD 0 1 run_BOOT1_1RB1LC_0LC1RB_1RD1LA_0LC0RD
                 ([S0] ++ Ap_Alph_00_10_1 q0 ++ [S0;S0]) [] j''
                 ltac:(discriminate) ltac:(reflexivity)).
      assert (HQ : cden ([S0] ++ Ap_Alph_00_10_1 q0 ++ [S0;S0]) [] j'' c_BOOT11_1RB1LC_0LC1RB_1RD1LA_0LC0RD
                   = Cq ([S0] ++ Ap_Alph_00_10_1 q0 ++ [S0;S0]) 0 (S j'')).
      { unfold cden, c_BOOT11_1RB1LC_0LC1RB_1RD1LA_0LC0RD, Cq_1RB1LC_0LC1RB_1RD1LA_0LC0RD, sden;
          cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
        replace (1 * j'' + 0) with j'' by lia.
        cbn [rep app]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity. }
      rewrite HQ. exact Hrun. }
    { rewrite Hl. unfold Cc_1RB1LC_0LC1RB_1RD1LA_0LC0RD. rewrite H2. cbn [rep app].
      first [ reflexivity
            | rewrite <- ?app_assoc; cbn [app]; reflexivity ]. }
Qed.

(** ** The overflow lap: the same ladder, one probe deeper *)

Lemma gso_1RB1LC_0LC1RB_1RD1LA_0LC0RD : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j c_BOOTO0_1RB1LC_0LC1RB_1RD1LA_0LC0RD.
Proof.
  intros p j E. destruct (Alph_00_10_1.cview_none_Alph_00_10_1 p j E) as (H1 & _).
  unfold Cc_1RB1LC_0LC1RB_1RD1LA_0LC0RD, cden, c_BOOTO0_1RB1LC_0LC1RB_1RD1LA_0LC0RD, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1; cbn [rep app].
  first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB1LC_0LC1RB_1RD1LA_0LC0RD : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma lapo_1RB1LC_0LC1RB_1RD1LA_0LC0RD : forall p j, cview p = (S j, None) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j E.
  destruct (Alph_00_10_1.cview_none_Alph_00_10_1 p j E) as (_ & H2).
  destruct (qrun_1RB1LC_0LC1RB_1RD1LA_0LC0RD [] (S j)) as (n & c' & Hrun & Hl & Hn).
  exists ((0 * j + 1) + n), c'. split; [lia|]. split.
  { rewrite csteps_add.
    rewrite (gso_1RB1LC_0LC1RB_1RD1LA_0LC0RD p j E).
    rewrite (srun_sound tm false true ch_BOOTO_1RB1LC_0LC1RB_1RD1LA_0LC0RD c_BOOTO0_1RB1LC_0LC1RB_1RD1LA_0LC0RD
               c_BOOTO1_1RB1LC_0LC1RB_1RD1LA_0LC0RD 0 1 run_BOOTO_1RB1LC_0LC1RB_1RD1LA_0LC0RD [] [] j
               ltac:(discriminate) ltac:(reflexivity)).
    assert (HQ : cden [] [] j c_BOOTO1_1RB1LC_0LC1RB_1RD1LA_0LC0RD = Cq [] 0 (S j)).
    { unfold cden, c_BOOTO1_1RB1LC_0LC1RB_1RD1LA_0LC0RD, Cq_1RB1LC_0LC1RB_1RD1LA_0LC0RD, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      replace (1 * j + 0) with j by lia.
      cbn [rep app]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity. }
    rewrite HQ. exact Hrun. }
  { rewrite Hl. unfold Cc_1RB1LC_0LC1RB_1RD1LA_0LC0RD.
    assert (HG : Ap_Alph_00_10_1 (Pos.succ p) ++ [S0;S0] = ((rep [S0;S0] (S j) ++ [S1]) ++ [S0]) ++ [S0]).
    { rewrite H2.
      first [ rewrite <- !app_assoc; reflexivity
            | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
    rewrite HG. rewrite !lbl_1RB1LC_0LC1RB_1RD1LA_0LC0RD. reflexivity. }
Qed.

(** ** The full lap *)

Lemma lap_1RB1LC_0LC1RB_1RD1LA_0LC0RD : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E; destruct oq as [q0|].
  - destruct (lapi_1RB1LC_0LC1RB_1RD1LA_0LC0RD p j q0 E) as (n & c' & Hn & Hrun & Hl).
    exists n, c'. split; [exact Hrun | split; [exact Hl | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    destruct (lapo_1RB1LC_0LC1RB_1RD1LA_0LC0RD p j' E) as (n & c' & Hn & Hrun & Hl).
    exists n, c'. split; [exact Hrun | split; [exact Hl | exact Hn]].
Qed.

(** ** Bootstrap *)

Lemma boot_1RB1LC_0LC1RB_1RD1LA_0LC0RD : exists t0, stepn tm t0 InitES = Some (lift (Cc 2)).
Proof.
  exists 11.
  assert (H : match csteps tm 11 c0 with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 11 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits: every state fires inside the overflow ladder *)

Lemma viso_1RB1LC_0LC1RB_1RD1LA_0LC0RD : forall (l : list lstep) (q : St),
  srun_st tm false true l c_BOOTO0_1RB1LC_0LC1RB_1RD1LA_0LC0RD = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc false true l c_BOOTO0_1RB1LC_0LC1RB_1RD1LA_0LC0RD p j [] []);
    [exact Hst | ltac:(intro; discriminate) | reflexivity
     | exact (gso_1RB1LC_0LC1RB_1RD1LA_0LC0RD p j E)].
Qed.

Lemma vis_1RB1LC_0LC1RB_1RD1LA_0LC0RD : forall p q,
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros p q.
  apply (vis_via_ovf_lift tm Cc lapi_1RB1LC_0LC1RB_1RD1LA_0LC0RD q).
  intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
  destruct q.
  - (* StA *)
    exact (viso_1RB1LC_0LC1RB_1RD1LA_0LC0RD [SRotL 1; SWin 1; SRotL 1; SWin 1] StA
             ltac:(vm_compute; reflexivity) p1 j1 E1).
  - (* StB *)
    exact (viso_1RB1LC_0LC1RB_1RD1LA_0LC0RD [SRotL 1; SWin 1; SRotL 1; SWin 2] StB
             ltac:(vm_compute; reflexivity) p1 j1 E1).
  - (* StC *)
    exact (viso_1RB1LC_0LC1RB_1RD1LA_0LC0RD [SRotL 1; SWin 1] StC
             ltac:(vm_compute; reflexivity) p1 j1 E1).
  - (* StD: the anchor state *)
    rewrite (gso_1RB1LC_0LC1RB_1RD1LA_0LC0RD p1 j1 E1).
    exists 0. eexists. split; reflexivity.
Qed.

Theorem nqh_1RB1LC_0LC1RB_1RD1LA_0LC0RD : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh_lift tm Cc 2). - exact boot_1RB1LC_0LC1RB_1RD1LA_0LC0RD. - intros p _. apply lap_1RB1LC_0LC1RB_1RD1LA_0LC0RD. - intros p q _. apply vis_1RB1LC_0LC1RB_1RD1LA_0LC0RD. Qed.

Theorem nonhalt_1RB1LC_0LC1RB_1RD1LA_0LC0RD : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_1RB1LC_0LC1RB_1RD1LA_0LC0RD. Qed.
