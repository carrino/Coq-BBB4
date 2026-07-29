(** * QMG_1RB1RA_1LC0LD_0RA0LC_0RA1LD: machine 1RB1RA_1LC0LD_0RA0LC_0RA1LD, boarded by CERTIFICATE (QUAD route).

    Auto-emitted by tools/counters/quad_emit.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  A linear-search-carry
    binary counter (WAVE26 section 7) under the Kp alphabet: the interior
    lap makes Theta(j) micro excursions -- one round trip per digit -- so no
    single chain is the lap; each ROUND TRIP is a chain, and
    [Counters/QuadGlue.quad_lap] (MeasureGlue.mrun at abstract state
    (probe depth k, unprobed count m)) composes them into the quadratic lap.

      anchor    Cc p = (StA, (Kp p ++ [S0], S0, []))
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
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape LapGlue MonoCounter JpCounter
                                  KpCounter LapCertGlue LapCertGlueLift
                                  MeasureGlue QuadGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_1RB1RA_1LC0LD_0RA0LC_0RA1LD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1RA_1LC0LD_0RA0LC_0RA1LD.

(** 1RB1RA_1LC0LD_0RA0LC_0RA1LD *)
(** 1RB1RA_1LC0LD_0RA0LC_0RA1LD -- the real machine (its counter grows RIGHT). *)
Definition tm_1RB1RA_1LC0LD_0RA0LC_0RA1LD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DR StA
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DL StD
  | StC, S0 => mk S0 DR StA | StC, S1 => mk S0 DL StC
  | StD, S0 => mk S0 DR StA | StD, S1 => mk S1 DL StD end.

(** Its mirror 1LB1LA_1RC0RD_0LA0RC_0LA1RD: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_1RB1RA_1LC0LD_0RA0LC_0RA1LD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => mk S1 DL StA
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S0 DR StD
  | StC, S0 => mk S0 DL StA | StC, S1 => mk S0 DR StC
  | StD, S0 => mk S0 DL StA | StD, S1 => mk S1 DR StD end.
Local Notation tm := tmm_1RB1RA_1LC0LD_0RA0LC_0RA1LD.

Lemma mirror_ok_1RB1RA_1LC0LD_0RA0LC_0RA1LD : mirror_tm tm_1RB1RA_1LC0LD_0RA0LC_0RA1LD = tmm_1RB1RA_1LC0LD_0RA0LC_0RA1LD.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_1RB1RA_1LC0LD_0RA0LC_0RA1LD (p : positive) : cconf := (StA, (Kp p ++ [S0], S0, [])).
Local Notation Cc := Cc_1RB1RA_1LC0LD_0RA0LC_0RA1LD.

(** The two-index probe family (WAVE26 7d): k probed digits, m unprobed,
    deep word W opaque. *)
Definition Cq_1RB1RA_1LC0LD_0RA0LC_0RA1LD (W : list Sym) (k m : nat) : cconf :=
  match m with
  | O => (StB, (W, S0, match k with O => [S1] | S k' => rep [S1] (S k') ++ [S1;S0] end))
  | S m' => (StB, (rep [S1] m' ++ [S0] ++ W, S1, match k with O => [S1] | S k' => rep [S1] (S k') ++ [S1;S0] end))
  end.
Local Notation Cq := Cq_1RB1RA_1LC0LD_0RA0LC_0RA1LD.

(** ** The certificate: nine chains, all run by the kernel *)

Definition c_MC1p0_1RB1RA_1LC0LD_0RA0LC_0RA1LD : sconf := mkC StB (mkS [S1] [] 0 0 []) S1 (mkS [S1] [S1] 1 0 [S1;S0]).
Definition c_MC1p1_1RB1RA_1LC0LD_0RA0LC_0RA1LD : sconf := mkC StB (mkS [] [] 0 0 []) S1 (mkS [S1] [S1] 1 1 [S1;S0]).
Definition ch_MC1p_1RB1RA_1LC0LD_0RA0LC_0RA1LD : list lstep := [SWin 1; SCycR 1; SWin 4; SCycL 1 0; SWin 2; SFoldR 1].

Lemma run_MC1p_1RB1RA_1LC0LD_0RA0LC_0RA1LD : srun tm false true ch_MC1p_1RB1RA_1LC0LD_0RA0LC_0RA1LD c_MC1p0_1RB1RA_1LC0LD_0RA0LC_0RA1LD = Some (c_MC1p1_1RB1RA_1LC0LD_0RA0LC_0RA1LD, 2, 7).
Proof. vm_compute. reflexivity. Qed.

Definition c_MC0p0_1RB1RA_1LC0LD_0RA0LC_0RA1LD : sconf := mkC StB (mkS [S0] [] 0 0 []) S1 (mkS [S1] [S1] 1 0 [S1;S0]).
Definition c_MC0p1_1RB1RA_1LC0LD_0RA0LC_0RA1LD : sconf := mkC StB (mkS [] [] 0 0 []) S0 (mkS [S1] [S1] 1 1 [S1;S0]).
Definition ch_MC0p_1RB1RA_1LC0LD_0RA0LC_0RA1LD : list lstep := [SWin 1; SCycR 1; SWin 4; SCycL 1 0; SWin 2; SFoldR 1].

Lemma run_MC0p_1RB1RA_1LC0LD_0RA0LC_0RA1LD : srun tm false true ch_MC0p_1RB1RA_1LC0LD_0RA0LC_0RA1LD c_MC0p0_1RB1RA_1LC0LD_0RA0LC_0RA1LD = Some (c_MC0p1_1RB1RA_1LC0LD_0RA0LC_0RA1LD, 2, 7).
Proof. vm_compute. reflexivity. Qed.

Definition c_MC1z0_1RB1RA_1LC0LD_0RA0LC_0RA1LD : sconf := mkC StB (mkS [S1] [] 0 0 []) S1 (mkS [S1] [] 0 0 []).
Definition c_MC1z1_1RB1RA_1LC0LD_0RA0LC_0RA1LD : sconf := mkC StB (mkS [] [] 0 0 []) S1 (mkS [S1;S1;S0] [] 0 0 []).
Definition ch_MC1z_1RB1RA_1LC0LD_0RA0LC_0RA1LD : list lstep := [SWin 1; SWinR 4].

Lemma run_MC1z_1RB1RA_1LC0LD_0RA0LC_0RA1LD : srun tm false true ch_MC1z_1RB1RA_1LC0LD_0RA0LC_0RA1LD c_MC1z0_1RB1RA_1LC0LD_0RA0LC_0RA1LD = Some (c_MC1z1_1RB1RA_1LC0LD_0RA0LC_0RA1LD, 0, 5).
Proof. vm_compute. reflexivity. Qed.

Definition c_MC0z0_1RB1RA_1LC0LD_0RA0LC_0RA1LD : sconf := mkC StB (mkS [S0] [] 0 0 []) S1 (mkS [S1] [] 0 0 []).
Definition c_MC0z1_1RB1RA_1LC0LD_0RA0LC_0RA1LD : sconf := mkC StB (mkS [] [] 0 0 []) S0 (mkS [S1;S1;S0] [] 0 0 []).
Definition ch_MC0z_1RB1RA_1LC0LD_0RA0LC_0RA1LD : list lstep := [SWin 1; SWinR 4].

Lemma run_MC0z_1RB1RA_1LC0LD_0RA0LC_0RA1LD : srun tm false true ch_MC0z_1RB1RA_1LC0LD_0RA0LC_0RA1LD c_MC0z0_1RB1RA_1LC0LD_0RA0LC_0RA1LD = Some (c_MC0z1_1RB1RA_1LC0LD_0RA0LC_0RA1LD, 0, 5).
Proof. vm_compute. reflexivity. Qed.

Definition c_TCp0_1RB1RA_1LC0LD_0RA0LC_0RA1LD : sconf := mkC StB (mkS [] [] 0 0 []) S0 (mkS [S1] [S1] 1 0 [S1;S0]).
Definition c_TCp1_1RB1RA_1LC0LD_0RA0LC_0RA1LD : sconf := mkC StA (mkS [] [S0] 1 1 [S1]) S0 (mkS [S0] [] 0 0 []).
Definition ch_TCp_1RB1RA_1LC0LD_0RA0LC_0RA1LD : list lstep := [SWin 1; SCycR 1; SWin 3; SFoldL 1].

Lemma run_TCp_1RB1RA_1LC0LD_0RA0LC_0RA1LD : srun tm false true ch_TCp_1RB1RA_1LC0LD_0RA0LC_0RA1LD c_TCp0_1RB1RA_1LC0LD_0RA0LC_0RA1LD = Some (c_TCp1_1RB1RA_1LC0LD_0RA0LC_0RA1LD, 1, 4).
Proof. vm_compute. reflexivity. Qed.

Definition c_TCz0_1RB1RA_1LC0LD_0RA0LC_0RA1LD : sconf := mkC StB (mkS [] [] 0 0 []) S0 (mkS [S1] [] 0 0 []).
Definition c_TCz1_1RB1RA_1LC0LD_0RA0LC_0RA1LD : sconf := mkC StA (mkS [S1] [] 0 0 []) S0 (mkS [S0] [] 0 0 []).
Definition ch_TCz_1RB1RA_1LC0LD_0RA0LC_0RA1LD : list lstep := [SWin 1; SWinR 2].

Lemma run_TCz_1RB1RA_1LC0LD_0RA0LC_0RA1LD : srun tm false true ch_TCz_1RB1RA_1LC0LD_0RA0LC_0RA1LD c_TCz0_1RB1RA_1LC0LD_0RA0LC_0RA1LD = Some (c_TCz1_1RB1RA_1LC0LD_0RA0LC_0RA1LD, 0, 3).
Proof. vm_compute. reflexivity. Qed.

Definition c_BOOT10_1RB1RA_1LC0LD_0RA0LC_0RA1LD : sconf := mkC StA (mkS [S1] [S1] 1 0 [S0]) S0 (mkS [] [] 0 0 []).
Definition c_BOOT11_1RB1RA_1LC0LD_0RA0LC_0RA1LD : sconf := mkC StB (mkS [] [S1] 1 0 [S0]) S1 (mkS [S1] [] 0 0 []).
Definition ch_BOOT1_1RB1RA_1LC0LD_0RA0LC_0RA1LD : list lstep := [SWin 1].

Lemma run_BOOT1_1RB1RA_1LC0LD_0RA0LC_0RA1LD : srun tm false true ch_BOOT1_1RB1RA_1LC0LD_0RA0LC_0RA1LD c_BOOT10_1RB1RA_1LC0LD_0RA0LC_0RA1LD = Some (c_BOOT11_1RB1RA_1LC0LD_0RA0LC_0RA1LD, 0, 1).
Proof. vm_compute. reflexivity. Qed.

Definition c_BOOT00_1RB1RA_1LC0LD_0RA0LC_0RA1LD : sconf := mkC StA (mkS [S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition c_BOOT01_1RB1RA_1LC0LD_0RA0LC_0RA1LD : sconf := mkC StB (mkS [] [] 0 0 []) S0 (mkS [S1] [] 0 0 []).
Definition ch_BOOT0_1RB1RA_1LC0LD_0RA0LC_0RA1LD : list lstep := [SWin 1].

Lemma run_BOOT0_1RB1RA_1LC0LD_0RA0LC_0RA1LD : srun tm false true ch_BOOT0_1RB1RA_1LC0LD_0RA0LC_0RA1LD c_BOOT00_1RB1RA_1LC0LD_0RA0LC_0RA1LD = Some (c_BOOT01_1RB1RA_1LC0LD_0RA0LC_0RA1LD, 0, 1).
Proof. vm_compute. reflexivity. Qed.

Definition c_BOOTO0_1RB1RA_1LC0LD_0RA0LC_0RA1LD : sconf := mkC StA (mkS [S1] [S1] 1 0 [S0]) S0 (mkS [] [] 0 0 []).
Definition c_BOOTO1_1RB1RA_1LC0LD_0RA0LC_0RA1LD : sconf := mkC StB (mkS [] [S1] 1 0 [S0]) S1 (mkS [S1] [] 0 0 []).
Definition ch_BOOTO_1RB1RA_1LC0LD_0RA0LC_0RA1LD : list lstep := [SWin 1].

Lemma run_BOOTO_1RB1RA_1LC0LD_0RA0LC_0RA1LD : srun tm false true ch_BOOTO_1RB1RA_1LC0LD_0RA0LC_0RA1LD c_BOOTO0_1RB1RA_1LC0LD_0RA0LC_0RA1LD = Some (c_BOOTO1_1RB1RA_1LC0LD_0RA0LC_0RA1LD, 0, 1).
Proof. vm_compute. reflexivity. Qed.

(** ** The micro hop *)

Lemma hop_1RB1RA_1LC0LD_0RA0LC_0RA1LD : forall W k m, exists n,
  csteps tm n (Cq W k (S m)) = Some (Cq W (S k) m) /\ 0 < n.
Proof.
  intros W k m.
  destruct m as [|m']; destruct k as [|k'].
  - (* k = 0, landing on the stop cell *)
    exists (0 * 0 + 5). split; [|lia].
    change (Cq W 0 1) with (cden W [] 0 c_MC0z0_1RB1RA_1LC0LD_0RA0LC_0RA1LD).
    rewrite (srun_sound tm false true ch_MC0z_1RB1RA_1LC0LD_0RA0LC_0RA1LD c_MC0z0_1RB1RA_1LC0LD_0RA0LC_0RA1LD c_MC0z1_1RB1RA_1LC0LD_0RA0LC_0RA1LD
               0 5 run_MC0z_1RB1RA_1LC0LD_0RA0LC_0RA1LD W [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    reflexivity.
  - (* k = S k', landing on the stop cell *)
    exists (2 * k' + 7). split; [|lia].
    assert (HS : Cq W (S k') 1 = cden W [] k' c_MC0p0_1RB1RA_1LC0LD_0RA0LC_0RA1LD).
    { unfold Cq_1RB1RA_1LC0LD_0RA0LC_0RA1LD, cden, c_MC0p0_1RB1RA_1LC0LD_0RA0LC_0RA1LD, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      replace (1 * k' + 0) with k' by lia.
      cbn [rep app]. rewrite <- ?app_assoc. reflexivity. }
    rewrite HS.
    rewrite (srun_sound tm false true ch_MC0p_1RB1RA_1LC0LD_0RA0LC_0RA1LD c_MC0p0_1RB1RA_1LC0LD_0RA0LC_0RA1LD c_MC0p1_1RB1RA_1LC0LD_0RA0LC_0RA1LD
               2 7 run_MC0p_1RB1RA_1LC0LD_0RA0LC_0RA1LD W [] k'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal; first
      [ reflexivity
      | unfold cden, c_MC0p1_1RB1RA_1LC0LD_0RA0LC_0RA1LD, Cq_1RB1RA_1LC0LD_0RA0LC_0RA1LD, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post];
        replace (1 * k' + 1) with (S k') by lia;
        cbn [rep app]; rewrite <- ?app_assoc; reflexivity ].
  - (* k = 0, landing on a digit *)
    exists (0 * 0 + 5). split; [|lia].
    change (Cq W 0 (S (S m')))
      with (cden (rep [S1] m' ++ [S0] ++ W) [] 0 c_MC1z0_1RB1RA_1LC0LD_0RA0LC_0RA1LD).
    rewrite (srun_sound tm false true ch_MC1z_1RB1RA_1LC0LD_0RA0LC_0RA1LD c_MC1z0_1RB1RA_1LC0LD_0RA0LC_0RA1LD c_MC1z1_1RB1RA_1LC0LD_0RA0LC_0RA1LD
               0 5 run_MC1z_1RB1RA_1LC0LD_0RA0LC_0RA1LD (rep [S1] m' ++ [S0] ++ W) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    reflexivity.
  - (* k = S k', landing on a digit *)
    exists (2 * k' + 7). split; [|lia].
    assert (HS : Cq W (S k') (S (S m'))
                 = cden (rep [S1] m' ++ [S0] ++ W) [] k' c_MC1p0_1RB1RA_1LC0LD_0RA0LC_0RA1LD).
    { unfold Cq_1RB1RA_1LC0LD_0RA0LC_0RA1LD, cden, c_MC1p0_1RB1RA_1LC0LD_0RA0LC_0RA1LD, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      replace (1 * k' + 0) with k' by lia.
      cbn [rep app]. rewrite <- ?app_assoc. reflexivity. }
    rewrite HS.
    rewrite (srun_sound tm false true ch_MC1p_1RB1RA_1LC0LD_0RA0LC_0RA1LD c_MC1p0_1RB1RA_1LC0LD_0RA0LC_0RA1LD c_MC1p1_1RB1RA_1LC0LD_0RA0LC_0RA1LD
               2 7 run_MC1p_1RB1RA_1LC0LD_0RA0LC_0RA1LD (rep [S1] m' ++ [S0] ++ W) [] k'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal; first
      [ reflexivity
      | unfold cden, c_MC1p1_1RB1RA_1LC0LD_0RA0LC_0RA1LD, Cq_1RB1RA_1LC0LD_0RA0LC_0RA1LD, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post];
        replace (1 * k' + 1) with (S k') by lia;
        cbn [rep app]; rewrite <- ?app_assoc; reflexivity ].
Qed.

(** ** The terminal: the carry write and the clearing sweep.  Its chain
    count is the FINAL probe depth k -- the anchor's carry index. *)

Lemma term_1RB1RA_1LC0LD_0RA0LC_0RA1LD : forall W k, exists n c',
  csteps tm n (Cq W k 0) = Some c'
  /\ c' = (StA, (rep [S0] k ++ [S1] ++ W, S0, ([]) ++ [S0])) /\ 0 < n.
Proof.
  intros W k. destruct k as [|k'].
  - exists (0 * 0 + 3). eexists. split; [|split; [reflexivity | lia]].
    change (Cq W 0 0) with (cden W [] 0 c_TCz0_1RB1RA_1LC0LD_0RA0LC_0RA1LD).
    rewrite (srun_sound tm false true ch_TCz_1RB1RA_1LC0LD_0RA0LC_0RA1LD c_TCz0_1RB1RA_1LC0LD_0RA0LC_0RA1LD c_TCz1_1RB1RA_1LC0LD_0RA0LC_0RA1LD
               0 3 run_TCz_1RB1RA_1LC0LD_0RA0LC_0RA1LD W [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal; first
      [ reflexivity
      | unfold cden, c_TCz1_1RB1RA_1LC0LD_0RA0LC_0RA1LD, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post];
        cbn [rep app]; rewrite ?app_nil_r, <- ?app_assoc; reflexivity ].
  - exists (1 * k' + 4). eexists.
    split; [|split; [reflexivity | lia]].
    assert (HS : Cq W (S k') 0 = cden W [] k' c_TCp0_1RB1RA_1LC0LD_0RA0LC_0RA1LD).
    { unfold Cq_1RB1RA_1LC0LD_0RA0LC_0RA1LD, cden, c_TCp0_1RB1RA_1LC0LD_0RA0LC_0RA1LD, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      replace (1 * k' + 0) with k' by lia.
      cbn [rep app]. rewrite <- ?app_assoc. reflexivity. }
    rewrite HS.
    rewrite (srun_sound tm false true ch_TCp_1RB1RA_1LC0LD_0RA0LC_0RA1LD c_TCp0_1RB1RA_1LC0LD_0RA0LC_0RA1LD c_TCp1_1RB1RA_1LC0LD_0RA0LC_0RA1LD
               1 4 run_TCp_1RB1RA_1LC0LD_0RA0LC_0RA1LD W [] k'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal; first
      [ reflexivity
      | unfold cden, c_TCp1_1RB1RA_1LC0LD_0RA0LC_0RA1LD, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post];
        replace (1 * k' + 1) with (S k') by lia;
        cbn [rep app]; rewrite ?app_nil_r, <- ?app_assoc; reflexivity ].
Qed.

(** ** The composed lap: boot + Theta(j) hops + terminal *)

Lemma qrun_1RB1RA_1LC0LD_0RA0LC_0RA1LD : forall W j, exists n c',
  csteps tm n (Cq W 0 j) = Some c'
  /\ lift c' = lift ((StA, (rep [S0] j ++ [S1] ++ W, S0, ([]) ++ [S0])) : cconf)
  /\ 0 < n.
Proof.
  intros W j.
  apply (quad_lap tm j (Cq_1RB1RA_1LC0LD_0RA0LC_0RA1LD W)).
  - intros k m _. exact (hop_1RB1RA_1LC0LD_0RA0LC_0RA1LD W k m).
  - intros k Hk. rewrite Nat.add_0_r in Hk. subst k.
    destruct (term_1RB1RA_1LC0LD_0RA0LC_0RA1LD W j) as (n & c' & Hrun & -> & Hn).
    exists n. eexists. split; [exact Hrun | split; [reflexivity | exact Hn]].
Qed.

(** ** The interior lap *)

Lemma lapi_1RB1RA_1LC0LD_0RA0LC_0RA1LD : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  destruct (KpCounter.cview_some_K p j q0 E) as (H1 & H2).
  destruct j as [|j''].
  - (* j = 0: the boot lands directly on the stop cell *)
    destruct (qrun_1RB1RA_1LC0LD_0RA0LC_0RA1LD (Kp q0 ++ [S0]) 0) as (n & c' & Hrun & Hl & Hn).
    exists ((0 * 0 + 1) + n), c'. split; [lia|]. split.
    { rewrite csteps_add.
      assert (HB : Cc p = cden (Kp q0 ++ [S0]) [] 0 c_BOOT00_1RB1RA_1LC0LD_0RA0LC_0RA1LD).
      { unfold Cc_1RB1RA_1LC0LD_0RA0LC_0RA1LD, cden, c_BOOT00_1RB1RA_1LC0LD_0RA0LC_0RA1LD, sden;
          cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
        rewrite H1. cbn [rep app]. rewrite <- ?app_assoc. reflexivity. }
      rewrite HB.
      rewrite (srun_sound tm false true ch_BOOT0_1RB1RA_1LC0LD_0RA0LC_0RA1LD c_BOOT00_1RB1RA_1LC0LD_0RA0LC_0RA1LD
                 c_BOOT01_1RB1RA_1LC0LD_0RA0LC_0RA1LD 0 1 run_BOOT0_1RB1RA_1LC0LD_0RA0LC_0RA1LD
                 (Kp q0 ++ [S0]) [] 0 ltac:(discriminate) ltac:(reflexivity)).
      assert (HQ : cden (Kp q0 ++ [S0]) [] 0 c_BOOT01_1RB1RA_1LC0LD_0RA0LC_0RA1LD
                   = Cq (Kp q0 ++ [S0]) 0 0).
      { unfold cden, c_BOOT01_1RB1RA_1LC0LD_0RA0LC_0RA1LD, Cq_1RB1RA_1LC0LD_0RA0LC_0RA1LD, sden;
          cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
        cbn [rep app]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity. }
      rewrite HQ. exact Hrun. }
    { rewrite Hl. unfold Cc_1RB1RA_1LC0LD_0RA0LC_0RA1LD. rewrite H2. rewrite !lift_app_blank. cbn [rep app].
      first [ reflexivity
            | rewrite <- ?app_assoc; cbn [app]; reflexivity ]. }
  - (* j = S j'': the boot lands on the first digit *)
    destruct (qrun_1RB1RA_1LC0LD_0RA0LC_0RA1LD (Kp q0 ++ [S0]) (S j''))
      as (n & c' & Hrun & Hl & Hn).
    exists ((0 * j'' + 1) + n), c'. split; [lia|]. split.
    { rewrite csteps_add.
      assert (HB : Cc p = cden (Kp q0 ++ [S0]) [] j'' c_BOOT10_1RB1RA_1LC0LD_0RA0LC_0RA1LD).
      { unfold Cc_1RB1RA_1LC0LD_0RA0LC_0RA1LD, cden, c_BOOT10_1RB1RA_1LC0LD_0RA0LC_0RA1LD, sden;
          cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
        replace (1 * j'' + 0) with j'' by lia.
        rewrite H1. cbn [rep app]. rewrite <- ?app_assoc. reflexivity. }
      rewrite HB.
      rewrite (srun_sound tm false true ch_BOOT1_1RB1RA_1LC0LD_0RA0LC_0RA1LD c_BOOT10_1RB1RA_1LC0LD_0RA0LC_0RA1LD
                 c_BOOT11_1RB1RA_1LC0LD_0RA0LC_0RA1LD 0 1 run_BOOT1_1RB1RA_1LC0LD_0RA0LC_0RA1LD
                 (Kp q0 ++ [S0]) [] j''
                 ltac:(discriminate) ltac:(reflexivity)).
      assert (HQ : cden (Kp q0 ++ [S0]) [] j'' c_BOOT11_1RB1RA_1LC0LD_0RA0LC_0RA1LD
                   = Cq (Kp q0 ++ [S0]) 0 (S j'')).
      { unfold cden, c_BOOT11_1RB1RA_1LC0LD_0RA0LC_0RA1LD, Cq_1RB1RA_1LC0LD_0RA0LC_0RA1LD, sden;
          cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
        replace (1 * j'' + 0) with j'' by lia.
        cbn [rep app]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity. }
      rewrite HQ. exact Hrun. }
    { rewrite Hl. unfold Cc_1RB1RA_1LC0LD_0RA0LC_0RA1LD. rewrite H2. rewrite !lift_app_blank. cbn [rep app].
      first [ reflexivity
            | rewrite <- ?app_assoc; cbn [app]; reflexivity ]. }
Qed.

(** ** The overflow lap: the same ladder, one probe deeper *)

Lemma gso_1RB1RA_1LC0LD_0RA0LC_0RA1LD : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j c_BOOTO0_1RB1RA_1LC0LD_0RA0LC_0RA1LD.
Proof.
  intros p j E. destruct (KpCounter.cview_none_K p j E) as (H1 & _).
  unfold Cc_1RB1RA_1LC0LD_0RA0LC_0RA1LD, cden, c_BOOTO0_1RB1RA_1LC0LD_0RA0LC_0RA1LD, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1; cbn [rep app].
  first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB1RA_1LC0LD_0RA0LC_0RA1LD : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma lapo_1RB1RA_1LC0LD_0RA0LC_0RA1LD : forall p j, cview p = (S j, None) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j E.
  destruct (KpCounter.cview_none_K p j E) as (_ & H2).
  destruct (qrun_1RB1RA_1LC0LD_0RA0LC_0RA1LD [] (S j)) as (n & c' & Hrun & Hl & Hn).
  exists ((0 * j + 1) + n), c'. split; [lia|]. split.
  { rewrite csteps_add.
    rewrite (gso_1RB1RA_1LC0LD_0RA0LC_0RA1LD p j E).
    rewrite (srun_sound tm false true ch_BOOTO_1RB1RA_1LC0LD_0RA0LC_0RA1LD c_BOOTO0_1RB1RA_1LC0LD_0RA0LC_0RA1LD
               c_BOOTO1_1RB1RA_1LC0LD_0RA0LC_0RA1LD 0 1 run_BOOTO_1RB1RA_1LC0LD_0RA0LC_0RA1LD [] [] j
               ltac:(discriminate) ltac:(reflexivity)).
    assert (HQ : cden [] [] j c_BOOTO1_1RB1RA_1LC0LD_0RA0LC_0RA1LD = Cq [] 0 (S j)).
    { unfold cden, c_BOOTO1_1RB1RA_1LC0LD_0RA0LC_0RA1LD, Cq_1RB1RA_1LC0LD_0RA0LC_0RA1LD, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      replace (1 * j + 0) with j by lia.
      cbn [rep app]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity. }
    rewrite HQ. exact Hrun. }
  { rewrite Hl. unfold Cc_1RB1RA_1LC0LD_0RA0LC_0RA1LD.
    assert (HG : Kp (Pos.succ p) ++ [S0] = (rep [S0] (S j) ++ [S1]) ++ [S0]).
    { rewrite H2.
      first [ rewrite <- !app_assoc; reflexivity
            | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
    rewrite HG. rewrite !lbl_1RB1RA_1LC0LD_0RA0LC_0RA1LD. rewrite !lift_app_blank. reflexivity. }
Qed.

(** ** The full lap *)

Lemma lap_1RB1RA_1LC0LD_0RA0LC_0RA1LD : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E; destruct oq as [q0|].
  - destruct (lapi_1RB1RA_1LC0LD_0RA0LC_0RA1LD p j q0 E) as (n & c' & Hn & Hrun & Hl).
    exists n, c'. split; [exact Hrun | split; [exact Hl | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    destruct (lapo_1RB1RA_1LC0LD_0RA0LC_0RA1LD p j' E) as (n & c' & Hn & Hrun & Hl).
    exists n, c'. split; [exact Hrun | split; [exact Hl | exact Hn]].
Qed.

(** ** Bootstrap *)

Lemma boot_1RB1RA_1LC0LD_0RA0LC_0RA1LD : exists t0, stepn tm t0 InitES = Some (lift (Cc 2)).
Proof.
  exists 14.
  assert (H : match csteps tm 14 c0 with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 14 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits: every state fires inside the overflow ladder *)

Lemma viso_1RB1RA_1LC0LD_0RA0LC_0RA1LD : forall (l : list lstep) (q : St),
  srun_st tm false true l c_BOOTO0_1RB1RA_1LC0LD_0RA0LC_0RA1LD = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc false true l c_BOOTO0_1RB1RA_1LC0LD_0RA0LC_0RA1LD p j [] []);
    [exact Hst | ltac:(intro; discriminate) | reflexivity
     | exact (gso_1RB1RA_1LC0LD_0RA0LC_0RA1LD p j E)].
Qed.

(** A state that fires INSIDE the ladder, not in the boot.  [vis_via_ovf]
    carries a witness taken from ONE chain prefix at the anchor, and for this
    board that chain is [BOOTO] -- so [viso_] cannot see this state at all.
    [QuadGlue.quad_reach0] walks the rungs to [Cq W j 0], where BOTH
    terminals start, and a prefix of the terminal chain is a witness there.
    The analogue of [NestedLapLift.vis_via_fill], needed for the same
    reason. *)
Lemma visq_1RB1RA_1LC0LD_0RA0LC_0RA1LD : forall (l : list lstep) (q : St),
  srun_st tm false true l c_TCp0_1RB1RA_1LC0LD_0RA0LC_0RA1LD = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  assert (HB : csteps tm (0 * j + 1) (Cc p) = Some (Cq [] 0 (S j))).
  { rewrite (gso_1RB1RA_1LC0LD_0RA0LC_0RA1LD p j E).
    rewrite (srun_sound tm false true ch_BOOTO_1RB1RA_1LC0LD_0RA0LC_0RA1LD c_BOOTO0_1RB1RA_1LC0LD_0RA0LC_0RA1LD
               c_BOOTO1_1RB1RA_1LC0LD_0RA0LC_0RA1LD 0 1 run_BOOTO_1RB1RA_1LC0LD_0RA0LC_0RA1LD [] [] j
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal.
    unfold cden, c_BOOTO1_1RB1RA_1LC0LD_0RA0LC_0RA1LD, Cq_1RB1RA_1LC0LD_0RA0LC_0RA1LD, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity. }
  destruct (quad_reach0 tm (S j) (Cq_1RB1RA_1LC0LD_0RA0LC_0RA1LD [])
              (fun k m (_ : k + S m = S j) => hop_1RB1RA_1LC0LD_0RA0LC_0RA1LD [] k m))
    as (n2 & H2).
  assert (HR : Cq [] (S j) 0 = cden [] [] j c_TCp0_1RB1RA_1LC0LD_0RA0LC_0RA1LD).
  { unfold Cq_1RB1RA_1LC0LD_0RA0LC_0RA1LD, cden, c_TCp0_1RB1RA_1LC0LD_0RA0LC_0RA1LD, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. reflexivity. }
  destruct (vis_of_run tm (fun _ : positive => Cq [] (S j) 0) false true
              l c_TCp0_1RB1RA_1LC0LD_0RA0LC_0RA1LD xH j [] [] q Hst
              ltac:(discriminate) ltac:(reflexivity) HR)
    as (k3 & c & H3 & Hq).
  exists ((0 * j + 1) + (n2 + k3)), c. split; [| exact Hq].
  rewrite csteps_add, HB, csteps_add, H2. exact H3.
Qed.

Lemma vis_1RB1RA_1LC0LD_0RA0LC_0RA1LD : forall p q,
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros p q.
  apply (vis_via_ovf_lift tm Cc lapi_1RB1RA_1LC0LD_0RA0LC_0RA1LD q).
  intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
  destruct q.
  - (* StA: the anchor state *)
    rewrite (gso_1RB1RA_1LC0LD_0RA0LC_0RA1LD p1 j1 E1).
    exists 0. eexists. split; reflexivity.
  - (* StB *)
    exact (viso_1RB1RA_1LC0LD_0RA0LC_0RA1LD [SWin 1] StB
             ltac:(vm_compute; reflexivity) p1 j1 E1).
  - (* StC: fires inside the ladder, not in the boot *)
    exact (visq_1RB1RA_1LC0LD_0RA0LC_0RA1LD [SWin 1] StC
             ltac:(vm_compute; reflexivity) p1 j1 E1).
  - (* StD *)
    exact (viso_1RB1RA_1LC0LD_0RA0LC_0RA1LD [SWin 1; SWin 1] StD
             ltac:(vm_compute; reflexivity) p1 j1 E1).
Qed.

Theorem nqhm_1RB1RA_1LC0LD_0RA0LC_0RA1LD : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh_lift tm Cc 2). - exact boot_1RB1RA_1LC0LD_0RA0LC_0RA1LD. - intros p _. apply lap_1RB1RA_1LC0LD_0RA0LC_0RA1LD. - intros p q _. apply vis_1RB1RA_1LC0LD_0RA0LC_0RA1LD. Qed.

Theorem nqh_1RB1RA_1LC0LD_0RA0LC_0RA1LD : NeverQuasiHaltsSt tm_1RB1RA_1LC0LD_0RA0LC_0RA1LD.
Proof. apply (mirror_never_qh tm_1RB1RA_1LC0LD_0RA0LC_0RA1LD). rewrite mirror_ok_1RB1RA_1LC0LD_0RA0LC_0RA1LD. exact nqhm_1RB1RA_1LC0LD_0RA0LC_0RA1LD. Qed.

Theorem nonhalt_1RB1RA_1LC0LD_0RA0LC_0RA1LD : NonHalt tm_1RB1RA_1LC0LD_0RA0LC_0RA1LD.
Proof. apply never_qh_nonhalt, nqh_1RB1RA_1LC0LD_0RA0LC_0RA1LD. Qed.
