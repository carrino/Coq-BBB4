(** * QMG_0RB0LA_1LA0RC_0LD1RC_1RB1LD: machine 0RB0LA_1LA0RC_0LD1RC_1RB1LD, boarded by CERTIFICATE (QUAD route).

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

Definition mk_0RB0LA_1LA0RC_0LD1RC_1RB1LD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB0LA_1LA0RC_0LD1RC_1RB1LD.

(** 0RB0LA_1LA0RC_0LD1RC_1RB1LD *)
(** 0RB0LA_1LA0RC_0LD1RC_1RB1LD -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB0LA_1LA0RC_0LD1RC_1RB1LD : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S0 DL StA
  | StB, S0 => mk S1 DL StA | StB, S1 => mk S0 DR StC
  | StC, S0 => mk S0 DL StD | StC, S1 => mk S1 DR StC
  | StD, S0 => mk S1 DR StB | StD, S1 => mk S1 DL StD end.

(** Its mirror 0LB0RA_1RA0LC_0RD1LC_1LB1RD: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB0LA_1LA0RC_0LD1RC_1RB1LD : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S0 DR StA
  | StB, S0 => mk S1 DR StA | StB, S1 => mk S0 DL StC
  | StC, S0 => mk S0 DR StD | StC, S1 => mk S1 DL StC
  | StD, S0 => mk S1 DL StB | StD, S1 => mk S1 DR StD end.
Local Notation tm := tmm_0RB0LA_1LA0RC_0LD1RC_1RB1LD.

Lemma mirror_ok_0RB0LA_1LA0RC_0LD1RC_1RB1LD : mirror_tm tm_0RB0LA_1LA0RC_0LD1RC_1RB1LD = tmm_0RB0LA_1LA0RC_0LD1RC_1RB1LD.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_0RB0LA_1LA0RC_0LD1RC_1RB1LD (p : positive) : cconf := (StA, (Kp p ++ [S0], S0, [])).
Local Notation Cc := Cc_0RB0LA_1LA0RC_0LD1RC_1RB1LD.

(** The two-index probe family (WAVE26 7d): k probed digits, m unprobed,
    deep word W opaque. *)
Definition Cq_0RB0LA_1LA0RC_0LD1RC_1RB1LD (W : list Sym) (k m : nat) : cconf :=
  match m with
  | O => (StB, (W, S0, rep [S1] k ++ [S0]))
  | S m' => (StB, (rep [S1] m' ++ [S0] ++ W, S1, rep [S1] k ++ [S0]))
  end.
Local Notation Cq := Cq_0RB0LA_1LA0RC_0LD1RC_1RB1LD.

(** ** The certificate: seven chains, all run by the kernel *)

Definition c_MD10_0RB0LA_1LA0RC_0LD1RC_1RB1LD : sconf := mkC StB (mkS [S1] [S1] 1 0 [S0]) S1 (mkS [] [] 0 0 []).
Definition c_MD11_0RB0LA_1LA0RC_0LD1RC_1RB1LD : sconf := mkC StB (mkS [] [S1] 1 0 [S0]) S1 (mkS [S1] [] 0 0 []).
Definition ch_MD1_0RB0LA_1LA0RC_0LD1RC_1RB1LD : list lstep := [SWin 1; SCycL 1 0; SWin 2; SCycR 1; SWin 2].

Lemma run_MD1_0RB0LA_1LA0RC_0LD1RC_1RB1LD : srun tm false false ch_MD1_0RB0LA_1LA0RC_0LD1RC_1RB1LD c_MD10_0RB0LA_1LA0RC_0LD1RC_1RB1LD = Some (c_MD11_0RB0LA_1LA0RC_0LD1RC_1RB1LD, 2, 5).
Proof. vm_compute. reflexivity. Qed.

Definition c_MD00_0RB0LA_1LA0RC_0LD1RC_1RB1LD : sconf := mkC StB (mkS [S0] [] 0 0 []) S1 (mkS [] [] 0 0 []).
Definition c_MD01_0RB0LA_1LA0RC_0LD1RC_1RB1LD : sconf := mkC StB (mkS [] [] 0 0 []) S0 (mkS [S1] [] 0 0 []).
Definition ch_MD0_0RB0LA_1LA0RC_0LD1RC_1RB1LD : list lstep := [SWin 3].

Lemma run_MD0_0RB0LA_1LA0RC_0LD1RC_1RB1LD : srun tm false false ch_MD0_0RB0LA_1LA0RC_0LD1RC_1RB1LD c_MD00_0RB0LA_1LA0RC_0LD1RC_1RB1LD = Some (c_MD01_0RB0LA_1LA0RC_0LD1RC_1RB1LD, 0, 3).
Proof. vm_compute. reflexivity. Qed.

Definition c_TCp0_0RB0LA_1LA0RC_0LD1RC_1RB1LD : sconf := mkC StB (mkS [] [] 0 0 []) S0 (mkS [S1] [S1] 1 0 [S0]).
Definition c_TCp1_0RB0LA_1LA0RC_0LD1RC_1RB1LD : sconf := mkC StA (mkS [] [S0] 1 1 [S1]) S0 (mkS [] [] 0 0 []).
Definition ch_TCp_0RB0LA_1LA0RC_0LD1RC_1RB1LD : list lstep := [SWin 1; SCycR 1; SWin 1; SFoldL 1].

Lemma run_TCp_0RB0LA_1LA0RC_0LD1RC_1RB1LD : srun tm false true ch_TCp_0RB0LA_1LA0RC_0LD1RC_1RB1LD c_TCp0_0RB0LA_1LA0RC_0LD1RC_1RB1LD = Some (c_TCp1_0RB0LA_1LA0RC_0LD1RC_1RB1LD, 1, 2).
Proof. vm_compute. reflexivity. Qed.

Definition c_TCz0_0RB0LA_1LA0RC_0LD1RC_1RB1LD : sconf := mkC StB (mkS [] [] 0 0 []) S0 (mkS [S0] [] 0 0 []).
Definition c_TCz1_0RB0LA_1LA0RC_0LD1RC_1RB1LD : sconf := mkC StA (mkS [S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition ch_TCz_0RB0LA_1LA0RC_0LD1RC_1RB1LD : list lstep := [SWin 1].

Lemma run_TCz_0RB0LA_1LA0RC_0LD1RC_1RB1LD : srun tm false true ch_TCz_0RB0LA_1LA0RC_0LD1RC_1RB1LD c_TCz0_0RB0LA_1LA0RC_0LD1RC_1RB1LD = Some (c_TCz1_0RB0LA_1LA0RC_0LD1RC_1RB1LD, 0, 1).
Proof. vm_compute. reflexivity. Qed.

Definition c_BOOT10_0RB0LA_1LA0RC_0LD1RC_1RB1LD : sconf := mkC StA (mkS [S1] [S1] 1 0 [S0]) S0 (mkS [] [] 0 0 []).
Definition c_BOOT11_0RB0LA_1LA0RC_0LD1RC_1RB1LD : sconf := mkC StB (mkS [] [S1] 1 0 [S0]) S1 (mkS [S0] [] 0 0 []).
Definition ch_BOOT1_0RB0LA_1LA0RC_0LD1RC_1RB1LD : list lstep := [SWin 1].

Lemma run_BOOT1_0RB0LA_1LA0RC_0LD1RC_1RB1LD : srun tm false true ch_BOOT1_0RB0LA_1LA0RC_0LD1RC_1RB1LD c_BOOT10_0RB0LA_1LA0RC_0LD1RC_1RB1LD = Some (c_BOOT11_0RB0LA_1LA0RC_0LD1RC_1RB1LD, 0, 1).
Proof. vm_compute. reflexivity. Qed.

Definition c_BOOT00_0RB0LA_1LA0RC_0LD1RC_1RB1LD : sconf := mkC StA (mkS [S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition c_BOOT01_0RB0LA_1LA0RC_0LD1RC_1RB1LD : sconf := mkC StB (mkS [] [] 0 0 []) S0 (mkS [S0] [] 0 0 []).
Definition ch_BOOT0_0RB0LA_1LA0RC_0LD1RC_1RB1LD : list lstep := [SWin 1].

Lemma run_BOOT0_0RB0LA_1LA0RC_0LD1RC_1RB1LD : srun tm false true ch_BOOT0_0RB0LA_1LA0RC_0LD1RC_1RB1LD c_BOOT00_0RB0LA_1LA0RC_0LD1RC_1RB1LD = Some (c_BOOT01_0RB0LA_1LA0RC_0LD1RC_1RB1LD, 0, 1).
Proof. vm_compute. reflexivity. Qed.

Definition c_BOOTO0_0RB0LA_1LA0RC_0LD1RC_1RB1LD : sconf := mkC StA (mkS [S1] [S1] 1 0 [S0]) S0 (mkS [] [] 0 0 []).
Definition c_BOOTO1_0RB0LA_1LA0RC_0LD1RC_1RB1LD : sconf := mkC StB (mkS [] [S1] 1 0 [S0]) S1 (mkS [S0] [] 0 0 []).
Definition ch_BOOTO_0RB0LA_1LA0RC_0LD1RC_1RB1LD : list lstep := [SWin 1].

Lemma run_BOOTO_0RB0LA_1LA0RC_0LD1RC_1RB1LD : srun tm false true ch_BOOTO_0RB0LA_1LA0RC_0LD1RC_1RB1LD c_BOOTO0_0RB0LA_1LA0RC_0LD1RC_1RB1LD = Some (c_BOOTO1_0RB0LA_1LA0RC_0LD1RC_1RB1LD, 0, 1).
Proof. vm_compute. reflexivity. Qed.

(** ** The micro hop *)

(** The DEEP-PIVOT hop.  This machine's round trip runs out to the deepest
    UNPROBED digit rather than back to the anchor, so its cost is
    [Theta(m)], not [Theta(k)] -- the chain's index is the unprobed count
    and the peel is at the LANDING, not at the start.  The right side, which
    the hop only ever touches at the head-adjacent cell, rides in the
    chain's OPAQUE tail ([er = false], [XR = rep RU k ++ RPOST]); that is
    what lets ONE chain cover every probe depth at once, and it is why this
    regime needs two chains where the near-pivot one needs four. *)
Lemma hop_0RB0LA_1LA0RC_0LD1RC_1RB1LD : forall W k m, exists n,
  csteps tm n (Cq W k (S m)) = Some (Cq W (S k) m) /\ 0 < n.
Proof.
  intros W k m.
  destruct m as [|m'].
  - (* the landing rung: one concrete hop, at every probe depth *)
    exists (0 * 0 + 3). split; [|lia].
    assert (HS : Cq W k 1 = cden W (rep [S1] k ++ [S0]) 0 c_MD00_0RB0LA_1LA0RC_0LD1RC_1RB1LD).
    { unfold Cq_0RB0LA_1LA0RC_0LD1RC_1RB1LD, cden, c_MD00_0RB0LA_1LA0RC_0LD1RC_1RB1LD, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      cbn [rep app]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity. }
    rewrite HS.
    rewrite (srun_sound tm false false ch_MD0_0RB0LA_1LA0RC_0LD1RC_1RB1LD c_MD00_0RB0LA_1LA0RC_0LD1RC_1RB1LD c_MD01_0RB0LA_1LA0RC_0LD1RC_1RB1LD
               0 3 run_MD0_0RB0LA_1LA0RC_0LD1RC_1RB1LD W (rep [S1] k ++ [S0]) 0
               ltac:(discriminate) ltac:(discriminate)).
    unfold cden, c_MD01_0RB0LA_1LA0RC_0LD1RC_1RB1LD, Cq_0RB0LA_1LA0RC_0LD1RC_1RB1LD, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    cbn [rep app]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
  - (* a digit rung: the index is the unprobed count, peeled once *)
    exists (2 * m' + 5). split; [|lia].
    assert (HS : Cq W k (S (S m'))
                 = cden W (rep [S1] k ++ [S0]) m' c_MD10_0RB0LA_1LA0RC_0LD1RC_1RB1LD).
    { unfold Cq_0RB0LA_1LA0RC_0LD1RC_1RB1LD, cden, c_MD10_0RB0LA_1LA0RC_0LD1RC_1RB1LD, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      replace (1 * m' + 0) with m' by lia.
      cbn [rep app]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity. }
    rewrite HS.
    rewrite (srun_sound tm false false ch_MD1_0RB0LA_1LA0RC_0LD1RC_1RB1LD c_MD10_0RB0LA_1LA0RC_0LD1RC_1RB1LD c_MD11_0RB0LA_1LA0RC_0LD1RC_1RB1LD
               2 5 run_MD1_0RB0LA_1LA0RC_0LD1RC_1RB1LD W (rep [S1] k ++ [S0]) m'
               ltac:(discriminate) ltac:(discriminate)).
    unfold cden, c_MD11_0RB0LA_1LA0RC_0LD1RC_1RB1LD, Cq_0RB0LA_1LA0RC_0LD1RC_1RB1LD, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * m' + 0) with m' by lia.
    cbn [rep app]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

(** ** The terminal: the carry write and the clearing sweep.  Its chain
    count is the FINAL probe depth k -- the anchor's carry index. *)

Lemma term_0RB0LA_1LA0RC_0LD1RC_1RB1LD : forall W k, exists n c',
  csteps tm n (Cq W k 0) = Some c'
  /\ c' = (StA, (rep [S0] k ++ [S1] ++ W, S0, [])) /\ 0 < n.
Proof.
  intros W k. destruct k as [|k'].
  - exists (0 * 0 + 1). eexists. split; [|split; [reflexivity | lia]].
    change (Cq W 0 0) with (cden W [] 0 c_TCz0_0RB0LA_1LA0RC_0LD1RC_1RB1LD).
    rewrite (srun_sound tm false true ch_TCz_0RB0LA_1LA0RC_0LD1RC_1RB1LD c_TCz0_0RB0LA_1LA0RC_0LD1RC_1RB1LD c_TCz1_0RB0LA_1LA0RC_0LD1RC_1RB1LD
               0 1 run_TCz_0RB0LA_1LA0RC_0LD1RC_1RB1LD W [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal; first
      [ reflexivity
      | unfold cden, c_TCz1_0RB0LA_1LA0RC_0LD1RC_1RB1LD, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post];
        cbn [rep app]; rewrite ?app_nil_r, <- ?app_assoc; reflexivity ].
  - exists (1 * k' + 2). eexists.
    split; [|split; [reflexivity | lia]].
    assert (HS : Cq W (S k') 0 = cden W [] k' c_TCp0_0RB0LA_1LA0RC_0LD1RC_1RB1LD).
    { unfold Cq_0RB0LA_1LA0RC_0LD1RC_1RB1LD, cden, c_TCp0_0RB0LA_1LA0RC_0LD1RC_1RB1LD, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      replace (1 * k' + 0) with k' by lia.
      cbn [rep app]. rewrite <- ?app_assoc. reflexivity. }
    rewrite HS.
    rewrite (srun_sound tm false true ch_TCp_0RB0LA_1LA0RC_0LD1RC_1RB1LD c_TCp0_0RB0LA_1LA0RC_0LD1RC_1RB1LD c_TCp1_0RB0LA_1LA0RC_0LD1RC_1RB1LD
               1 2 run_TCp_0RB0LA_1LA0RC_0LD1RC_1RB1LD W [] k'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal; first
      [ reflexivity
      | unfold cden, c_TCp1_0RB0LA_1LA0RC_0LD1RC_1RB1LD, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post];
        replace (1 * k' + 1) with (S k') by lia;
        cbn [rep app]; rewrite ?app_nil_r, <- ?app_assoc; reflexivity ].
Qed.

(** ** The composed lap: boot + Theta(j) hops + terminal *)

Lemma qrun_0RB0LA_1LA0RC_0LD1RC_1RB1LD : forall W j, exists n c',
  csteps tm n (Cq W 0 j) = Some c'
  /\ lift c' = lift ((StA, (rep [S0] j ++ [S1] ++ W, S0, [])) : cconf)
  /\ 0 < n.
Proof.
  intros W j.
  apply (quad_lap tm j (Cq_0RB0LA_1LA0RC_0LD1RC_1RB1LD W)).
  - intros k m _. exact (hop_0RB0LA_1LA0RC_0LD1RC_1RB1LD W k m).
  - intros k Hk. rewrite Nat.add_0_r in Hk. subst k.
    destruct (term_0RB0LA_1LA0RC_0LD1RC_1RB1LD W j) as (n & c' & Hrun & -> & Hn).
    exists n. eexists. split; [exact Hrun | split; [reflexivity | exact Hn]].
Qed.

(** ** The interior lap *)

Lemma lapi_0RB0LA_1LA0RC_0LD1RC_1RB1LD : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  destruct (KpCounter.cview_some_K p j q0 E) as (H1 & H2).
  destruct j as [|j''].
  - (* j = 0: the boot lands directly on the stop cell *)
    destruct (qrun_0RB0LA_1LA0RC_0LD1RC_1RB1LD (Kp q0 ++ [S0]) 0) as (n & c' & Hrun & Hl & Hn).
    exists ((0 * 0 + 1) + n), c'. split; [lia|]. split.
    { rewrite csteps_add.
      assert (HB : Cc p = cden (Kp q0 ++ [S0]) [] 0 c_BOOT00_0RB0LA_1LA0RC_0LD1RC_1RB1LD).
      { unfold Cc_0RB0LA_1LA0RC_0LD1RC_1RB1LD, cden, c_BOOT00_0RB0LA_1LA0RC_0LD1RC_1RB1LD, sden;
          cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
        rewrite H1. cbn [rep app]. rewrite <- ?app_assoc. reflexivity. }
      rewrite HB.
      rewrite (srun_sound tm false true ch_BOOT0_0RB0LA_1LA0RC_0LD1RC_1RB1LD c_BOOT00_0RB0LA_1LA0RC_0LD1RC_1RB1LD
                 c_BOOT01_0RB0LA_1LA0RC_0LD1RC_1RB1LD 0 1 run_BOOT0_0RB0LA_1LA0RC_0LD1RC_1RB1LD
                 (Kp q0 ++ [S0]) [] 0 ltac:(discriminate) ltac:(reflexivity)).
      assert (HQ : cden (Kp q0 ++ [S0]) [] 0 c_BOOT01_0RB0LA_1LA0RC_0LD1RC_1RB1LD
                   = Cq (Kp q0 ++ [S0]) 0 0).
      { unfold cden, c_BOOT01_0RB0LA_1LA0RC_0LD1RC_1RB1LD, Cq_0RB0LA_1LA0RC_0LD1RC_1RB1LD, sden;
          cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
        cbn [rep app]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity. }
      rewrite HQ. exact Hrun. }
    { rewrite Hl. unfold Cc_0RB0LA_1LA0RC_0LD1RC_1RB1LD. rewrite H2. cbn [rep app].
      first [ reflexivity
            | rewrite <- ?app_assoc; cbn [app]; reflexivity ]. }
  - (* j = S j'': the boot lands on the first digit *)
    destruct (qrun_0RB0LA_1LA0RC_0LD1RC_1RB1LD (Kp q0 ++ [S0]) (S j''))
      as (n & c' & Hrun & Hl & Hn).
    exists ((0 * j'' + 1) + n), c'. split; [lia|]. split.
    { rewrite csteps_add.
      assert (HB : Cc p = cden (Kp q0 ++ [S0]) [] j'' c_BOOT10_0RB0LA_1LA0RC_0LD1RC_1RB1LD).
      { unfold Cc_0RB0LA_1LA0RC_0LD1RC_1RB1LD, cden, c_BOOT10_0RB0LA_1LA0RC_0LD1RC_1RB1LD, sden;
          cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
        replace (1 * j'' + 0) with j'' by lia.
        rewrite H1. cbn [rep app]. rewrite <- ?app_assoc. reflexivity. }
      rewrite HB.
      rewrite (srun_sound tm false true ch_BOOT1_0RB0LA_1LA0RC_0LD1RC_1RB1LD c_BOOT10_0RB0LA_1LA0RC_0LD1RC_1RB1LD
                 c_BOOT11_0RB0LA_1LA0RC_0LD1RC_1RB1LD 0 1 run_BOOT1_0RB0LA_1LA0RC_0LD1RC_1RB1LD
                 (Kp q0 ++ [S0]) [] j''
                 ltac:(discriminate) ltac:(reflexivity)).
      assert (HQ : cden (Kp q0 ++ [S0]) [] j'' c_BOOT11_0RB0LA_1LA0RC_0LD1RC_1RB1LD
                   = Cq (Kp q0 ++ [S0]) 0 (S j'')).
      { unfold cden, c_BOOT11_0RB0LA_1LA0RC_0LD1RC_1RB1LD, Cq_0RB0LA_1LA0RC_0LD1RC_1RB1LD, sden;
          cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
        replace (1 * j'' + 0) with j'' by lia.
        cbn [rep app]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity. }
      rewrite HQ. exact Hrun. }
    { rewrite Hl. unfold Cc_0RB0LA_1LA0RC_0LD1RC_1RB1LD. rewrite H2. cbn [rep app].
      first [ reflexivity
            | rewrite <- ?app_assoc; cbn [app]; reflexivity ]. }
Qed.

(** ** The overflow lap: the same ladder, one probe deeper *)

Lemma gso_0RB0LA_1LA0RC_0LD1RC_1RB1LD : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j c_BOOTO0_0RB0LA_1LA0RC_0LD1RC_1RB1LD.
Proof.
  intros p j E. destruct (KpCounter.cview_none_K p j E) as (H1 & _).
  unfold Cc_0RB0LA_1LA0RC_0LD1RC_1RB1LD, cden, c_BOOTO0_0RB0LA_1LA0RC_0LD1RC_1RB1LD, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1; cbn [rep app].
  first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_0RB0LA_1LA0RC_0LD1RC_1RB1LD : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma lapo_0RB0LA_1LA0RC_0LD1RC_1RB1LD : forall p j, cview p = (S j, None) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j E.
  destruct (KpCounter.cview_none_K p j E) as (_ & H2).
  destruct (qrun_0RB0LA_1LA0RC_0LD1RC_1RB1LD [] (S j)) as (n & c' & Hrun & Hl & Hn).
  exists ((0 * j + 1) + n), c'. split; [lia|]. split.
  { rewrite csteps_add.
    rewrite (gso_0RB0LA_1LA0RC_0LD1RC_1RB1LD p j E).
    rewrite (srun_sound tm false true ch_BOOTO_0RB0LA_1LA0RC_0LD1RC_1RB1LD c_BOOTO0_0RB0LA_1LA0RC_0LD1RC_1RB1LD
               c_BOOTO1_0RB0LA_1LA0RC_0LD1RC_1RB1LD 0 1 run_BOOTO_0RB0LA_1LA0RC_0LD1RC_1RB1LD [] [] j
               ltac:(discriminate) ltac:(reflexivity)).
    assert (HQ : cden [] [] j c_BOOTO1_0RB0LA_1LA0RC_0LD1RC_1RB1LD = Cq [] 0 (S j)).
    { unfold cden, c_BOOTO1_0RB0LA_1LA0RC_0LD1RC_1RB1LD, Cq_0RB0LA_1LA0RC_0LD1RC_1RB1LD, sden;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      replace (1 * j + 0) with j by lia.
      cbn [rep app]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity. }
    rewrite HQ. exact Hrun. }
  { rewrite Hl. unfold Cc_0RB0LA_1LA0RC_0LD1RC_1RB1LD.
    assert (HG : Kp (Pos.succ p) ++ [S0] = (rep [S0] (S j) ++ [S1]) ++ [S0]).
    { rewrite H2.
      first [ rewrite <- !app_assoc; reflexivity
            | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
    rewrite HG. rewrite !lbl_0RB0LA_1LA0RC_0LD1RC_1RB1LD. reflexivity. }
Qed.

(** ** The full lap *)

Lemma lap_0RB0LA_1LA0RC_0LD1RC_1RB1LD : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E; destruct oq as [q0|].
  - destruct (lapi_0RB0LA_1LA0RC_0LD1RC_1RB1LD p j q0 E) as (n & c' & Hn & Hrun & Hl).
    exists n, c'. split; [exact Hrun | split; [exact Hl | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    destruct (lapo_0RB0LA_1LA0RC_0LD1RC_1RB1LD p j' E) as (n & c' & Hn & Hrun & Hl).
    exists n, c'. split; [exact Hrun | split; [exact Hl | exact Hn]].
Qed.

(** ** Bootstrap *)

Lemma boot_0RB0LA_1LA0RC_0LD1RC_1RB1LD : exists t0, stepn tm t0 InitES = Some (lift (Cc 2)).
Proof.
  exists 8.
  assert (H : match csteps tm 8 c0 with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 8 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits: every state fires inside the overflow ladder *)

Lemma viso_0RB0LA_1LA0RC_0LD1RC_1RB1LD : forall (l : list lstep) (q : St),
  srun_st tm false true l c_BOOTO0_0RB0LA_1LA0RC_0LD1RC_1RB1LD = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc false true l c_BOOTO0_0RB0LA_1LA0RC_0LD1RC_1RB1LD p j [] []);
    [exact Hst | ltac:(intro; discriminate) | reflexivity
     | exact (gso_0RB0LA_1LA0RC_0LD1RC_1RB1LD p j E)].
Qed.

(** A state that fires in the MICRO HOP -- neither in the boot nor in the
    terminal, so neither [viso_] nor [visq_] can see it.  The hop applies at
    every rung, but the only rung that EXISTS at every overflow anchor is
    the last one ([Cq W j 1]; an interior rung needs [j >= 1]).
    [QuadGlue.quad_reach_at] stops the ladder walk exactly there and a
    prefix of the [m = 1] hop chain fires from it. *)
Lemma visr_0RB0LA_1LA0RC_0LD1RC_1RB1LD : forall (l : list lstep) (q : St),
  srun_st tm false false l c_MD00_0RB0LA_1LA0RC_0LD1RC_1RB1LD = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  assert (HB : csteps tm (0 * j + 1) (Cc p) = Some (Cq [] 0 (S j))).
  { rewrite (gso_0RB0LA_1LA0RC_0LD1RC_1RB1LD p j E).
    rewrite (srun_sound tm false true ch_BOOTO_0RB0LA_1LA0RC_0LD1RC_1RB1LD c_BOOTO0_0RB0LA_1LA0RC_0LD1RC_1RB1LD
               c_BOOTO1_0RB0LA_1LA0RC_0LD1RC_1RB1LD 0 1 run_BOOTO_0RB0LA_1LA0RC_0LD1RC_1RB1LD [] [] j
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal.
    unfold cden, c_BOOTO1_0RB0LA_1LA0RC_0LD1RC_1RB1LD, Cq_0RB0LA_1LA0RC_0LD1RC_1RB1LD, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity. }
  destruct (quad_reach_at tm (S j) (Cq_0RB0LA_1LA0RC_0LD1RC_1RB1LD [])
              (fun k m (_ : k + S m = S j) => hop_0RB0LA_1LA0RC_0LD1RC_1RB1LD [] k m) j 1
              ltac:(lia))
    as (n2 & H2).
  assert (HR : Cq [] j 1 = cden [] (rep [S1] j ++ [S0]) 0
                                 c_MD00_0RB0LA_1LA0RC_0LD1RC_1RB1LD).
  { unfold Cq_0RB0LA_1LA0RC_0LD1RC_1RB1LD, cden, c_MD00_0RB0LA_1LA0RC_0LD1RC_1RB1LD, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    cbn [rep app]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity. }
  destruct (vis_of_run tm (fun _ : positive => Cq [] j 1) false false
              l c_MD00_0RB0LA_1LA0RC_0LD1RC_1RB1LD xH 0 [] (rep [S1] j ++ [S0]) q Hst
              ltac:(discriminate) ltac:(discriminate) HR)
    as (k3 & c & H3 & Hq).
  exists ((0 * j + 1) + (n2 + k3)), c. split; [| exact Hq].
  rewrite csteps_add, HB, csteps_add, H2. exact H3.
Qed.

Lemma vis_0RB0LA_1LA0RC_0LD1RC_1RB1LD : forall p q,
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros p q.
  apply (vis_via_ovf_lift tm Cc lapi_0RB0LA_1LA0RC_0LD1RC_1RB1LD q).
  intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
  destruct q.
  - (* StA: the anchor state *)
    rewrite (gso_0RB0LA_1LA0RC_0LD1RC_1RB1LD p1 j1 E1).
    exists 0. eexists. split; reflexivity.
  - (* StB *)
    exact (viso_0RB0LA_1LA0RC_0LD1RC_1RB1LD [SWin 1] StB
             ltac:(vm_compute; reflexivity) p1 j1 E1).
  - (* StC: fires in the micro hop *)
    exact (visr_0RB0LA_1LA0RC_0LD1RC_1RB1LD [SWin 1] StC
             ltac:(vm_compute; reflexivity) p1 j1 E1).
  - (* StD: fires in the micro hop *)
    exact (visr_0RB0LA_1LA0RC_0LD1RC_1RB1LD [SWin 2] StD
             ltac:(vm_compute; reflexivity) p1 j1 E1).
Qed.

Theorem nqhm_0RB0LA_1LA0RC_0LD1RC_1RB1LD : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh_lift tm Cc 2). - exact boot_0RB0LA_1LA0RC_0LD1RC_1RB1LD. - intros p _. apply lap_0RB0LA_1LA0RC_0LD1RC_1RB1LD. - intros p q _. apply vis_0RB0LA_1LA0RC_0LD1RC_1RB1LD. Qed.

Theorem nqh_0RB0LA_1LA0RC_0LD1RC_1RB1LD : NeverQuasiHaltsSt tm_0RB0LA_1LA0RC_0LD1RC_1RB1LD.
Proof. apply (mirror_never_qh tm_0RB0LA_1LA0RC_0LD1RC_1RB1LD). rewrite mirror_ok_0RB0LA_1LA0RC_0LD1RC_1RB1LD. exact nqhm_0RB0LA_1LA0RC_0LD1RC_1RB1LD. Qed.

Theorem nonhalt_0RB0LA_1LA0RC_0LD1RC_1RB1LD : NonHalt tm_0RB0LA_1LA0RC_0LD1RC_1RB1LD.
Proof. apply never_qh_nonhalt, nqh_0RB0LA_1LA0RC_0LD1RC_1RB1LD. Qed.
