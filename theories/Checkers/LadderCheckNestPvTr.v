(** * Checkers.LadderCheckNestPvTr: the nested ladder board with a visit
    phase PER INSTRUCTION.

    [LadderCheckNestTr.boardN_neverqhtr] witnesses every unpinned instruction
    from the fill anchors of ONE phase [pv].  A multi-phase counter whose
    rarest instruction fires only in the fill of another phase has no such
    phase: each phase's anchors miss a different instruction
    (SCOPING_INSTR 7.4.LE).  The liveness it needs is per instruction anyway
    ([LadderCheckTr.glue_neverqhtrN], [QHConveyorTr.lap_qh_stage]: for each
    unpinned [t], some anchor past every [N] reaches [t]), and
    [tops_cof_pv] gives cofinal tops at any phase the cycle returns to.  So
    here the visit phase is a function [pvf] of the instruction: [t] is
    witnessed from the fill anchors of phase [pvf t], and the cycle has to
    return to every [pvf t].

    The lap is [LadderCheckNestTr.lapN] as it stands (it does not see the
    visit phase); only the fires and the two closers are restated.  Axiom
    footprint: [functional_extensionality_dep], via [CTape.lift]. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr.
From BBB4.Counters Require Import WTape LapCertGlueLift.
From BBB4.Checkers Require Import WrapTr LapDecider LadderKernel LadderFam LadderCheck LadderCheckTr LadderNest LadderCheckNestTr TCyclerQHTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

Section BoardPvTr.

Variable tm0   : TM.
Variable pins  : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable F     : Fam.
Variable NPH   : nat.
Variable Aint  : nat -> nat -> LRule.
Variable N0i sti : nat.
Variable Afill : nat -> nat -> LRule.
Variable N0f stf : nat.
Variable fm1 fm2 : nat -> nat -> nat.
Variable pvf   : Instr -> nat.                 (** each instruction's phase *)
Variable rsv   : list LRule.
Variable vsegs : nat -> Instr -> list nseg.
Variable visI  : nat -> Instr -> list lstep.
Variable ds0   : list nat.
Variable ph0   : nat.

Hypothesis Hb    : 1 < fm_b F.
Hypothesis Hcode : fm_code F = Binary.
Hypothesis Hstep : fm_step F = 1.
Hypothesis Hfpre : forall ph, ph < NPH ->
  Forall (fun d => d < fm_b F) (f_pre (fam_fill F ph)).
Hypothesis Hfsuf : forall ph, ph < NPH ->
  Forall (fun d => d < fm_b F) (f_suf (fam_fill F ph)).
Hypothesis Hfmid : forall ph, ph < NPH -> f_mid (fam_fill F ph) < fm_b F.
Hypothesis Hfs   : forall ph, ph < NPH ->
  length (f_pre (fam_fill F ph)) + length (f_suf (fam_fill F ph))
  <= 1 + f_s (fam_fill F ph).
Hypothesis Hfto  : forall ph, ph < NPH -> f_to (fam_fill F ph) < NPH.
Hypothesis Hpv   : forall t, pvf t < NPH.
Hypothesis Hcyc  : forall t ph, ph < NPH -> exists k, phto F k ph = pvf t.
Hypothesis Hfm12 : forall r ph, 0 < r -> r < N0f + stf -> ph < NPH ->
  fm1 r ph + fm2 r ph
  + (length (f_pre (fam_fill F ph)) + length (f_suf (fam_fill F ph)))
  = r + f_s (fam_fill F ph).

Hypothesis Hbnd0 : Forall (fun d => d < fm_b F) ds0.
Hypothesis Hlen0 : 0 < length ds0.
Hypothesis Hph0  : ph0 < NPH.

Hypothesis Hsti : 0 < sti.
Hypothesis HAiS : forall d r, d < fm_b F - 1 -> r < N0i + sti ->
  ReachL tm (negb (fm_left F)) (fm_left F) (lr_lhs (Aint d r)) (lr_rhs (Aint d r)).
Hypothesis HAiL : forall d r, d < fm_b F - 1 -> r < N0i + sti ->
  lr_lhs (Aint d r)
    = cls_conf F (cls_side F [] (fm_b F - 1) r (astride N0i sti r) [d]).
Hypothesis HAiR : forall d r, d < fm_b F - 1 -> r < N0i + sti ->
  lr_rhs (Aint d r)
    = cls_conf F (cls_side F [] 0 r (astride N0i sti r) [S d]).

Hypothesis Hstf : 0 < stf.
Hypothesis HN0f : 0 < N0f.
Hypothesis HAfS : forall r ph, 0 < r -> r < N0f + stf -> ph < NPH ->
  ReachL tm true true (lr_lhs (Afill r ph)) (lr_rhs (Afill r ph)).
Hypothesis HAfL : forall r ph, 0 < r -> r < N0f + stf -> ph < NPH ->
  lr_lhs (Afill r ph)
    = cls_conf F (run_side F (fm_b F - 1) r (astride N0f stf r) 0 ph [] []).
Hypothesis HAfR : forall r ph, 0 < r -> r < N0f + stf -> ph < NPH ->
  lr_rhs (Afill r ph)
    = cls_conf F (run_side F (f_mid (fam_fill F ph)) (fm1 r ph)
                    (astride N0f stf r) (fm2 r ph) (f_to (fam_fill F ph))
                    (f_pre (fam_fill F ph)) (f_suf (fam_fill F ph))).

Hypothesis Hrsv : Forall (RuleSound tm false false) rsv.
Hypothesis Hfire : forall r t, ~ In t pins -> 0 < r -> r < N0f + stf ->
  nfire tm true true rsv (vsegs r t) (visI r t) (lr_lhs (Afill r (pvf t))) = Some t.

Local Notation Cf := (CfB F ds0 ph0).

(** [LadderCheckNestTr.lapN]: the lap does not see the visit phase. *)
Lemma lapP : forall n, exists m c,
  0 < m /\ csteps tm m (Cf n) = Some c /\ lift c = lift (Cf (S n)).
Proof.
  exact (lapN tm0 pins F NPH Aint N0i sti Afill N0f stf fm1 fm2
           (pvf (StA, S0)) ds0 ph0
           Hb Hcode Hstep Hfpre Hfsuf Hfmid Hfs Hfto (Hpv (StA, S0))
           Hfm12 Hbnd0 Hlen0 Hph0
           Hsti HAiS HAiL HAiR Hstf HN0f HAfS HAfL HAfR).
Qed.

(** [LadderCheckNestTr.board_fireN] at the instruction's own phase. *)
Lemma board_firePv : forall t N, ~ In t pins ->
  exists n k c, N <= n /\ csteps tm k (Cf n) = Some c /\ cinstr c = t.
Proof.
  intros t N Hnp.
  destruct (tops_cof_pv F NPH (pvf t) Hb Hcode Hstep Hfpre Hfsuf Hfmid Hfs Hfto
              (Hcyc t) (ds0, 0, ph0) N (inv0 F NPH ds0 ph0 Hbnd0 Hlen0 Hph0))
    as (n & s' & HN & Hit & Htop & Hi' & Hph).
  exists n.
  destruct s' as [[ds' p'] ph']. simpl in Htop. simpl in Hph. subst ph'.
  destruct Hi' as (Hbnd' & Hlen' & _).
  assert (Hsh : ds' = repeat (fm_b F - 1) (length ds'))
    by (apply pos1_top_shape; assumption).
  remember (aoff N0f stf (length ds')) as r eqn:Er.
  assert (Hr0 : 0 < r) by (subst r; apply arm_index_pos; assumption).
  assert (Hrlt : r < N0f + stf) by (subst r; apply arm_index_lt; assumption).
  assert (Hk : r + astride N0f stf r * acnt N0f stf (length ds') = length ds')
    by (subst r; apply arm_index; assumption).
  assert (Hden : Cf n
                 = cden [] [] (acnt N0f stf (length ds'))
                     (lr_lhs (Afill r (pvf t)))).
  { unfold CfB. rewrite Hit, (HAfL r (pvf t) Hr0 Hrlt (Hpv t)).
    rewrite <- (cden_cls_conf F
                  (run_side F (fm_b F - 1) r (astride N0f stf r) 0 (pvf t) [] [])
                  [] (acnt N0f stf (length ds')) ds' p' (pvf t)).
    - unfold tailL, tailR; destruct (fm_left F); reflexivity.
    - rewrite Hsh at 1. apply cells_top. exact Hk. }
  destruct (nfire_sound tm true true rsv (vsegs r t) (visI r t)
              (lr_lhs (Afill r (pvf t))) t Hrsv (Hfire r t Hnp Hr0 Hrlt)
              [] [] (acnt N0f stf (length ds'))
              (fun _ => eq_refl) (fun _ => eq_refl)) as (k & c & Hc & Ht).
  exists k, c. rewrite Hden. split; [exact HN | split; [exact Hc | exact Ht]].
Qed.

(** *** Never-quasihalting rows *)
Theorem boardPv_neverqhtr : forall t0,
  stepn tm t0 InitES = Some (lift (fam_cfg F (ds0, 0, ph0))) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros t0 Hboot.
  apply (glue_neverqhtrN tm0 pins Cf).
  - exists t0. unfold CfB; simpl. exact Hboot.
  - intros n. destruct (lapP n) as (m & c & Hm & Hrun & Hl).
    exists m, c. split; [exact Hrun | split; [exact Hl | exact Hm]].
  - intros t Hnp N. exact (board_firePv t N Hnp).
Qed.

(** *** Quasihalting rows *)

Lemma reachP : forall d n,
  exists T, stepn tm T (lift (Cf n)) = Some (lift (Cf (n + d))).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (T & HT).
    destruct (lapP (n + d)) as (m & c & _ & Hm & Hl).
    exists (T + m). rewrite stepn_add, HT.
    replace (n + S d) with (S (n + d)) by lia.
    rewrite <- Hl. apply csteps_lift. exact Hm.
Qed.

Lemma fire_everyP : forall t, ~ In t pins -> forall n,
  exists k c, csteps tm k (Cf n) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp n.
  destruct (board_firePv t n Hnp) as (m & k & c & Hm & Hk & Hc).
  destruct (reachP (m - n) n) as (T & HT).
  replace (n + (m - n)) with m in HT by lia.
  assert (Hs : stepn tm (T + k) (lift (Cf n)) = Some (lift c)).
  { rewrite stepn_add, HT. apply csteps_lift. exact Hk. }
  destruct (stepn_csteps_at tm (T + k) (Cf n) (lift c) Hs) as (c' & Hc' & Hl').
  exists (T + k), c'. split; [exact Hc'|].
  rewrite <- cinstr_lift, Hl', cinstr_lift. exact Hc.
Qed.

Theorem boardPv_qhtr : forall t0 B,
  stepn tm0 t0 InitES = Some (lift (fam_cfg F (ds0, 0, ph0))) ->
  existsb (fun tg => cfires tm0 CTape.c0 t0 tg) pins = true ->
  (t0 <=? B) = true ->
  NonHalt tm0 /\ QHBoundTr B tm0 /\ QuasiHaltsTr tm0.
Proof.
  intros t0 B Hboot Hwit Hle.
  apply (lap_qh_stage tm0 pins (fun p => Cf (Nat.pred (Pos.to_nat p)))
           1%positive t0 B).
  - simpl. unfold CfB; simpl. exact Hboot.
  - intros p _.
    destruct (lapP (Nat.pred (Pos.to_nat p))) as (m & c & Hm & Hrun & Hl).
    exists m, c. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (fire_everyP t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End BoardPvTr.
