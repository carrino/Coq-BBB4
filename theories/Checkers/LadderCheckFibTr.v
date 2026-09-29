(** * Checkers.LadderCheckFibTr: the FIBONACCI ladder at the INSTRUCTION
    level, on both sides.

    [LadderCheck] section 11 ([boardF_neverqh]) closes a counter whose
    digits read in the kernel's fibonacci numeration ([(Fib, 1)]:
    [LadderFam.fibw] = 1, 1, 2, 3, 5, 8, the greedy representative) to
    [NeverQuasiHaltsSt].  This file is [LadderCheckTr] and
    [LadderCheckQHTr] done again for that section, and needs nothing new
    from the ladder:

    - the board (arms, fill, visit chains) runs on the machine WRAPPED at
      its pins; the per-state visit chains become per-INSTRUCTION chains
      ([LapGlueTr.srun_instr], [fire_of_run_instr]), [board_fireF] being
      [LadderCheck.board_visitF] with that substitution;
    - never-quasihalting rows: the boot runs on the wrapped machine too and
      [LadderCheckTr.glue_neverqhtrN] closes ([boardF_neverqhtr]);
    - quasihalting rows: the boot runs on the ORIGINAL machine to a member
      past the pins' last fire, and [QHConveyorTr.lap_qh_stage] closes over
      the anchors re-indexed by [positive] ([boardF_qhtr]), exactly as
      [LadderCheckQHTr.boardph_qhtr] does at [(Binary, 1)].

    Why a ladder section and not a [MonoCounter.cview]-style digit family
    (SCOPING_INSTR 7.4.CE2): [cview] splits a [positive] at its run of low
    set bits, which IS the binary carry.  A fibonacci counter has no
    [positive] to index by and its increment is not a fixed-radix roll-over
    ([F(k) + F(k+1) -> F(k+2)]), so a per-board [cview] glue would have to
    re-prove the numeration on every board.  [LadderFam]/[LadderCheck]
    already state it once ([fib_split], [fib_class], [topsF_cofinal]); the
    port is generic and per-board data stays data.

    [LadderCheck.v] is not modified.  Axiom footprint: as [LadderCheck] --
    [functional_extensionality_dep], via [CTape.lift]. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr.
From BBB4.Checkers Require Import WrapTr LapDecider LadderKernel LadderFam LadderCheck LadderCheckTr TCyclerQHTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

Section BoardFTr.

Variable tm0   : TM.                (** the machine the theorem is about *)
Variable pins  : list Instr.        (** never fire (after the boot, on the
                                        quasihalting side) *)
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable F     : Fam.
Variable Aint  : nat -> nat -> LRule.
Variable N0i sti : nat.
Variable Afill : nat -> LRule.
Variable N0f stf : nat.
Variable fw1 fw2 : nat -> nat.
Variable fm1 fm2 : nat -> nat.
Variable visI  : nat -> Instr -> list lstep.  (** a chain to each unpinned
                                                  instruction, from each fill
                                                  arm's anchor *)
Variable ds0   : list nat.

Hypothesis HbF   : fm_b F = 2.
Hypothesis HcF   : fm_code F = Fib.
Hypothesis HsF   : fm_step F = 1.
Hypothesis Hfpre : Forall (fun d => d < 2) (f_pre (fam_fill F 0)).
Hypothesis Hfsuf : Forall (fun d => d < 2) (f_suf (fam_fill F 0)).
Hypothesis Hfmid : f_mid (fam_fill F 0) < 2.
Hypothesis Hfs   : length (f_pre (fam_fill F 0))
                   + length (f_suf (fam_fill F 0))
                   <= 1 + f_s (fam_fill F 0).
Hypothesis Hfto  : f_to (fam_fill F 0) = 0.
Hypothesis Hfmem : forall k, 0 < k -> fibokb false (filled F 0 k) = true.

Hypothesis Hbnd0 : Forall (fun d => d < 2) ds0.
Hypothesis Hlen0 : 0 < length ds0.
Hypothesis Hmem0 : fibokb false ds0 = true.

Hypothesis Hsti : 0 < sti.
Hypothesis HAiS : forall i r, i < 2 -> r < N0i + sti ->
  RuleSound tm (negb (fm_left F)) (fm_left F) (Aint i r).
Hypothesis HAiL : forall i r, i < 2 -> r < N0i + sti ->
  lr_lhs (Aint i r)
    = cls_conf F (cls_side F (cs_u (f1c i)) (cs_t (f1c i)) r
                    (astride N0i sti r) (cs_w (f1c i))).
Hypothesis HAiR : forall i r, i < 2 -> r < N0i + sti ->
  lr_rhs (Aint i r)
    = cls_conf F (cls_side F (cs_u' (f1c i)) (cs_t' (f1c i)) r
                    (astride N0i sti r) (cs_w' (f1c i))).
Hypothesis HAiC : forall i r, i < 2 -> r < N0i + sti -> 0 < lr_cb (Aint i r).

Hypothesis Hstf : 0 < stf.
Hypothesis HN0f : 1 <= N0f.
Hypothesis Hfw   : forall r, 1 <= r -> r < N0f + stf -> fw1 r + fw2 r = r.
Hypothesis Hfm12 : forall r, 1 <= r -> r < N0f + stf ->
  fm1 r + fm2 r
  + (length (f_pre (fam_fill F 0)) + length (f_suf (fam_fill F 0)))
  = r + f_s (fam_fill F 0).
Hypothesis HAfS : forall r, 1 <= r -> r < N0f + stf ->
  RuleSound tm true true (Afill r).
Hypothesis HAfL : forall r, 1 <= r -> r < N0f + stf ->
  lr_lhs (Afill r)
    = cls_conf F (run_side F 1 (fw1 r) (astride N0f stf r) (fw2 r) 0 [] []).
Hypothesis HAfR : forall r, 1 <= r -> r < N0f + stf ->
  lr_rhs (Afill r)
    = cls_conf F (run_side F (f_mid (fam_fill F 0)) (fm1 r)
                    (astride N0f stf r) (fm2 r) 0
                    (f_pre (fam_fill F 0)) (f_suf (fam_fill F 0))).
Hypothesis HAfC : forall r, 1 <= r -> r < N0f + stf -> 0 < lr_cb (Afill r).

(** every unpinned instruction fires from every fill arm's anchor *)
Hypothesis Hfire : forall r t, ~ In t pins -> 1 <= r -> r < N0f + stf ->
  srun_instr tm true true (visI r t) (lr_lhs (Afill r)) = Some t.

Local Notation Cf := (CfF F ds0).

(** one exact lap, anchor [n] to anchor [S n], on the wrapped machine *)
Lemma lapF : forall n, exists m, 0 < m /\ csteps tm m (Cf n) = Some (Cf (S n)).
Proof.
  intros n.
  destruct (iterF_total F HbF HcF HsF Hfpre Hfsuf Hfmid Hfs Hfto Hfmem n
              (ds0, 0, 0) (invF0 ds0 Hbnd0 Hlen0 Hmem0))
    as (s & Hit & Hi).
  destruct (board_lapF tm F Aint N0i sti Afill N0f stf fw1 fw2 fm1 fm2 ds0
              HbF HcF HsF Hfmid Hfs Hfto Hlen0 Hsti HAiS HAiL HAiR HAiC
              Hstf HN0f Hfw Hfm12 HAfS HAfL HAfR HAfC s Hi)
    as (s' & m & Hsucc & Hm & Hrun).
  exists m. split; [exact Hm|].
  unfold CfF. rewrite Hit.
  replace (S n) with (n + 1) by lia.
  rewrite fam_iter_add, Hit. simpl. rewrite Hsucc. exact Hrun.
Qed.

(** [LadderCheck.board_visitF], per instruction. *)
Lemma board_fireF : forall t N, ~ In t pins ->
  exists n k c, N <= n /\ csteps tm k (Cf n) = Some c /\ cinstr c = t.
Proof.
  intros t N Hnp.
  destruct (topsF_cof F HbF HcF HsF Hfpre Hfsuf Hfmid Hfs Hfto Hfmem
              (ds0, 0, 0) N (invF0 ds0 Hbnd0 Hlen0 Hmem0))
    as (n & s' & HN & Hit & Htop & Hi').
  exists n.
  destruct s' as [[ds' q'] ph']. simpl in Htop.
  destruct Hi' as (Hbnd' & Hk' & Hph' & Hok').
  assert (Hsh : ds' = repeat 1 (length ds'))
    by (apply (fib_top_shape F HcF HsF); assumption).
  remember (aoff N0f stf (length ds')) as r eqn:Er.
  assert (Hr1 : 1 <= r)
    by (subst r; pose proof (arm_index_pos N0f stf (length ds')
                               ltac:(lia) Hk'); lia).
  assert (Hrlt : r < N0f + stf) by (subst r; apply arm_index_lt; assumption).
  assert (Hidx : r + astride N0f stf r * acnt N0f stf (length ds') = length ds')
    by (subst r; apply arm_index; assumption).
  pose proof (Hfw r Hr1 Hrlt) as Hfwr.
  assert (Hden : Cf n
                 = cden [] [] (acnt N0f stf (length ds')) (lr_lhs (Afill r))).
  { unfold CfF. rewrite Hit, (HAfL r Hr1 Hrlt), Hph'.
    rewrite <- (cden_cls_conf F
                  (run_side F 1 (fw1 r) (astride N0f stf r) (fw2 r) 0 [] [])
                  [] (acnt N0f stf (length ds')) ds' q' 0).
    - unfold tailL, tailR; destruct (fm_left F); reflexivity.
    - rewrite Hsh at 1. apply cells_topF. lia. }
  destruct (fire_of_run_instr tm (fun _ => Cf n) true true (visI r t)
              (lr_lhs (Afill r)) 1%positive (acnt N0f stf (length ds'))
              [] [] t (Hfire r t Hnp Hr1 Hrlt)
              (fun _ => eq_refl) (fun _ => eq_refl) Hden) as (k & c & Hc & Ht).
  exists k, c. split; [exact HN | split; [exact Hc | exact Ht]].
Qed.

(** *** Never-quasihalting rows: the boot on the wrapped machine *)
Theorem boardF_neverqhtr : forall t0,
  csteps tm t0 CTape.c0 = Some (fam_cfg F (ds0, 0, 0)) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros t0 Hboot.
  apply (glue_neverqhtrN tm0 pins Cf).
  - exists t0. unfold CfF; simpl.
    rewrite <- lift_c0. apply csteps_lift. exact Hboot.
  - intros n. destruct (lapF n) as (m & Hm & Hrun).
    exists m, (Cf (S n)). split; [exact Hrun | split; [reflexivity | exact Hm]].
  - intros t Hnp N. exact (board_fireF t N Hnp).
Qed.

(** *** Quasihalting rows: the boot on the ORIGINAL machine, up to [lift] *)

(** the laps carry anchor [n] to every later anchor *)
Lemma reachF : forall d n, exists T, csteps tm T (Cf n) = Some (Cf (n + d)).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (T & HT).
    destruct (lapF (n + d)) as (m & _ & Hm).
    exists (T + m). rewrite csteps_add, HT.
    replace (n + S d) with (S (n + d)) by lia. exact Hm.
Qed.

Lemma fire_everyF : forall t, ~ In t pins -> forall n,
  exists k c, csteps tm k (Cf n) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp n.
  destruct (board_fireF t n Hnp) as (m & k & c & Hm & Hk & Hc).
  destruct (reachF (m - n) n) as (T & HT).
  replace (n + (m - n)) with m in HT by lia.
  exists (T + k), c. split; [|exact Hc].
  rewrite csteps_add, HT. exact Hk.
Qed.

Theorem boardF_qhtr : forall t0 B,
  stepn tm0 t0 InitES = Some (lift (fam_cfg F (ds0, 0, 0))) ->
  existsb (fun tg => cfires tm0 CTape.c0 t0 tg) pins = true ->
  (t0 <=? B) = true ->
  NonHalt tm0 /\ QHBoundTr B tm0 /\ QuasiHaltsTr tm0.
Proof.
  intros t0 B Hboot Hwit Hle.
  apply (lap_qh_stage tm0 pins (fun p => Cf (Nat.pred (Pos.to_nat p)))
           1%positive t0 B).
  - simpl. unfold CfF; simpl. exact Hboot.
  - intros p _.
    destruct (lapF (Nat.pred (Pos.to_nat p))) as (m & Hm & Hrun).
    exists m, (Cf (S (Nat.pred (Pos.to_nat p)))).
    split; [exact Hrun | split; [|exact Hm]].
    rewrite Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (fire_everyF t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End BoardFTr.
