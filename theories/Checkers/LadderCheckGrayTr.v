(** * Checkers.LadderCheckGrayTr: the [(Gray, 2)] ladder at the INSTRUCTION
    level, on both sides.

    [LadderCheck] section 10 ([boardG_neverqh]) closes a counter whose digits
    read in the reflected binary code, stepping by 2 at a fixed parity [p].
    This is [LadderCheckFibTr] again for that section (SCOPING_INSTR
    7.4.CE2): the board runs on the machine wrapped at its pins, the
    per-state visit chains become per-instruction chains ([board_fireG] is
    [LadderCheck.board_visitG] with [fire_of_run_instr]), and the two
    closers are [LadderCheckTr.glue_neverqhtrN] (never-quasihalting rows)
    and [QHConveyorTr.lap_qh_stage] (quasihalting rows, the boot on the
    original machine up to [lift]).

    [LadderCheck.v] is not modified.  Axiom footprint: as [LadderCheck] --
    [functional_extensionality_dep], via [CTape.lift]. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr.
From BBB4.Checkers Require Import WrapTr LapDecider LadderKernel LadderFam LadderCheck LadderCheckTr TCyclerQHTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

Section BoardGTr.

Variable tm0   : TM.                (** the machine the theorem is about *)
Variable pins  : list Instr.        (** never fire (after the boot, on the
                                        quasihalting side) *)
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable F     : Fam.
Variable p     : nat.                  (** the family's parity *)
Variable Aint  : nat -> nat -> LRule.
Variable N0i sti : nat.
Variable Afill : nat -> LRule.
Variable N0f stf : nat.
Variable fw1 fw2 : nat -> nat.
Variable fm1 fm2 : nat -> nat.
Variable visI  : nat -> Instr -> list lstep.
Variable ds0   : list nat.

Hypothesis HbF   : fm_b F = 2.
Hypothesis HcF   : fm_code F = Gray.
Hypothesis HsF   : fm_step F = 2.
Hypothesis Hp    : p < 2.
Hypothesis Hfpre : Forall (fun d => d < 2) (f_pre (fam_fill F 0)).
Hypothesis Hfsuf : Forall (fun d => d < 2) (f_suf (fam_fill F 0)).
Hypothesis Hfmid : f_mid (fam_fill F 0) < 2.
Hypothesis Hfs   : length (f_pre (fam_fill F 0))
                   + length (f_suf (fam_fill F 0))
                   <= 2 + f_s (fam_fill F 0).
Hypothesis Hfto  : f_to (fam_fill F 0) = 0.
Hypothesis Hfpar : forall k, 2 <= k -> dsum (filled F 0 k) mod 2 = p.

Hypothesis Hbnd0 : Forall (fun d => d < 2) ds0.
Hypothesis Hlen0 : 2 <= length ds0.
Hypothesis Hpar0 : dsum ds0 mod 2 = p.

Hypothesis Hsti : 0 < sti.
Hypothesis HAiS : forall i r, i < 4 -> r < N0i + sti ->
  RuleSound tm (negb (fm_left F)) (fm_left F) (Aint i r).
Hypothesis HAiL : forall i r, i < 4 -> r < N0i + sti ->
  lr_lhs (Aint i r)
    = cls_conf F (cls_side F (cs_u (g2c p i)) (cs_t (g2c p i)) r
                    (astride N0i sti r) (cs_w (g2c p i))).
Hypothesis HAiR : forall i r, i < 4 -> r < N0i + sti ->
  lr_rhs (Aint i r)
    = cls_conf F (cls_side F (cs_u' (g2c p i)) (cs_t' (g2c p i)) r
                    (astride N0i sti r) (cs_w' (g2c p i))).
Hypothesis HAiC : forall i r, i < 4 -> r < N0i + sti -> 0 < lr_cb (Aint i r).

Hypothesis Hstf : 0 < stf.
Hypothesis HN0f : 2 <= N0f.
Hypothesis Hfw   : forall r, 2 <= r -> r < N0f + stf -> fw1 r + fw2 r + 2 = r.
Hypothesis Hfm12 : forall r, 2 <= r -> r < N0f + stf ->
  fm1 r + fm2 r
  + (length (f_pre (fam_fill F 0)) + length (f_suf (fam_fill F 0)))
  = r + f_s (fam_fill F 0).
Hypothesis HAfS : forall r, 2 <= r -> r < N0f + stf ->
  RuleSound tm true true (Afill r).
Hypothesis HAfL : forall r, 2 <= r -> r < N0f + stf ->
  lr_lhs (Afill r)
    = cls_conf F (run_side F 0 (fw1 r) (astride N0f stf r) (fw2 r) 0
                    [1 - p] [1]).
Hypothesis HAfR : forall r, 2 <= r -> r < N0f + stf ->
  lr_rhs (Afill r)
    = cls_conf F (run_side F (f_mid (fam_fill F 0)) (fm1 r)
                    (astride N0f stf r) (fm2 r) 0
                    (f_pre (fam_fill F 0)) (f_suf (fam_fill F 0))).
Hypothesis HAfC : forall r, 2 <= r -> r < N0f + stf -> 0 < lr_cb (Afill r).

(** every unpinned instruction fires from every fill arm's anchor *)
Hypothesis Hfire : forall r t, ~ In t pins -> 2 <= r -> r < N0f + stf ->
  srun_instr tm true true (visI r t) (lr_lhs (Afill r)) = Some t.

Local Notation Cf := (CfG F ds0).

(** one exact lap, anchor [n] to anchor [S n], on the wrapped machine *)
Lemma lapG : forall n, exists m, 0 < m /\ csteps tm m (Cf n) = Some (Cf (S n)).
Proof.
  intros n.
  destruct (iterG_total F p HbF HcF HsF Hp Hfpre Hfsuf Hfmid Hfs Hfto Hfpar n
              (ds0, 0, 0) (invG0 p ds0 Hbnd0 Hlen0 Hpar0))
    as (s & Hit & Hi).
  destruct (board_lapG tm F p Aint N0i sti Afill N0f stf fw1 fw2 fm1 fm2 ds0
              HbF HcF HsF Hp Hfmid Hfs Hfto Hlen0 Hpar0 Hsti HAiS HAiL HAiR HAiC
              Hstf HN0f Hfw Hfm12 HAfS HAfL HAfR HAfC s Hi)
    as (s' & m & Hsucc & Hm & Hrun).
  exists m. split; [exact Hm|].
  unfold CfG. rewrite Hit.
  replace (S n) with (n + 1) by lia.
  rewrite fam_iter_add, Hit. simpl. rewrite Hsucc. exact Hrun.
Qed.

(** [LadderCheck.board_visitG], per instruction. *)
Lemma board_fireG : forall t N, ~ In t pins ->
  exists n k c, N <= n /\ csteps tm k (Cf n) = Some c /\ cinstr c = t.
Proof.
  intros t N Hnp.
  destruct (topsG_cof F p HbF HcF HsF Hp Hfpre Hfsuf Hfmid Hfs Hfto Hfpar
              (ds0, 0, 0) N (invG0 p ds0 Hbnd0 Hlen0 Hpar0))
    as (n & s' & HN & Hit & Htop & Hi').
  exists n.
  destruct s' as [[ds' q'] ph']. simpl in Htop.
  destruct Hi' as (Hbnd' & Hk' & Hph' & Hpar').
  assert (Hsh : ds' = g2top p (length ds'))
    by (apply (gray_top_shape F HbF HcF HsF); assumption).
  remember (aoff N0f stf (length ds')) as r eqn:Er.
  assert (Hr2 : 2 <= r) by (subst r; apply arm_index_ge2; assumption).
  assert (Hrlt : r < N0f + stf) by (subst r; apply arm_index_lt; assumption).
  assert (Hidx : r + astride N0f stf r * acnt N0f stf (length ds') = length ds')
    by (subst r; apply arm_index; assumption).
  pose proof (Hfw r Hr2 Hrlt) as Hfwr.
  assert (Hden : Cf n
                 = cden [] [] (acnt N0f stf (length ds')) (lr_lhs (Afill r))).
  { unfold CfG. rewrite Hit, (HAfL r Hr2 Hrlt), Hph'.
    rewrite <- (cden_cls_conf F
                  (run_side F 0 (fw1 r) (astride N0f stf r) (fw2 r) 0
                     [1 - p] [1])
                  [] (acnt N0f stf (length ds')) ds' q' 0).
    - unfold tailL, tailR; destruct (fm_left F); reflexivity.
    - rewrite Hsh at 1.
      apply (cells_topG F p sti N0f stf ds0 HbF HsF Hp Hfmid Hfs Hfto Hlen0
               Hpar0 Hsti Hstf HN0f). lia. }
  destruct (fire_of_run_instr tm (fun _ => Cf n) true true (visI r t)
              (lr_lhs (Afill r)) 1%positive (acnt N0f stf (length ds'))
              [] [] t (Hfire r t Hnp Hr2 Hrlt)
              (fun _ => eq_refl) (fun _ => eq_refl) Hden) as (k & c & Hc & Ht).
  exists k, c. split; [exact HN | split; [exact Hc | exact Ht]].
Qed.

(** *** Never-quasihalting rows: the boot on the wrapped machine *)
Theorem boardG_neverqhtr : forall t0,
  csteps tm t0 CTape.c0 = Some (fam_cfg F (ds0, 0, 0)) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros t0 Hboot.
  apply (glue_neverqhtrN tm0 pins Cf).
  - exists t0. unfold CfG; simpl.
    rewrite <- lift_c0. apply csteps_lift. exact Hboot.
  - intros n. destruct (lapG n) as (m & Hm & Hrun).
    exists m, (Cf (S n)). split; [exact Hrun | split; [reflexivity | exact Hm]].
  - intros t Hnp N. exact (board_fireG t N Hnp).
Qed.

(** *** Quasihalting rows: the boot on the ORIGINAL machine, up to [lift] *)

(** the laps carry anchor [n] to every later anchor *)
Lemma reachG : forall d n, exists T, csteps tm T (Cf n) = Some (Cf (n + d)).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (T & HT).
    destruct (lapG (n + d)) as (m & _ & Hm).
    exists (T + m). rewrite csteps_add, HT.
    replace (n + S d) with (S (n + d)) by lia. exact Hm.
Qed.

Lemma fire_everyG : forall t, ~ In t pins -> forall n,
  exists k c, csteps tm k (Cf n) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp n.
  destruct (board_fireG t n Hnp) as (m & k & c & Hm & Hk & Hc).
  destruct (reachG (m - n) n) as (T & HT).
  replace (n + (m - n)) with m in HT by lia.
  exists (T + k), c. split; [|exact Hc].
  rewrite csteps_add, HT. exact Hk.
Qed.

Theorem boardG_qhtr : forall t0 B,
  stepn tm0 t0 InitES = Some (lift (fam_cfg F (ds0, 0, 0))) ->
  existsb (fun tg => cfires tm0 CTape.c0 t0 tg) pins = true ->
  (t0 <=? B) = true ->
  NonHalt tm0 /\ QHBoundTr B tm0 /\ QuasiHaltsTr tm0.
Proof.
  intros t0 B Hboot Hwit Hle.
  apply (lap_qh_stage tm0 pins (fun pp => Cf (Nat.pred (Pos.to_nat pp)))
           1%positive t0 B).
  - simpl. unfold CfG; simpl. exact Hboot.
  - intros pp _.
    destruct (lapG (Nat.pred (Pos.to_nat pp))) as (m & Hm & Hrun).
    exists m, (Cf (S (Nat.pred (Pos.to_nat pp)))).
    split; [exact Hrun | split; [|exact Hm]].
    rewrite Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat pp))) with (Pos.to_nat pp)
      by (pose proof (Pos2Nat.is_pos pp); lia).
    reflexivity.
  - intros t Hnp pp _. exact (fire_everyG t Hnp (Nat.pred (Pos.to_nat pp))).
  - exact Hwit.
  - exact Hle.
Qed.

End BoardGTr.
