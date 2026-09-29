(** * Checkers.LadderCheckQHTr: the value-family ladder on the QUASIHALTING
    side, at the INSTRUCTION level.

    [LadderCheckTr.boardph_neverqhtr] runs the whole board, boot included,
    on the machine wrapped at the instructions that never fire.  A
    quasihalting row fires its quiet instructions in a prefix, so the
    wrapped machine would halt there.  The port is the one
    [Counters/LapGlueQHTr] made of [LapGlueTr]:

    - the boot runs on the ORIGINAL machine, to a family member reached at
      index [t0] past the last fire of every pinned instruction;
    - the laps ([LadderCheck.board_lap], exact) and the per-instruction
      fires ([LadderCheckTr.board_fire], at the tops of the visit phase)
      run on the wrapped machine from that member;
    - a pinned instruction that fired in the prefix is the quasihalt
      witness.

    The anchors are re-indexed over [positive] ([Cfp p = CfB (p - 1)]) so
    that [QHConveyorTr.lap_qh_stage] closes the board unchanged.  Its fire
    premise wants a fire from EVERY anchor; [board_fire] gives one from
    anchors past every bound, and the exact laps carry any anchor to such
    a later one ([reachB]).

    Nothing in [LadderCheck.v] or [LadderCheckTr.v] changes.  Axiom
    footprint: as [LadderCheck] -- [functional_extensionality_dep], via
    [CTape.lift]. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr.
From BBB4.Checkers Require Import WrapTr LapDecider LadderKernel LadderFam LadderCheck LadderCheckTr TCyclerQHTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

Section BoardPhQHTr.

Variable tm0   : TM.                (** the machine the theorem is about *)
Variable pins  : list Instr.        (** quiet after the boot *)
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable F     : Fam.
Variable NPH   : nat.
Variable Aint  : nat -> nat -> LRule.
Variable N0i sti : nat.
Variable Afill : nat -> nat -> LRule.
Variable N0f stf : nat.
Variable fm1 fm2 : nat -> nat -> nat.
Variable pv    : nat.
Variable visI  : nat -> Instr -> list lstep.
Variable ds0   : list nat.
Variable ph0   : nat.
Variable t0    : nat.
Variable B     : nat.

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
Hypothesis Hpv   : pv < NPH.
Hypothesis Hcyc  : forall ph, ph < NPH -> exists k, phto F k ph = pv.
Hypothesis Hfm12 : forall r ph, 0 < r -> r < N0f + stf -> ph < NPH ->
  fm1 r ph + fm2 r ph
  + (length (f_pre (fam_fill F ph)) + length (f_suf (fam_fill F ph)))
  = r + f_s (fam_fill F ph).

Hypothesis Hbnd0 : Forall (fun d => d < fm_b F) ds0.
Hypothesis Hlen0 : 0 < length ds0.
Hypothesis Hph0  : ph0 < NPH.
(** the boot, on the ORIGINAL machine, up to [lift] (so the member may be
    one the run spells with blanks past either end) *)
Hypothesis Hboot : stepn tm0 t0 InitES = Some (lift (fam_cfg F (ds0, 0, ph0))).
(** some pinned instruction fired before the boot index *)
Hypothesis Hwit  : existsb (fun tg => cfires tm0 CTape.c0 t0 tg) pins = true.
Hypothesis Hle   : (t0 <=? B) = true.

Hypothesis Hsti : 0 < sti.
Hypothesis HAiS : forall d r, d < fm_b F - 1 -> r < N0i + sti ->
  RuleSound tm (negb (fm_left F)) (fm_left F) (Aint d r).
Hypothesis HAiL : forall d r, d < fm_b F - 1 -> r < N0i + sti ->
  lr_lhs (Aint d r)
    = cls_conf F (cls_side F [] (fm_b F - 1) r (astride N0i sti r) [d]).
Hypothesis HAiR : forall d r, d < fm_b F - 1 -> r < N0i + sti ->
  lr_rhs (Aint d r)
    = cls_conf F (cls_side F [] 0 r (astride N0i sti r) [S d]).
Hypothesis HAiC : forall d r, d < fm_b F - 1 -> r < N0i + sti ->
  0 < lr_cb (Aint d r).

Hypothesis Hstf : 0 < stf.
Hypothesis HN0f : 0 < N0f.
Hypothesis HAfS : forall r ph, 0 < r -> r < N0f + stf -> ph < NPH ->
  RuleSound tm true true (Afill r ph).
Hypothesis HAfL : forall r ph, 0 < r -> r < N0f + stf -> ph < NPH ->
  lr_lhs (Afill r ph)
    = cls_conf F (run_side F (fm_b F - 1) r (astride N0f stf r) 0 ph [] []).
Hypothesis HAfR : forall r ph, 0 < r -> r < N0f + stf -> ph < NPH ->
  lr_rhs (Afill r ph)
    = cls_conf F (run_side F (f_mid (fam_fill F ph)) (fm1 r ph)
                    (astride N0f stf r) (fm2 r ph) (f_to (fam_fill F ph))
                    (f_pre (fam_fill F ph)) (f_suf (fam_fill F ph))).
Hypothesis HAfC : forall r ph, 0 < r -> r < N0f + stf -> ph < NPH ->
  0 < lr_cb (Afill r ph).

Hypothesis Hfire : forall r t, ~ In t pins -> 0 < r -> r < N0f + stf ->
  srun_instr tm true true (visI r t) (lr_lhs (Afill r pv)) = Some t.

Local Notation Cf := (CfB F ds0 ph0).

(** one exact lap, anchor [n] to anchor [S n], on the wrapped machine *)
Lemma lapB : forall n, exists m, 0 < m /\ csteps tm m (Cf n) = Some (Cf (S n)).
Proof.
  intros n.
  destruct (iter_total F NPH Hb Hcode Hstep Hfpre Hfsuf Hfmid Hfs Hfto n
              (ds0, 0, ph0) (inv0 F NPH ds0 ph0 Hbnd0 Hlen0 Hph0))
    as (s & Hit & Hi).
  destruct (board_lap tm F NPH Aint N0i sti Afill N0f stf fm1 fm2 pv ds0 ph0
              Hb Hcode Hstep Hfs Hpv Hfm12 Hlen0 Hph0 Hsti HAiS HAiL HAiR HAiC
              Hstf HN0f HAfS HAfL HAfR HAfC s Hi)
    as (s' & m & Hsucc & Hm & Hrun).
  exists m. split; [exact Hm|].
  unfold CfB. rewrite Hit.
  replace (S n) with (n + 1) by lia.
  rewrite fam_iter_add, Hit. simpl. rewrite Hsucc. exact Hrun.
Qed.

(** the laps carry anchor [n] to every later anchor *)
Lemma reachB : forall d n, exists T, csteps tm T (Cf n) = Some (Cf (n + d)).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (T & HT).
    destruct (lapB (n + d)) as (m & _ & Hm).
    exists (T + m). rewrite csteps_add, HT.
    replace (n + S d) with (S (n + d)) by lia. exact Hm.
Qed.

(** every unpinned instruction fires from EVERY anchor *)
Lemma fire_everyB : forall t, ~ In t pins -> forall n,
  exists k c, csteps tm k (Cf n) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp n.
  destruct (board_fire tm0 pins F NPH Aint N0i sti Afill N0f stf pv
              visI ds0 ph0 Hb Hcode Hstep Hfpre Hfsuf Hfmid Hfs Hfto Hpv Hcyc
              Hbnd0 Hlen0 Hph0 HAiS Hstf HN0f HAfL Hfire t n Hnp)
    as (m & k & c & Hm & Hk & Hc).
  destruct (reachB (m - n) n) as (T & HT).
  replace (n + (m - n)) with m in HT by lia.
  exists (T + k), c. split; [|exact Hc].
  rewrite csteps_add, HT. exact Hk.
Qed.

Local Notation Cfp := (fun p : positive => Cf (Nat.pred (Pos.to_nat p))).

Theorem boardph_qhtr : NonHalt tm0 /\ QHBoundTr B tm0 /\ QuasiHaltsTr tm0.
Proof.
  apply (lap_qh_stage tm0 pins Cfp 1%positive t0 B).
  - (* boot, on the original machine *)
    simpl. unfold CfB; simpl. exact Hboot.
  - (* lap *)
    intros p _.
    destruct (lapB (Nat.pred (Pos.to_nat p))) as (m & Hm & Hrun).
    exists m, (Cf (S (Nat.pred (Pos.to_nat p)))).
    split; [exact Hrun | split; [|exact Hm]].
    rewrite Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - (* fires *)
    intros t Hnp p _. exact (fire_everyB t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End BoardPhQHTr.
