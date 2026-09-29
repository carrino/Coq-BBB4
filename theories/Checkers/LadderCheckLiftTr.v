(** * Checkers.LadderCheckLiftTr: the value-family ladder at the INSTRUCTION
    level, with fill arms that close up to [lift].

    [LadderCheck]'s board states every arm EXACTLY: the fill arm must land on
    [cls_conf] of the family's target, cell for cell.  A counter whose top
    digit ends in a blank the machine never writes cannot do that.  The base-4
    counters of SCOPING_INSTR 7.4.CE2 are the case in point: digits
    [000/110/001/111], the fill [111^k -> 000^k 110], and the machine writes
    [000^k 11] and turns back, one blank short of the target.  The run is
    right; only the list spelling differs, and [lift] cannot see the
    difference.

    So the fill arms here are the machine's own exact runs ([RuleSound], to a
    right-hand side the kernel replays), and each board states how many
    trailing blanks separate that right-hand side from the family's target
    ([cpad]).  [lift_cpad] says the two lift alike.  The laps then hold up to
    [lift], which is all both closers ask for:

    - never-quasihalting rows: [LadderCheckTr.glue_neverqhtrN], whose lap
      premise is up to [lift] already ([boardphL_neverqhtr]);
    - quasihalting rows: [QHConveyorTr.lap_qh_stage], as in
      [LadderCheckQHTr], with the fire from every anchor carried through
      [stepn] on lifted configurations and pulled back to [csteps] by
      [LapCertGlueLift.stepn_csteps_at] ([boardphL_qhtr]).

    [LadderCheck.board_arm] is generic over the property its arms carry, so
    it is used unchanged, over a VIRTUAL fill arm whose right-hand side is
    the family's target.  Nothing in [LadderCheck.v] changes.  Axiom
    footprint: [functional_extensionality_dep], via [CTape.lift]. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr.
From BBB4.Counters Require Import WTape LapCertGlueLift.
From BBB4.Checkers Require Import WrapTr LapDecider LadderKernel LadderFam LadderCheck LadderCheckTr TCyclerQHTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

(** ** Trailing blanks *)

Definition spad (k : nat) (s : sside) : sside :=
  mkS (s_pre s) (s_u s) (s_a s) (s_b s) (s_post s ++ repeat S0 k).

Definition cpad (kl kr : nat) (c : sconf) : sconf :=
  mkC (c_st c) (spad kl (c_l c)) (c_h c) (spad kr (c_r c)).

Lemma lift_side_app_blanks : forall k r,
  lift_side (r ++ repeat S0 k) = lift_side r.
Proof.
  induction k; intros r; simpl.
  - rewrite app_nil_r. reflexivity.
  - replace (r ++ S0 :: repeat S0 k) with ((r ++ [S0]) ++ repeat S0 k)
      by (rewrite <- app_assoc; reflexivity).
    rewrite IHk. apply lift_side_app_blank.
Qed.

Lemma lift_cpad : forall kl kr j c,
  lift (cden [] [] j (cpad kl kr c)) = lift (cden [] [] j c).
Proof.
  intros kl kr j [q l h r].
  unfold cden, cpad, spad, sden, lift, lift_tape; simpl.
  rewrite !app_nil_r, !app_assoc, !lift_side_app_blanks. reflexivity.
Qed.

(** ** The board *)

Section BoardPhLTr.

Variable tm0   : TM.
Variable pins  : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable F     : Fam.
Variable NPH   : nat.
Variable Aint  : nat -> nat -> LRule.
Variable N0i sti : nat.
Variable Afill : nat -> nat -> LRule.   (** the machine's own fill runs *)
Variable N0f stf : nat.
Variable fm1 fm2 : nat -> nat -> nat.
Variable padl padr : nat -> nat -> nat. (** the blanks each fill run is short *)
Variable pv    : nat.
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
Hypothesis Hpv   : pv < NPH.
Hypothesis Hcyc  : forall ph, ph < NPH -> exists k, phto F k ph = pv.
Hypothesis Hfm12 : forall r ph, 0 < r -> r < N0f + stf -> ph < NPH ->
  fm1 r ph + fm2 r ph
  + (length (f_pre (fam_fill F ph)) + length (f_suf (fam_fill F ph)))
  = r + f_s (fam_fill F ph).

Hypothesis Hbnd0 : Forall (fun d => d < fm_b F) ds0.
Hypothesis Hlen0 : 0 < length ds0.
Hypothesis Hph0  : ph0 < NPH.

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
(** the family's target is the fill run's right-hand side plus blanks *)
Hypothesis HAfR : forall r ph, 0 < r -> r < N0f + stf -> ph < NPH ->
  cls_conf F (run_side F (f_mid (fam_fill F ph)) (fm1 r ph)
                (astride N0f stf r) (fm2 r ph) (f_to (fam_fill F ph))
                (f_pre (fam_fill F ph)) (f_suf (fam_fill F ph)))
    = cpad (padl r ph) (padr r ph) (lr_rhs (Afill r ph)).
Hypothesis HAfC : forall r ph, 0 < r -> r < N0f + stf -> ph < NPH ->
  0 < lr_cb (Afill r ph).

Hypothesis Hfire : forall r t, ~ In t pins -> 0 < r -> r < N0f + stf ->
  srun_instr tm true true (visI r t) (lr_lhs (Afill r pv)) = Some t.

(** the fill arm [board_arm] sees: the same run, stated to the target *)
Definition Vfill (r ph : nat) : LRule :=
  mkLRule (lr_lhs (Afill r ph))
          (cls_conf F (run_side F (f_mid (fam_fill F ph)) (fm1 r ph)
                         (astride N0f stf r) (fm2 r ph) (f_to (fam_fill F ph))
                         (f_pre (fam_fill F ph)) (f_suf (fam_fill F ph))))
          (lr_ca (Afill r ph)) (lr_cb (Afill r ph)).

(** what every arm carries: an exact run to a configuration that lifts to
    the right-hand side's *)
Definition RuleLift (el er : bool) (A : LRule) : Prop :=
  forall XL XR j, (el = true -> XL = []) -> (er = true -> XR = []) ->
  exists c, csteps tm (lr_ca A * j + lr_cb A) (cden XL XR j (lr_lhs A)) = Some c
            /\ lift c = lift (cden XL XR j (lr_rhs A)).

Local Notation Cf := (CfB F ds0 ph0).

Lemma lapL : forall n, exists m c,
  0 < m /\ csteps tm m (Cf n) = Some c /\ lift c = lift (Cf (S n)).
Proof.
  intros n.
  destruct (iter_total F NPH Hb Hcode Hstep Hfpre Hfsuf Hfmid Hfs Hfto n
              (ds0, 0, ph0) (inv0 F NPH ds0 ph0 Hbnd0 Hlen0 Hph0))
    as (s & Hit & Hi).
  assert (HVL : forall r ph, 0 < r -> r < N0f + stf -> ph < NPH ->
    lr_lhs (Vfill r ph)
      = cls_conf F (run_side F (fm_b F - 1) r (astride N0f stf r) 0 ph [] []))
    by (intros; unfold Vfill; simpl; auto).
  assert (HVR : forall r ph, 0 < r -> r < N0f + stf -> ph < NPH ->
    lr_rhs (Vfill r ph)
      = cls_conf F (run_side F (f_mid (fam_fill F ph)) (fm1 r ph)
                      (astride N0f stf r) (fm2 r ph) (f_to (fam_fill F ph))
                      (f_pre (fam_fill F ph)) (f_suf (fam_fill F ph))))
    by (intros; reflexivity).
  assert (HVC : forall r ph, 0 < r -> r < N0f + stf -> ph < NPH ->
    0 < lr_cb (Vfill r ph)) by (intros; unfold Vfill; simpl; auto).
  assert (HPi : forall d r, d < fm_b F - 1 -> r < N0i + sti ->
    RuleLift (negb (fm_left F)) (fm_left F) (Aint d r)).
  { intros d r Hd Hr XL XR j HL HR.
    exists (cden XL XR j (lr_rhs (Aint d r))).
    split; [exact (HAiS d r Hd Hr XL XR j HL HR) | reflexivity]. }
  assert (HPf : forall r ph, 0 < r -> r < N0f + stf -> ph < NPH ->
    RuleLift true true (Vfill r ph)).
  { intros r ph H0 Hr Hph XL XR j HL HR.
    rewrite (HL eq_refl), (HR eq_refl).
    exists (cden [] [] j (lr_rhs (Afill r ph))).
    split.
    - unfold Vfill; simpl. exact (HAfS r ph H0 Hr Hph [] [] j (fun _ => eq_refl) (fun _ => eq_refl)).
    - unfold Vfill; simpl. rewrite (HAfR r ph H0 Hr Hph).
      symmetry. apply lift_cpad. }
  destruct (board_arm tm F NPH Aint N0i sti Vfill N0f stf fm1 fm2 pv ds0 ph0
              Hb Hcode Hstep Hfs Hpv Hfm12 Hlen0 Hph0 Hsti HAiS HAiL HAiR HAiC
              Hstf HN0f HVL HVR HVC RuleLift HPi HPf s Hi)
    as (s' & A & el & er & X & k & Hsucc & HA & HL & HR & Hl & Hr & Hcb).
  destruct (HA _ _ k HL HR) as (c & Hc & Hlc).
  exists (lr_ca A * k + lr_cb A), c.
  split; [lia|]. split.
  - unfold CfB. rewrite Hit, Hl. exact Hc.
  - rewrite Hlc, <- Hr. unfold CfB.
    replace (S n) with (n + 1) by lia.
    rewrite fam_iter_add, Hit. simpl. rewrite Hsucc. reflexivity.
Qed.

Lemma board_fireL : forall t N, ~ In t pins ->
  exists n k c, N <= n /\ csteps tm k (Cf n) = Some c /\ cinstr c = t.
Proof.
  intros t N Hnp.
  exact (board_fire tm0 pins F NPH Aint N0i sti Afill N0f stf pv visI ds0 ph0
           Hb Hcode Hstep Hfpre Hfsuf Hfmid Hfs Hfto Hpv Hcyc Hbnd0 Hlen0 Hph0
           HAiS Hstf HN0f HAfL Hfire t N Hnp).
Qed.

(** *** Never-quasihalting rows: the boot on the wrapped machine, up to
    [lift] (the boot member may end in the same unwritten blanks) *)
Theorem boardphL_neverqhtr : forall t0,
  stepn tm t0 InitES = Some (lift (fam_cfg F (ds0, 0, ph0))) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros t0 Hboot.
  apply (glue_neverqhtrN tm0 pins Cf).
  - exists t0. unfold CfB; simpl. exact Hboot.
  - intros n. destruct (lapL n) as (m & c & Hm & Hrun & Hl).
    exists m, c. split; [exact Hrun | split; [exact Hl | exact Hm]].
  - intros t Hnp N. exact (board_fireL t N Hnp).
Qed.

(** *** Quasihalting rows: the boot on the ORIGINAL machine, up to [lift] *)

Lemma reachL : forall d n,
  exists T, stepn tm T (lift (Cf n)) = Some (lift (Cf (n + d))).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (T & HT).
    destruct (lapL (n + d)) as (m & c & _ & Hm & Hl).
    exists (T + m). rewrite stepn_add, HT.
    replace (n + S d) with (S (n + d)) by lia.
    rewrite <- Hl. apply csteps_lift. exact Hm.
Qed.

Lemma fire_everyL : forall t, ~ In t pins -> forall n,
  exists k c, csteps tm k (Cf n) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp n.
  destruct (board_fireL t n Hnp) as (m & k & c & Hm & Hk & Hc).
  destruct (reachL (m - n) n) as (T & HT).
  replace (n + (m - n)) with m in HT by lia.
  assert (Hs : stepn tm (T + k) (lift (Cf n)) = Some (lift c)).
  { rewrite stepn_add, HT. apply csteps_lift. exact Hk. }
  destruct (stepn_csteps_at tm (T + k) (Cf n) (lift c) Hs) as (c' & Hc' & Hl').
  exists (T + k), c'. split; [exact Hc'|].
  rewrite <- cinstr_lift, Hl', cinstr_lift. exact Hc.
Qed.

Theorem boardphL_qhtr : forall t0 B,
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
    destruct (lapL (Nat.pred (Pos.to_nat p))) as (m & c & Hm & Hrun & Hl).
    exists m, c. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (fire_everyL t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End BoardPhLTr.
