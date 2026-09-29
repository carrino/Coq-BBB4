(** * Checkers.LadderCheckNestTr: the value-family ladder at the INSTRUCTION
    level, with arms that are chains of chains.

    [LadderCheckTr] and [LadderCheckQHTr] close a binary value-family counter
    from arms that are [LadderKernel] rules, each with a step count affine in
    its run.  A counter whose carry walks back to the anchor once per digit
    costs time QUADRATIC in the carry, and its interior arm is no such rule
    (SCOPING_INSTR 7.4.CE2).  [LadderNest] proves those arms as segment
    programs, to [ReachL]: a positive run to a configuration that LIFTS to
    the right-hand side's.  This file is the board over such arms.

    Nothing about the family, the case split or the liveness changes:

    - [board_armN] is [LadderCheck.board_arm] restated without the
      [RuleSound] premise that section carries along (its conclusion is
      already generic over the arm property, and so is its proof);
    - the lap is up to [lift], which is all both glues ask for
      ([LadderCheckTr.glue_neverqhtrN], [QHConveyorTr.lap_qh_stage]),
      exactly as in [LadderCheckLiftTr];
    - the fires are [LadderCheckTr.board_fire]'s argument, restated for the
      same reason as [board_armN].

    A plain kernel arm is a one-segment program ([LadderNest.NCh]), and
    [ReachL] also absorbs blanks a fill run leaves unwritten, so a board may
    state every arm this way.  Axiom footprint: [functional_extensionality_dep],
    via [CTape.lift]. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr.
From BBB4.Counters Require Import WTape LapCertGlueLift.
From BBB4.Checkers Require Import WrapTr LapDecider LadderKernel LadderFam LadderCheck LadderCheckTr LadderNest TCyclerQHTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

(** ** Fires past an iteration

    A fill arm whose run is a chain of chains may fire an instruction only
    after its rounds: the machine's last sweep runs after the carry.  A visit
    is then a segment program to some configuration, and a base chain from
    there to the instruction. *)

Definition nfire (tm : TM) (el er : bool) (rs : list LRule) (sg : list nseg)
    (l : list lstep) (c : sconf) : option Instr :=
  match nrun tm el er rs sg c with
  | Some (c1, _) => srun_instr tm el er l c1
  | None => None
  end.

Lemma nfire_sound : forall tm el er rs sg l c t,
  Forall (RuleSound tm false false) rs ->
  nfire tm el er rs sg l c = Some t ->
  forall XL XR j, (el = true -> XL = []) -> (er = true -> XR = []) ->
  exists k c', csteps tm k (cden XL XR j c) = Some c' /\ cinstr c' = t.
Proof.
  intros tm el er rs sg l c t HF H XL XR j HL HR. unfold nfire in H.
  destruct (nrun tm el er rs sg c) as [[c1 p]|] eqn:E; [|discriminate].
  destruct (nrun_sound tm el er rs sg c c1 p HF E XL XR j HL HR) as (m & _ & Hm).
  destruct (fire_of_run_instr tm (fun _ => cden XL XR j c1) el er l c1
              1%positive j XL XR t H HL HR eq_refl) as (k & c' & Hk & Ht).
  exists (m + k), c'. split; [|exact Ht].
  rewrite csteps_add, Hm. exact Hk.
Qed.

Section BoardNTr.

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
Variable pv    : nat.
Variable rsv   : list LRule.                  (** the inner rules *)
Variable vsegs : nat -> Instr -> list nseg.    (** each visit's program *)
Variable visI  : nat -> Instr -> list lstep.   (** and its closing chain *)
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

(** *** The arms: [ReachL], no step count *)
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
  nfire tm true true rsv (vsegs r t) (visI r t) (lr_lhs (Afill r pv)) = Some t.

(** [LadderCheck.board_arm], verbatim but for the premises it does not use. *)
Lemma board_armN : forall (P : bool -> bool -> LRule -> Prop),
  (forall d r, d < fm_b F - 1 -> r < N0i + sti ->
     P (negb (fm_left F)) (fm_left F) (Aint d r)) ->
  (forall r ph, 0 < r -> r < N0f + stf -> ph < NPH -> P true true (Afill r ph)) ->
  forall s, Inv F NPH s ->
  exists s' A el er X n,
    fam_succ F s = Some s'
    /\ P el er A
    /\ (el = true -> tailL F X = []) /\ (er = true -> tailR F X = [])
    /\ fam_cfg F s  = cden (tailL F X) (tailR F X) n (lr_lhs A)
    /\ fam_cfg F s' = cden (tailL F X) (tailR F X) n (lr_rhs A).
Proof.
  intros P HPi HPf [[ds p] ph] Hi. destruct Hi as (Hbnd & Hlen & Hph).
  destruct (digs_decomp (fm_b F - 1) ds) as [Htop | (n & d & rest & -> & Hd)].
  - remember (aoff N0f stf (length ds)) as r eqn:Er.
    assert (Hr0 : 0 < r) by (subst r; apply arm_index_pos; assumption).
    assert (Hrlt : r < N0f + stf) by (subst r; apply arm_index_lt; assumption).
    assert (Hk : r + astride N0f stf r * acnt N0f stf (length ds) = length ds)
      by (subst r; apply arm_index; assumption).
    assert (Hist : fam_is_top F ds = true).
    { rewrite Htop at 1. apply pos1_is_top; assumption. }
    exists (filled F ph (length ds), p, f_to (fam_fill F ph)), (Afill r ph).
    exists true, true, [].
    exists (acnt N0f stf (length ds)).
    split; [|split; [|split; [|split; [|split]]]].
    + unfold fam_succ.
      rewrite (fill_top F NPH Hb Hcode Hstep Hfs ds ph Hph Hlen Hist), Hist.
      reflexivity.
    + exact (HPf r ph Hr0 Hrlt Hph).
    + intros _; apply tailL_nil.
    + intros _; apply tailR_nil.
    + rewrite (HAfL r ph Hr0 Hrlt Hph). symmetry.
      apply cden_cls_conf. rewrite Htop at 1. apply cells_top. exact Hk.
    + rewrite (HAfR r ph Hr0 Hrlt Hph). symmetry.
      apply cden_cls_conf. apply cells_filled.
      pose proof (Hfm12 r ph Hr0 Hrlt Hph). lia.
  - apply Forall_app in Hbnd as [Hrun Hrest'].
    inversion Hrest' as [|? ? Hdb Hrest]; subst.
    assert (Hdlt : d < fm_b F - 1) by lia.
    remember (aoff N0i sti n) as r eqn:Er.
    assert (Hrlt : r < N0i + sti) by (subst r; apply arm_index_lt; assumption).
    assert (Hn : r + astride N0i sti r * acnt N0i sti n = n)
      by (subst r; apply arm_index; assumption).
    exists (repeat 0 n ++ S d :: rest, p, ph), (Aint d r).
    exists (negb (fm_left F)), (fm_left F), (cls_tail F rest ph).
    exists (acnt N0i sti n).
    split; [|split; [|split; [|split; [|split]]]].
    + assert (Hns : fam_next F (repeat (fm_b F - 1) n ++ d :: rest) ph
                    = Some (repeat 0 n ++ S d :: rest))
        by exact (pos1_class_succ F d Hb Hcode Hstep Hdlt n rest ph Hrest I).
      unfold fam_succ. rewrite Hns.
      rewrite (pos1_class_not_top F d n rest Hb Hcode Hstep Hdlt Hrest).
      reflexivity.
    + exact (HPi d r Hdlt Hrlt).
    + intros He. unfold tailL. destruct (fm_left F); [discriminate|reflexivity].
    + intros He. unfold tailR. rewrite He. reflexivity.
    + rewrite (HAiL d r Hdlt Hrlt). symmetry. apply cden_cls_conf.
      rewrite <- Hn at 1.
      apply (fam_cells_class F [] (fm_b F - 1) r (astride N0i sti r)
               (acnt N0i sti n) [d] rest ph).
    + rewrite (HAiR d r Hdlt Hrlt). symmetry. apply cden_cls_conf.
      rewrite <- Hn at 1.
      apply (fam_cells_class F [] 0 r (astride N0i sti r)
               (acnt N0i sti n) [S d] rest ph).
Qed.

Local Notation Cf := (CfB F ds0 ph0).

Definition ArmL (el er : bool) (A : LRule) : Prop :=
  ReachL tm el er (lr_lhs A) (lr_rhs A).

Lemma lapN : forall n, exists m c,
  0 < m /\ csteps tm m (Cf n) = Some c /\ lift c = lift (Cf (S n)).
Proof.
  intros n.
  destruct (iter_total F NPH Hb Hcode Hstep Hfpre Hfsuf Hfmid Hfs Hfto n
              (ds0, 0, ph0) (inv0 F NPH ds0 ph0 Hbnd0 Hlen0 Hph0))
    as (s & Hit & Hi).
  destruct (board_armN ArmL HAiS HAfS s Hi)
    as (s' & A & el & er & X & k & Hsucc & HA & HL & HR & Hl & Hr).
  destruct (HA _ _ k HL HR) as (m & c & Hm & Hc & Hlc).
  exists m, c. split; [exact Hm|]. split.
  - unfold CfB. rewrite Hit, Hl. exact Hc.
  - rewrite Hlc, <- Hr. unfold CfB.
    replace (S n) with (n + 1) by lia.
    rewrite fam_iter_add, Hit. simpl. rewrite Hsucc. reflexivity.
Qed.

(** [LadderCheckTr.board_fire], verbatim but for the premises it does not
    use. *)
Lemma board_fireN : forall t N, ~ In t pins ->
  exists n k c, N <= n /\ csteps tm k (Cf n) = Some c /\ cinstr c = t.
Proof.
  intros t N Hnp.
  destruct (tops_cof_pv F NPH pv Hb Hcode Hstep Hfpre Hfsuf Hfmid Hfs Hfto
              Hcyc (ds0, 0, ph0) N (inv0 F NPH ds0 ph0 Hbnd0 Hlen0 Hph0))
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
                 = cden [] [] (acnt N0f stf (length ds')) (lr_lhs (Afill r pv))).
  { unfold CfB. rewrite Hit, (HAfL r pv Hr0 Hrlt Hpv).
    rewrite <- (cden_cls_conf F
                  (run_side F (fm_b F - 1) r (astride N0f stf r) 0 pv [] [])
                  [] (acnt N0f stf (length ds')) ds' p' pv).
    - unfold tailL, tailR; destruct (fm_left F); reflexivity.
    - rewrite Hsh at 1. apply cells_top. exact Hk. }
  destruct (nfire_sound tm true true rsv (vsegs r t) (visI r t)
              (lr_lhs (Afill r pv)) t Hrsv (Hfire r t Hnp Hr0 Hrlt)
              [] [] (acnt N0f stf (length ds'))
              (fun _ => eq_refl) (fun _ => eq_refl)) as (k & c & Hc & Ht).
  exists k, c. rewrite Hden. split; [exact HN | split; [exact Hc | exact Ht]].
Qed.

(** *** Never-quasihalting rows: the boot on the wrapped machine, up to
    [lift] *)
Theorem boardN_neverqhtr : forall t0,
  stepn tm t0 InitES = Some (lift (fam_cfg F (ds0, 0, ph0))) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros t0 Hboot.
  apply (glue_neverqhtrN tm0 pins Cf).
  - exists t0. unfold CfB; simpl. exact Hboot.
  - intros n. destruct (lapN n) as (m & c & Hm & Hrun & Hl).
    exists m, c. split; [exact Hrun | split; [exact Hl | exact Hm]].
  - intros t Hnp N. exact (board_fireN t N Hnp).
Qed.

(** *** Quasihalting rows: the boot on the ORIGINAL machine, up to [lift] *)

Lemma reachN : forall d n,
  exists T, stepn tm T (lift (Cf n)) = Some (lift (Cf (n + d))).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (T & HT).
    destruct (lapN (n + d)) as (m & c & _ & Hm & Hl).
    exists (T + m). rewrite stepn_add, HT.
    replace (n + S d) with (S (n + d)) by lia.
    rewrite <- Hl. apply csteps_lift. exact Hm.
Qed.

Lemma fire_everyN : forall t, ~ In t pins -> forall n,
  exists k c, csteps tm k (Cf n) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp n.
  destruct (board_fireN t n Hnp) as (m & k & c & Hm & Hk & Hc).
  destruct (reachN (m - n) n) as (T & HT).
  replace (n + (m - n)) with m in HT by lia.
  assert (Hs : stepn tm (T + k) (lift (Cf n)) = Some (lift c)).
  { rewrite stepn_add, HT. apply csteps_lift. exact Hk. }
  destruct (stepn_csteps_at tm (T + k) (Cf n) (lift c) Hs) as (c' & Hc' & Hl').
  exists (T + k), c'. split; [exact Hc'|].
  rewrite <- cinstr_lift, Hl', cinstr_lift. exact Hc.
Qed.

Theorem boardN_qhtr : forall t0 B,
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
    destruct (lapN (Nat.pred (Pos.to_nat p))) as (m & c & Hm & Hrun & Hl).
    exists m, c. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (fire_everyN t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End BoardNTr.

(** ** The board with a digit of LOOKAHEAD

    Some carries read one digit past the one they increment (the machine
    turns back on the NEXT digit's first cell), so the class
    [t^n ++ d :: rest] with [rest] opaque has no arm.  Splitting [rest] once
    more serves them: [t^n ++ d :: e :: rest'] with [e] concrete and [rest']
    opaque, and [t^n ++ [d]] -- the carry into the LAST digit, which sees the
    terminator and so has both tails known empty and one arm per phase.  The
    successor is [pos1_class_succ]'s at either shape; the fill class and the
    fires are unchanged ([board_fireN] is reused as it stands). *)

Section BoardKTr.

Variable tm0   : TM.
Variable pins  : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable F     : Fam.
Variable NPH   : nat.
Variable AintK : nat -> nat -> nat -> LRule.   (** digit, next digit, index *)
Variable AendK : nat -> nat -> nat -> LRule.   (** digit, index, phase *)
Variable N0i sti : nat.
Variable Afill : nat -> nat -> LRule.
Variable N0f stf : nat.
Variable fm1 fm2 : nat -> nat -> nat.
Variable pv    : nat.
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
Hypothesis HKS : forall d e r, d < fm_b F - 1 -> e < fm_b F -> r < N0i + sti ->
  ReachL tm (negb (fm_left F)) (fm_left F)
    (lr_lhs (AintK d e r)) (lr_rhs (AintK d e r)).
Hypothesis HKL : forall d e r, d < fm_b F - 1 -> e < fm_b F -> r < N0i + sti ->
  lr_lhs (AintK d e r)
    = cls_conf F (cls_side F [] (fm_b F - 1) r (astride N0i sti r) [d; e]).
Hypothesis HKR : forall d e r, d < fm_b F - 1 -> e < fm_b F -> r < N0i + sti ->
  lr_rhs (AintK d e r)
    = cls_conf F (cls_side F [] 0 r (astride N0i sti r) [S d; e]).
Hypothesis HES : forall d r ph, d < fm_b F - 1 -> r < N0i + sti -> ph < NPH ->
  ReachL tm true true (lr_lhs (AendK d r ph)) (lr_rhs (AendK d r ph)).
Hypothesis HEL : forall d r ph, d < fm_b F - 1 -> r < N0i + sti -> ph < NPH ->
  lr_lhs (AendK d r ph)
    = cls_conf F (run_side F (fm_b F - 1) r (astride N0i sti r) 0 ph [] [d]).
Hypothesis HER : forall d r ph, d < fm_b F - 1 -> r < N0i + sti -> ph < NPH ->
  lr_rhs (AendK d r ph)
    = cls_conf F (run_side F 0 r (astride N0i sti r) 0 ph [] [S d]).

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
  nfire tm true true rsv (vsegs r t) (visI r t) (lr_lhs (Afill r pv)) = Some t.

Local Notation Cf := (CfB F ds0 ph0).

Lemma board_armK : forall s, Inv F NPH s ->
  exists s' A el er X n,
    fam_succ F s = Some s'
    /\ ReachL tm el er (lr_lhs A) (lr_rhs A)
    /\ (el = true -> tailL F X = []) /\ (er = true -> tailR F X = [])
    /\ fam_cfg F s  = cden (tailL F X) (tailR F X) n (lr_lhs A)
    /\ fam_cfg F s' = cden (tailL F X) (tailR F X) n (lr_rhs A).
Proof.
  intros [[ds p] ph] Hi. pose proof Hi as Hi0. destruct Hi as (Hbnd & Hlen & Hph).
  destruct (digs_decomp (fm_b F - 1) ds) as [Htop | (n & d & rest & -> & Hd)].
  - (* the top: the fill arm, exactly as [board_armN] *)
    remember (aoff N0f stf (length ds)) as r eqn:Er.
    assert (Hr0 : 0 < r) by (subst r; apply arm_index_pos; assumption).
    assert (Hrlt : r < N0f + stf) by (subst r; apply arm_index_lt; assumption).
    assert (Hk : r + astride N0f stf r * acnt N0f stf (length ds) = length ds)
      by (subst r; apply arm_index; assumption).
    assert (Hist : fam_is_top F ds = true).
    { rewrite Htop at 1. apply pos1_is_top; assumption. }
    exists (filled F ph (length ds), p, f_to (fam_fill F ph)), (Afill r ph).
    exists true, true, [].
    exists (acnt N0f stf (length ds)).
    split; [|split; [|split; [|split; [|split]]]].
    + unfold fam_succ.
      rewrite (fill_top F NPH Hb Hcode Hstep Hfs ds ph Hph Hlen Hist), Hist.
      reflexivity.
    + exact (HAfS r ph Hr0 Hrlt Hph).
    + intros _; apply tailL_nil.
    + intros _; apply tailR_nil.
    + rewrite (HAfL r ph Hr0 Hrlt Hph). symmetry.
      apply cden_cls_conf. rewrite Htop at 1. apply cells_top. exact Hk.
    + rewrite (HAfR r ph Hr0 Hrlt Hph). symmetry.
      apply cden_cls_conf. apply cells_filled.
      pose proof (Hfm12 r ph Hr0 Hrlt Hph). lia.
  - apply Forall_app in Hbnd as [Hrun Hrest'].
    inversion Hrest' as [|? ? Hdb Hrest]; subst.
    assert (Hdlt : d < fm_b F - 1) by lia.
    remember (aoff N0i sti n) as r eqn:Er.
    assert (Hrlt : r < N0i + sti) by (subst r; apply arm_index_lt; assumption).
    assert (Hn : r + astride N0i sti r * acnt N0i sti n = n)
      by (subst r; apply arm_index; assumption).
    assert (Hns : fam_succ F (repeat (fm_b F - 1) n ++ d :: rest, p, ph)
                  = Some (repeat 0 n ++ S d :: rest, p, ph)).
    { assert (Hnx : fam_next F (repeat (fm_b F - 1) n ++ d :: rest) ph
                    = Some (repeat 0 n ++ S d :: rest))
        by exact (pos1_class_succ F d Hb Hcode Hstep Hdlt n rest ph Hrest I).
      unfold fam_succ. rewrite Hnx.
      rewrite (pos1_class_not_top F d n rest Hb Hcode Hstep Hdlt Hrest).
      reflexivity. }
    destruct rest as [|e rest].
    + (* the LAST digit: the end arm, both tails known empty *)
      exists (repeat 0 n ++ [S d], p, ph), (AendK d r ph).
      exists true, true, [].
      exists (acnt N0i sti n).
      split; [|split; [|split; [|split; [|split]]]].
      * exact Hns.
      * exact (HES d r ph Hdlt Hrlt Hph).
      * intros _; apply tailL_nil.
      * intros _; apply tailR_nil.
      * rewrite (HEL d r ph Hdlt Hrlt Hph). symmetry. apply cden_cls_conf.
        rewrite <- (fam_cells_run F (fm_b F - 1) r (astride N0i sti r)
                      (acnt N0i sti n) 0 ph [] [d]).
        f_equal. rewrite Nat.add_0_r, Hn. reflexivity.
      * rewrite (HER d r ph Hdlt Hrlt Hph). symmetry. apply cden_cls_conf.
        rewrite <- (fam_cells_run F 0 r (astride N0i sti r)
                      (acnt N0i sti n) 0 ph [] [S d]).
        f_equal. rewrite Nat.add_0_r, Hn. reflexivity.
    + (* a digit follows: the lookahead arm, [rest] opaque *)
      apply Forall_cons_iff in Hrest as [Heb Hrest2].
      exists (repeat 0 n ++ S d :: e :: rest, p, ph), (AintK d e r).
      exists (negb (fm_left F)), (fm_left F), (cls_tail F rest ph).
      exists (acnt N0i sti n).
      split; [|split; [|split; [|split; [|split]]]].
      * exact Hns.
      * exact (HKS d e r Hdlt Heb Hrlt).
      * intros He. unfold tailL. destruct (fm_left F); [discriminate|reflexivity].
      * intros He. unfold tailR. rewrite He. reflexivity.
      * rewrite (HKL d e r Hdlt Heb Hrlt). symmetry. apply cden_cls_conf.
        rewrite <- Hn at 1.
        exact (fam_cells_class F [] (fm_b F - 1) r (astride N0i sti r)
                 (acnt N0i sti n) [d; e] rest ph).
      * rewrite (HKR d e r Hdlt Heb Hrlt). symmetry. apply cden_cls_conf.
        rewrite <- Hn at 1.
        exact (fam_cells_class F [] 0 r (astride N0i sti r)
                 (acnt N0i sti n) [S d; e] rest ph).
Qed.

Lemma lapK : forall n, exists m c,
  0 < m /\ csteps tm m (Cf n) = Some c /\ lift c = lift (Cf (S n)).
Proof.
  intros n.
  destruct (iter_total F NPH Hb Hcode Hstep Hfpre Hfsuf Hfmid Hfs Hfto n
              (ds0, 0, ph0) (inv0 F NPH ds0 ph0 Hbnd0 Hlen0 Hph0))
    as (s & Hit & Hi).
  destruct (board_armK s Hi)
    as (s' & A & el & er & X & k & Hsucc & HA & HL & HR & Hl & Hr).
  destruct (HA _ _ k HL HR) as (m & c & Hm & Hc & Hlc).
  exists m, c. split; [exact Hm|]. split.
  - unfold CfB. rewrite Hit, Hl. exact Hc.
  - rewrite Hlc, <- Hr. unfold CfB.
    replace (S n) with (n + 1) by lia.
    rewrite fam_iter_add, Hit. simpl. rewrite Hsucc. reflexivity.
Qed.

Lemma fire_K : forall t N, ~ In t pins ->
  exists n k c, N <= n /\ csteps tm k (Cf n) = Some c /\ cinstr c = t.
Proof.
  intros t N Hnp.
  destruct (tops_cof_pv F NPH pv Hb Hcode Hstep Hfpre Hfsuf Hfmid Hfs Hfto
              Hcyc (ds0, 0, ph0) N (inv0 F NPH ds0 ph0 Hbnd0 Hlen0 Hph0))
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
                 = cden [] [] (acnt N0f stf (length ds')) (lr_lhs (Afill r pv))).
  { unfold CfB. rewrite Hit, (HAfL r pv Hr0 Hrlt Hpv).
    rewrite <- (cden_cls_conf F
                  (run_side F (fm_b F - 1) r (astride N0f stf r) 0 pv [] [])
                  [] (acnt N0f stf (length ds')) ds' p' pv).
    - unfold tailL, tailR; destruct (fm_left F); reflexivity.
    - rewrite Hsh at 1. apply cells_top. exact Hk. }
  destruct (nfire_sound tm true true rsv (vsegs r t) (visI r t)
              (lr_lhs (Afill r pv)) t Hrsv (Hfire r t Hnp Hr0 Hrlt)
              [] [] (acnt N0f stf (length ds'))
              (fun _ => eq_refl) (fun _ => eq_refl)) as (k & c & Hc & Ht).
  exists k, c. rewrite Hden. split; [exact HN | split; [exact Hc | exact Ht]].
Qed.

Theorem boardK_neverqhtr : forall t0,
  stepn tm t0 InitES = Some (lift (fam_cfg F (ds0, 0, ph0))) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros t0 Hboot.
  apply (glue_neverqhtrN tm0 pins Cf).
  - exists t0. unfold CfB; simpl. exact Hboot.
  - intros n. destruct (lapK n) as (m & c & Hm & Hrun & Hl).
    exists m, c. split; [exact Hrun | split; [exact Hl | exact Hm]].
  - intros t Hnp N. exact (fire_K t N Hnp).
Qed.

Lemma reachK : forall d n,
  exists T, stepn tm T (lift (Cf n)) = Some (lift (Cf (n + d))).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (T & HT).
    destruct (lapK (n + d)) as (m & c & _ & Hm & Hl).
    exists (T + m). rewrite stepn_add, HT.
    replace (n + S d) with (S (n + d)) by lia.
    rewrite <- Hl. apply csteps_lift. exact Hm.
Qed.

Lemma fire_everyK : forall t, ~ In t pins -> forall n,
  exists k c, csteps tm k (Cf n) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp n.
  destruct (fire_K t n Hnp) as (m & k & c & Hm & Hk & Hc).
  destruct (reachK (m - n) n) as (T & HT).
  replace (n + (m - n)) with m in HT by lia.
  assert (Hs : stepn tm (T + k) (lift (Cf n)) = Some (lift c)).
  { rewrite stepn_add, HT. apply csteps_lift. exact Hk. }
  destruct (stepn_csteps_at tm (T + k) (Cf n) (lift c) Hs) as (c' & Hc' & Hl').
  exists (T + k), c'. split; [exact Hc'|].
  rewrite <- cinstr_lift, Hl', cinstr_lift. exact Hc.
Qed.

Theorem boardK_qhtr : forall t0 B,
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
    destruct (lapK (Nat.pred (Pos.to_nat p))) as (m & c & Hm & Hrun & Hl).
    exists m, c. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (fire_everyK t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End BoardKTr.
