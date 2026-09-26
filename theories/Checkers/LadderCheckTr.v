(** * Checkers.LadderCheckTr: the value-family ladder at the INSTRUCTION level.

    [LadderCheck.boardph_neverqh] closes a binary value-family counter to
    [NeverQuasiHaltsSt] from a boot, two classes of arms (the interior digits
    and the fill at the top of a width) and one visit chain per STATE out of
    the fill arm's anchor.  The transition-level obligation
    ([NeverQuasiHaltsTr]: every instruction that ever fires fires unboundedly
    often) is what the closeout's class SP needs: there the rare instruction
    is the counter's OVERFLOW, which fires once per width -- exactly the fill
    arm, whose anchors [tops_cofinal_at] already proves cofinal.

    The port is the one [Counters/LapGlueTr] made of [LapGlue], and it needs
    nothing new from the ladder:

    - the whole board runs on the WRAPPED machine [tm_wrap_trs tm pins]
      (pins: the instructions the certificate claims never fire).  Laps
      chaining forever on it prove that it never halts, so by
      [WrapTr.wrap_trs_agree] its run IS [tm]'s run and no pin fires
      ([glue_neverqhtrN], [LadderCheck.glue_neverqhN] with that one change);
    - the per-state visit chains become per-INSTRUCTION chains: a prefix of
      the fill arm ending on a configuration whose (state, head symbol) is
      the instruction ([LapGlueTr.srun_instr], [fire_of_run_instr]).
      [board_fire] is [LadderCheck.board_visit] with that substitution.

    [LadderCheck.v] is not modified (it is in the state census's closure);
    every lemma used here is one it exports.  Axiom footprint: as
    [LadderCheck] -- [functional_extensionality_dep], via [CTape.lift]. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlueQuiet.
From BBB4.Checkers Require Import WrapTr LapDecider LadderKernel LadderFam LadderCheck.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
Import ListNotations.

(** ** 1. The glue: nat-indexed anchors, instruction fires cofinal *)

Section GlueNTr.

Variable tm : TM.
Variable pins : list Instr.       (** claimed never to fire *)
Variable Cf : nat -> cconf.

Hypothesis Hboot : exists t0,
  stepn (tm_wrap_trs tm pins) t0 InitES = Some (lift (Cf 0)).
Hypothesis Hlap : forall n, exists m c',
  csteps (tm_wrap_trs tm pins) m (Cf n) = Some c'
  /\ lift c' = lift (Cf (S n)) /\ 0 < m.
(** every unpinned instruction fires from anchors past every bound *)
Hypothesis Hfire : forall t, ~ In t pins -> forall N, exists n k c,
  N <= n /\ csteps (tm_wrap_trs tm pins) k (Cf n) = Some c /\ cinstr c = t.

Lemma wrapped_nonhaltN : forall n, stepn (tm_wrap_trs tm pins) n InitES <> None.
Proof.
  intro n.
  destruct (glue_reachN (tm_wrap_trs tm pins) Cf Hboot Hlap n)
    as (T & HT & Hstep).
  destruct (stepn_prefix (tm_wrap_trs tm pins) n T InitES _ HT Hstep)
    as (cm & Hcm & _).
  rewrite Hcm. discriminate.
Qed.

Theorem glue_neverqhtrN : NeverQuasiHaltsTr tm.
Proof.
  intros t (n & c & Hc & Ht) N.
  pose proof (wrap_trs_agree tm pins InitES wrapped_nonhaltN) as Hagree.
  assert (Hnp : ~ In t pins).
  { destruct (Hagree n) as [_ Hnot]. rewrite <- Ht. exact (Hnot c Hc). }
  destruct (Hfire t Hnp N) as (m & k & ck & Hm & Hk & Hck).
  destruct (glue_reachN (tm_wrap_trs tm pins) Cf Hboot Hlap m)
    as (T & HT & Hstep).
  exists (T + k). split; [lia|].
  exists (lift ck). split.
  - destruct (Hagree (T + k)) as [Heq _]. rewrite <- Heq.
    rewrite stepn_add, Hstep. apply csteps_lift; exact Hk.
  - rewrite cinstr_lift. exact Hck.
Qed.

End GlueNTr.

(** ** 2. The board: [LadderCheck.BoardPh] on the wrapped machine

    The hypotheses are [BoardPh]'s, verbatim, with [tm] the wrapped machine
    and the per-state [Hvisit] replaced by the per-instruction [Hfire]. *)

Section BoardPhTr.

Variable tm0   : TM.                (** the machine the theorem is about *)
Variable pins  : list Instr.        (** the instructions it never fires *)
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable F     : Fam.
Variable NPH   : nat.
Variable Aint  : nat -> nat -> LRule.
Variable N0i sti : nat.
Variable Afill : nat -> nat -> LRule.
Variable N0f stf : nat.
Variable fm1 fm2 : nat -> nat -> nat.
Variable pv    : nat.
Variable visI  : nat -> Instr -> list lstep.  (** a chain to each unpinned
                                                  instruction, from each fill
                                                  arm's anchor in phase [pv] *)
Variable ds0   : list nat.
Variable ph0   : nat.
Variable t0    : nat.

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
Hypothesis Hboot : csteps tm t0 CTape.c0 = Some (fam_cfg F (ds0, 0, ph0)).

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

(** *** Liveness: every unpinned instruction fires from every fill arm's
    anchor in phase [pv] -- the fill arm is the overflow, so this is where
    the rare instruction is witnessed *)
Hypothesis Hfire : forall r t, ~ In t pins -> 0 < r -> r < N0f + stf ->
  srun_instr tm true true (visI r t) (lr_lhs (Afill r pv)) = Some t.

(** [LadderCheck.board_visit], per instruction. *)
Lemma board_fire : forall t N, ~ In t pins ->
  exists n k c, N <= n /\ csteps tm k (CfB F ds0 ph0 n) = Some c
                /\ cinstr c = t.
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
  assert (Hden : CfB F ds0 ph0 n
                 = cden [] [] (acnt N0f stf (length ds')) (lr_lhs (Afill r pv))).
  { unfold CfB. rewrite Hit, (HAfL r pv Hr0 Hrlt Hpv).
    rewrite <- (cden_cls_conf F
                  (run_side F (fm_b F - 1) r (astride N0f stf r) 0 pv [] [])
                  [] (acnt N0f stf (length ds')) ds' p' pv).
    - unfold tailL, tailR; destruct (fm_left F); reflexivity.
    - rewrite Hsh at 1. apply cells_top. exact Hk. }
  destruct (fire_of_run_instr tm (fun _ => CfB F ds0 ph0 n) true true (visI r t)
              (lr_lhs (Afill r pv)) 1%positive (acnt N0f stf (length ds'))
              [] [] t (Hfire r t Hnp Hr0 Hrlt)
              (fun _ => eq_refl) (fun _ => eq_refl) Hden) as (k & c & Hc & Ht).
  exists k, c. split; [exact HN | split; [exact Hc | exact Ht]].
Qed.

Theorem boardph_neverqhtr : NeverQuasiHaltsTr tm0.
Proof.
  apply (glue_neverqhtrN tm0 pins (CfB F ds0 ph0)).
  - (* boot, on the wrapped machine *)
    exists t0. unfold CfB; simpl.
    rewrite <- lift_c0. apply csteps_lift. exact Hboot.
  - (* lap *)
    intros n.
    destruct (iter_total F NPH Hb Hcode Hstep Hfpre Hfsuf Hfmid Hfs Hfto n
                (ds0, 0, ph0) (inv0 F NPH ds0 ph0 Hbnd0 Hlen0 Hph0))
      as (s & Hit & Hi).
    destruct (board_lap tm F NPH Aint N0i sti Afill N0f stf fm1 fm2 pv ds0 ph0
                Hb Hcode Hstep Hfs Hpv Hfm12 Hlen0 Hph0 Hsti HAiS HAiL HAiR HAiC
                Hstf HN0f HAfS HAfL HAfR HAfC s Hi)
      as (s' & m & Hsucc & Hm & Hrun).
    exists m, (fam_cfg F s'). unfold CfB. rewrite Hit.
    split; [exact Hrun | split; [|exact Hm]].
    replace (S n) with (n + 1) by lia.
    rewrite fam_iter_add, Hit. simpl. rewrite Hsucc. reflexivity.
  - (* fires: at every top of phase [pv], and those tops are cofinal *)
    intros t Hnp N. exact (board_fire t N Hnp).
Qed.

End BoardPhTr.
