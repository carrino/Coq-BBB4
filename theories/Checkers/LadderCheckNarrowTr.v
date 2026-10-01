(** * Checkers.LadderCheckNarrowTr: the value-family ladder with fill laws
    that may NARROW the counter (SCOPING_INSTR 7.4.LE3).

    [LadderFam.Fill] states the widening [f_s : nat], so a multi-phase
    counter whose cycle runs (for example) [+2, -1] -- a net gain, but one
    fill lands on a NARROWER width -- has no [Fam].  LE2 re-read the narrowing
    fills whose landing terminator starts on a digit-word boundary
    ([emit_ladder.respell]: the top digit moves into the digit string).
    The rest have a terminator that does not ([0RB1LA_1RC0LA_0LD1RB_1LB0RC]
    lands [(10)^k 01] on [(11)^(k-1) 0101]), and no re-reading makes every
    widening a [nat].

    This file states them directly.  The family is a [Fam] as before, read
    in [(Binary, 1)], plus a NARROWING per phase [nar ph]: the fill of a
    width-[k] top lands on width [k + f_s - nar ph].  The successor
    [nsucc] is [fam_succ] with that one change (inside a width it IS
    [fam_next], so [LadderCheck]'s class laws [pos1_class_succ] and
    [pos1_is_top] are used as they stand).  What a narrowing costs is a
    floor: a width may not narrow below the fill's own target words, so the
    board carries a MINIMUM WIDTH per phase [minw] with

      [0 < minw ph],  [nar ph + |pre| + |suf| <= minw ph + f_s],
      [nar ph + minw (f_to ph) <= minw ph + f_s],

    all closed by [vm_compute]; every reachable width is then at least its
    phase's floor ([InvN]), and the fill arms are needed only from the floor
    up.  Liveness is [LadderCheck] section 5's argument (tops recur in every
    phase the cycle returns to), restated over [nsucc]: it never needed the
    fill to widen.  The arms are [LadderNest.ReachL] programs and the fires
    [LadderCheckNestTr.nfire]s; both closers are given ([boardNw_neverqhtr]
    on the wrapped machine, [boardNw_qhtr] past the pins' last fire).

    Nothing landed is modified.  Axiom footprint: [functional_extensionality_dep],
    via [CTape.lift]. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr.
From BBB4.Counters Require Import WTape LapCertGlueLift.
From BBB4.Checkers Require Import WrapTr LapDecider LadderKernel LadderFam LadderCheck LadderCheckTr LadderNest LadderCheckNestTr TCyclerQHTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

(** ** 1. The successor with a narrowing per phase *)

Definition nfilled (F : Fam) (nar : nat -> nat) (ph k : nat) : list nat :=
  f_pre (fam_fill F ph)
  ++ repeat (f_mid (fam_fill F ph))
       (k + f_s (fam_fill F ph) - nar ph
        - (length (f_pre (fam_fill F ph)) + length (f_suf (fam_fill F ph))))
  ++ f_suf (fam_fill F ph).

Definition nsucc (F : Fam) (nar : nat -> nat) (s : CtrSt) : option CtrSt :=
  let '(ds, p, ph) := s in
  if fam_is_top F ds
  then Some (nfilled F nar ph (length ds), p, f_to (fam_fill F ph))
  else match fam_next F ds ph with
       | None => None
       | Some nd => Some (nd, p, ph)
       end.

Fixpoint niter (F : Fam) (nar : nat -> nat) (s : CtrSt) (k : nat) : option CtrSt :=
  match k with
  | O => Some s
  | S k' => match nsucc F nar s with
            | None => None
            | Some s' => niter F nar s' k'
            end
  end.

Lemma niter_add : forall F nar k1 k2 s,
  niter F nar s (k1 + k2) =
  match niter F nar s k1 with
  | None => None
  | Some s1 => niter F nar s1 k2
  end.
Proof.
  intros F nar. induction k1 as [|k1 IH]; intros k2 s; simpl; [reflexivity|].
  destruct (nsucc F nar s) as [s'|]; [apply IH | reflexivity].
Qed.

Definition CfN (F : Fam) (nar : nat -> nat) (ds0 : list nat) (ph0 n : nat)
  : cconf :=
  match niter F nar (ds0, 0, ph0) n with
  | Some s => fam_cfg F s
  | None => CTape.c0
  end.

(** ** 2. Tops recur, in every phase the cycle returns to *)

Section IterN.

Variable F : Fam.
Variable NPH : nat.
Variable nar minw : nat -> nat.
Hypothesis Hb    : 1 < fm_b F.
Hypothesis Hcode : fm_code F = Binary.
Hypothesis Hstep : fm_step F = 1.
Hypothesis Hfpre : forall ph, ph < NPH ->
  Forall (fun d => d < fm_b F) (f_pre (fam_fill F ph)).
Hypothesis Hfsuf : forall ph, ph < NPH ->
  Forall (fun d => d < fm_b F) (f_suf (fam_fill F ph)).
Hypothesis Hfmid : forall ph, ph < NPH -> f_mid (fam_fill F ph) < fm_b F.
Hypothesis Hfto  : forall ph, ph < NPH -> f_to (fam_fill F ph) < NPH.
Hypothesis Hmin  : forall ph, ph < NPH ->
  0 < minw ph
  /\ nar ph + (length (f_pre (fam_fill F ph)) + length (f_suf (fam_fill F ph)))
     <= minw ph + f_s (fam_fill F ph)
  /\ nar ph + minw (f_to (fam_fill F ph)) <= minw ph + f_s (fam_fill F ph).

Definition InvN (s : CtrSt) : Prop :=
  let '(ds, _, ph) := s in
  Forall (fun d => d < fm_b F) ds /\ minw ph <= length ds /\ ph < NPH.

Lemma invN_len : forall ds p ph, InvN (ds, p, ph) -> 0 < length ds.
Proof.
  intros ds p ph (_ & Hl & Hph). pose proof (Hmin ph Hph). lia.
Qed.

Lemma invN_value_lt : forall s,
  InvN s -> fam_value F (ct_ds s) < Nat.pow (fm_b F) (length (ct_ds s)).
Proof.
  intros [[ds p] ph] (Hbnd & _ & _); simpl.
  unfold fam_value. rewrite Hcode. apply val_pos_lt; [lia | exact Hbnd].
Qed.

Lemma nfilled_length : forall ph k, ph < NPH -> minw ph <= k ->
  length (nfilled F nar ph k) = k + f_s (fam_fill F ph) - nar ph.
Proof.
  intros ph k Hph Hk. unfold nfilled. pose proof (Hmin ph Hph).
  rewrite !app_length, repeat_length. lia.
Qed.

Lemma nfilled_bnd : forall ph k, ph < NPH ->
  Forall (fun d => d < fm_b F) (nfilled F nar ph k).
Proof.
  intros ph k Hph. unfold nfilled. apply Forall_app.
  split; [apply (Hfpre ph Hph)|].
  apply Forall_app. split; [|apply (Hfsuf ph Hph)].
  apply Forall_forall. intros x Hx. apply repeat_spec in Hx.
  pose proof (Hfmid ph Hph). lia.
Qed.

Lemma nsucc_totalN : forall s,
  InvN s -> exists s', nsucc F nar s = Some s' /\ InvN s'.
Proof.
  intros [[ds p] ph] Hi. pose proof (invN_len _ _ _ Hi) as Hlen.
  destruct Hi as (Hbnd & Hmw & Hph).
  destruct (fam_is_top F ds) eqn:Htop.
  - eexists. unfold nsucc. rewrite Htop. split; [reflexivity|].
    simpl. repeat split.
    + apply nfilled_bnd; exact Hph.
    + rewrite nfilled_length by assumption. pose proof (Hmin ph Hph). lia.
    + apply Hfto; exact Hph.
  - assert (Hlt : fam_value F ds + fm_step F < Nat.pow (fm_b F) (length ds)).
    { unfold fam_is_top in Htop. rewrite (fam_lim_bin F _ Hcode) in Htop.
      apply Nat.ltb_ge in Htop.
      pose proof (pow_pos (fm_b F) (length ds) ltac:(lia)). lia. }
    destruct (fam_next F ds ph) as [nd|] eqn:Hnd.
    2:{ exfalso. unfold fam_next in Hnd. rewrite Htop in Hnd.
        unfold fam_of_value in Hnd.
        rewrite (fam_lim_bin F _ Hcode), (fam_lo_bin F _ Hcode) in Hnd.
        cbn [Nat.leb andb] in Hnd.
        destruct (Nat.ltb_spec (fam_value F ds + fm_step F)
                    (Nat.pow (fm_b F) (length ds))); [discriminate | lia]. }
    exists (nd, p, ph). unfold nsucc. rewrite Htop, Hnd.
    split; [reflexivity|].
    destruct (fam_next_interior F ds ph nd Hb Htop Hnd) as (_ & Hlen').
    assert (Hbnd' : Forall (fun d => d < fm_b F) nd).
    { unfold fam_next in Hnd. rewrite Htop in Hnd. unfold fam_of_value in Hnd.
      destruct ((fam_lo F (length ds) <=? fam_value F ds + fm_step F)
                && (fam_value F ds + fm_step F <? fam_lim F (length ds)));
        [|discriminate].
      rewrite Hcode in Hnd. injection Hnd as <-. apply pos_of_lt; lia. }
    unfold InvN. repeat split; [exact Hbnd' | rewrite Hlen'; exact Hmw | exact Hph].
Qed.

Lemma niter_totalN : forall N s,
  InvN s -> exists s', niter F nar s N = Some s' /\ InvN s'.
Proof.
  induction N as [|N IH]; intros s Hi; [exists s; split; [reflexivity|exact Hi]|].
  destruct (nsucc_totalN s Hi) as (s1 & H1 & Hi1).
  destruct (IH s1 Hi1) as (s' & H' & Hi').
  exists s'. split; [|exact Hi']. simpl. rewrite H1. exact H'.
Qed.

Lemma top_reachedN_aux : forall m s,
  InvN s ->
  Nat.pow (fm_b F) (length (ct_ds s)) - fam_value F (ct_ds s) <= m ->
  exists n s', niter F nar s n = Some s' /\ fam_is_top F (ct_ds s') = true
               /\ InvN s' /\ ct_ph s' = ct_ph s.
Proof.
  induction m as [|m IH]; intros s Hi Hm.
  - exfalso. pose proof (invN_value_lt s Hi). lia.
  - destruct (fam_is_top F (ct_ds s)) eqn:Htop.
    + exists 0, s.
      split; [reflexivity | split; [exact Htop | split; [exact Hi|reflexivity]]].
    + destruct s as [[ds p] ph]. simpl in Htop.
      destruct (nsucc_totalN _ Hi) as (s1 & H1 & Hi1).
      unfold nsucc in H1. rewrite Htop in H1.
      destruct (fam_next F ds ph) as [nd|] eqn:Hnd; [|discriminate].
      injection H1 as <-.
      destruct (fam_next_interior F ds ph nd Hb Htop Hnd) as (Hval & Hlen').
      destruct (IH (nd, p, ph) Hi1) as (n & s' & Hit & Htop' & Hi' & Hph').
      { simpl. simpl in Hm. rewrite Hval, Hlen', Hstep. lia. }
      exists (S n), s'.
      split; [|split; [exact Htop' | split; [exact Hi' | exact Hph']]].
      simpl. unfold nsucc. rewrite Htop, Hnd. exact Hit.
Qed.

Lemma top_reachedN : forall s,
  InvN s ->
  exists n s', niter F nar s n = Some s' /\ fam_is_top F (ct_ds s') = true
               /\ InvN s' /\ ct_ph s' = ct_ph s.
Proof.
  intros s Hi.
  apply (top_reachedN_aux
           (Nat.pow (fm_b F) (length (ct_ds s)) - fam_value F (ct_ds s)) s Hi).
  lia.
Qed.

Lemma top_afterN : forall k s, InvN s ->
  exists n s', niter F nar s n = Some s' /\ fam_is_top F (ct_ds s') = true
               /\ InvN s' /\ ct_ph s' = phto F k (ct_ph s).
Proof.
  induction k as [|k IH]; intros s Hi.
  - destruct (top_reachedN s Hi) as (n & s' & Hit & Htop & Hi' & Hph).
    exists n, s'.
    split; [exact Hit | split; [exact Htop | split; [exact Hi' | exact Hph]]].
  - destruct (top_reachedN s Hi) as (n & s1 & Hit & Htop & Hi1 & Hph).
    destruct (nsucc_totalN s1 Hi1) as (s2 & Hs2 & Hi2).
    assert (Hph2 : ct_ph s2 = f_to (fam_fill F (ct_ph s1))).
    { destruct s1 as [[ds1 p1] ph1]. simpl in Htop |- *.
      unfold nsucc in Hs2. rewrite Htop in Hs2.
      injection Hs2 as <-. reflexivity. }
    destruct (IH s2 Hi2) as (m & s' & Hit2 & Htop' & Hi' & Hph').
    exists (n + (1 + m)), s'.
    split; [| split; [exact Htop' | split; [exact Hi' |]]].
    + rewrite niter_add, Hit. simpl. rewrite Hs2. exact Hit2.
    + rewrite Hph', Hph2, Hph. reflexivity.
Qed.

Theorem tops_cofinal_atN : forall pv s N,
  (forall ph, ph < NPH -> exists k, phto F k ph = pv) ->
  InvN s ->
  exists n s', N <= n /\ niter F nar s n = Some s'
               /\ fam_is_top F (ct_ds s') = true /\ InvN s'
               /\ ct_ph s' = pv.
Proof.
  intros pv s N Hcyc Hi.
  destruct (niter_totalN N s Hi) as (sN & HN & HiN).
  assert (HphN : ct_ph sN < NPH)
    by (destruct sN as [[? ?] ?]; destruct HiN as (_ & _ & H); exact H).
  destruct (Hcyc (ct_ph sN) HphN) as (k & Hk).
  destruct (top_afterN k sN HiN) as (m & s' & Hm & Htop & Hi' & Hph).
  exists (N + m), s'.
  split; [lia | split; [| split; [exact Htop | split; [exact Hi' |]]]].
  - rewrite niter_add, HN. exact Hm.
  - rewrite Hph. exact Hk.
Qed.

End IterN.

(** ** 3. The board *)

Section BoardNwTr.

Variable tm0   : TM.
Variable pins  : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable F     : Fam.
Variable NPH   : nat.
Variable nar minw : nat -> nat.
Variable Aint  : nat -> nat -> LRule.
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
Hypothesis Hfto  : forall ph, ph < NPH -> f_to (fam_fill F ph) < NPH.
Hypothesis Hmin  : forall ph, ph < NPH ->
  0 < minw ph
  /\ nar ph + (length (f_pre (fam_fill F ph)) + length (f_suf (fam_fill F ph)))
     <= minw ph + f_s (fam_fill F ph)
  /\ nar ph + minw (f_to (fam_fill F ph)) <= minw ph + f_s (fam_fill F ph).
Hypothesis HN0f  : forall ph, ph < NPH -> minw ph <= N0f.
Hypothesis Hpv   : pv < NPH.
Hypothesis Hcyc  : forall ph, ph < NPH -> exists k, phto F k ph = pv.
Hypothesis Hfm12 : forall r ph, minw ph <= r -> r < N0f + stf -> ph < NPH ->
  fm1 r ph + fm2 r ph + nar ph
  + (length (f_pre (fam_fill F ph)) + length (f_suf (fam_fill F ph)))
  = r + f_s (fam_fill F ph).

Hypothesis Hbnd0 : Forall (fun d => d < fm_b F) ds0.
Hypothesis Hlen0 : minw ph0 <= length ds0.
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
Hypothesis HAfS : forall r ph, minw ph <= r -> r < N0f + stf -> ph < NPH ->
  ReachL tm true true (lr_lhs (Afill r ph)) (lr_rhs (Afill r ph)).
Hypothesis HAfL : forall r ph, minw ph <= r -> r < N0f + stf -> ph < NPH ->
  lr_lhs (Afill r ph)
    = cls_conf F (run_side F (fm_b F - 1) r (astride N0f stf r) 0 ph [] []).
Hypothesis HAfR : forall r ph, minw ph <= r -> r < N0f + stf -> ph < NPH ->
  lr_rhs (Afill r ph)
    = cls_conf F (run_side F (f_mid (fam_fill F ph)) (fm1 r ph)
                    (astride N0f stf r) (fm2 r ph) (f_to (fam_fill F ph))
                    (f_pre (fam_fill F ph)) (f_suf (fam_fill F ph))).

Hypothesis Hrsv : Forall (RuleSound tm false false) rsv.
Hypothesis Hfire : forall r t, ~ In t pins -> minw pv <= r -> r < N0f + stf ->
  nfire tm true true rsv (vsegs r t) (visI r t) (lr_lhs (Afill r pv)) = Some t.

Local Notation Cf := (CfN F nar ds0 ph0).
Local Notation INV := (InvN F NPH minw).

Lemma invN0 : INV (ds0, 0, ph0).
Proof. simpl. repeat split; assumption. Qed.

(** the fill arm serving width [k]: its index is at least the phase's floor *)
Lemma farm_index : forall k ph, ph < NPH -> minw ph <= k ->
  minw ph <= aoff N0f stf k /\ aoff N0f stf k < N0f + stf
  /\ aoff N0f stf k + astride N0f stf (aoff N0f stf k) * acnt N0f stf k = k.
Proof.
  intros k ph Hph Hk. pose proof (HN0f ph Hph).
  split; [|split; [apply arm_index_lt; exact Hstf | apply arm_index; exact Hstf]].
  unfold aoff. destruct (k <? N0f); lia.
Qed.

Lemma cells_topN : forall k m1 st n ph, m1 + st * n = k ->
  fam_cells F (repeat (fm_b F - 1) k) ph
    = sden [] n (run_side F (fm_b F - 1) m1 st 0 ph [] []).
Proof.
  intros k m1 st n ph Hk.
  transitivity
    (fam_cells F ([] ++ repeat (fm_b F - 1) (m1 + st * n + 0) ++ []) ph).
  - f_equal. rewrite Nat.add_0_r, Hk, app_nil_r. reflexivity.
  - apply fam_cells_run.
Qed.

Lemma cells_nfilled : forall k a st n c ph,
  a + st * n + c
    = k + f_s (fam_fill F ph) - nar ph
      - (length (f_pre (fam_fill F ph)) + length (f_suf (fam_fill F ph))) ->
  fam_cells F (nfilled F nar ph k) (f_to (fam_fill F ph))
    = sden [] n
        (run_side F (f_mid (fam_fill F ph)) a st c (f_to (fam_fill F ph))
           (f_pre (fam_fill F ph)) (f_suf (fam_fill F ph))).
Proof.
  intros k a st n c ph Hk.
  transitivity (fam_cells F
    (f_pre (fam_fill F ph)
     ++ repeat (f_mid (fam_fill F ph)) (a + st * n + c)
     ++ f_suf (fam_fill F ph)) (f_to (fam_fill F ph))).
  - f_equal. unfold nfilled. rewrite Hk. reflexivity.
  - apply fam_cells_run.
Qed.

Lemma board_armNw : forall s, INV s ->
  exists s' A el er X n,
    nsucc F nar s = Some s'
    /\ ReachL tm el er (lr_lhs A) (lr_rhs A)
    /\ (el = true -> tailL F X = []) /\ (er = true -> tailR F X = [])
    /\ fam_cfg F s  = cden (tailL F X) (tailR F X) n (lr_lhs A)
    /\ fam_cfg F s' = cden (tailL F X) (tailR F X) n (lr_rhs A).
Proof.
  intros [[ds p] ph] Hi. destruct Hi as (Hbnd & Hmw & Hph).
  destruct (digs_decomp (fm_b F - 1) ds) as [Htop | (n & d & rest & -> & Hd)].
  - destruct (farm_index (length ds) ph Hph Hmw) as (Hr0 & Hrlt & Hk).
    set (r := aoff N0f stf (length ds)) in *.
    assert (Hist : fam_is_top F ds = true).
    { rewrite Htop at 1. apply pos1_is_top; assumption. }
    exists (nfilled F nar ph (length ds), p, f_to (fam_fill F ph)), (Afill r ph).
    exists true, true, [], (acnt N0f stf (length ds)).
    split; [|split; [|split; [|split; [|split]]]].
    + unfold nsucc. rewrite Hist. reflexivity.
    + exact (HAfS r ph Hr0 Hrlt Hph).
    + intros _; apply tailL_nil.
    + intros _; apply tailR_nil.
    + rewrite (HAfL r ph Hr0 Hrlt Hph). symmetry.
      apply cden_cls_conf. rewrite Htop at 1. apply cells_topN. exact Hk.
    + rewrite (HAfR r ph Hr0 Hrlt Hph). symmetry.
      apply cden_cls_conf. apply cells_nfilled.
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
      unfold nsucc. rewrite Hns.
      rewrite (pos1_class_not_top F d n rest Hb Hcode Hstep Hdlt Hrest).
      reflexivity.
    + exact (HAiS d r Hdlt Hrlt).
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

Lemma lapNw : forall n, exists m c,
  0 < m /\ csteps tm m (Cf n) = Some c /\ lift c = lift (Cf (S n)).
Proof.
  intros n.
  destruct (niter_totalN F NPH nar minw Hb Hcode Hstep Hfpre Hfsuf Hfmid Hfto
              Hmin n (ds0, 0, ph0) invN0) as (s & Hit & Hi).
  destruct (board_armNw s Hi)
    as (s' & A & el & er & X & k & Hsucc & HA & HL & HR & Hl & Hr).
  destruct (HA _ _ k HL HR) as (m & c & Hm & Hc & Hlc).
  exists m, c. split; [exact Hm|]. split.
  - unfold CfN. rewrite Hit, Hl. exact Hc.
  - rewrite Hlc, <- Hr. unfold CfN.
    replace (S n) with (n + 1) by lia.
    rewrite niter_add, Hit. simpl. rewrite Hsucc. reflexivity.
Qed.

Lemma fireNw : forall t N, ~ In t pins ->
  exists n k c, N <= n /\ csteps tm k (Cf n) = Some c /\ cinstr c = t.
Proof.
  intros t N Hnp.
  destruct (tops_cofinal_atN F NPH nar minw Hb Hcode Hstep Hfpre Hfsuf Hfmid
              Hfto Hmin pv (ds0, 0, ph0) N Hcyc invN0)
    as (n & s' & HN & Hit & Htop & Hi' & Hph).
  exists n.
  destruct s' as [[ds' p'] ph']. simpl in Htop. simpl in Hph. subst ph'.
  destruct Hi' as (Hbnd' & Hmw' & _).
  assert (Hsh : ds' = repeat (fm_b F - 1) (length ds'))
    by (apply pos1_top_shape; assumption).
  destruct (farm_index (length ds') pv Hpv Hmw') as (Hr0 & Hrlt & Hk).
  set (r := aoff N0f stf (length ds')) in *.
  assert (Hden : Cf n
                 = cden [] [] (acnt N0f stf (length ds')) (lr_lhs (Afill r pv))).
  { unfold CfN. rewrite Hit, (HAfL r pv Hr0 Hrlt Hpv).
    rewrite <- (cden_cls_conf F
                  (run_side F (fm_b F - 1) r (astride N0f stf r) 0 pv [] [])
                  [] (acnt N0f stf (length ds')) ds' p' pv).
    - unfold tailL, tailR; destruct (fm_left F); reflexivity.
    - rewrite Hsh at 1. apply cells_topN. exact Hk. }
  destruct (nfire_sound tm true true rsv (vsegs r t) (visI r t)
              (lr_lhs (Afill r pv)) t Hrsv (Hfire r t Hnp Hr0 Hrlt)
              [] [] (acnt N0f stf (length ds'))
              (fun _ => eq_refl) (fun _ => eq_refl)) as (k & c & Hc & Ht).
  exists k, c. rewrite Hden. split; [exact HN | split; [exact Hc | exact Ht]].
Qed.

Theorem boardNw_neverqhtr : forall t0,
  stepn tm t0 InitES = Some (lift (fam_cfg F (ds0, 0, ph0))) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros t0 Hboot.
  apply (glue_neverqhtrN tm0 pins Cf).
  - exists t0. unfold CfN; simpl. exact Hboot.
  - intros n. destruct (lapNw n) as (m & c & Hm & Hrun & Hl).
    exists m, c. split; [exact Hrun | split; [exact Hl | exact Hm]].
  - intros t Hnp N. exact (fireNw t N Hnp).
Qed.

Lemma reachNw : forall d n,
  exists T, stepn tm T (lift (Cf n)) = Some (lift (Cf (n + d))).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (T & HT).
    destruct (lapNw (n + d)) as (m & c & _ & Hm & Hl).
    exists (T + m). rewrite stepn_add, HT.
    replace (n + S d) with (S (n + d)) by lia.
    rewrite <- Hl. apply csteps_lift. exact Hm.
Qed.

Lemma fire_everyNw : forall t, ~ In t pins -> forall n,
  exists k c, csteps tm k (Cf n) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp n.
  destruct (fireNw t n Hnp) as (m & k & c & Hm & Hk & Hc).
  destruct (reachNw (m - n) n) as (T & HT).
  replace (n + (m - n)) with m in HT by lia.
  assert (Hs : stepn tm (T + k) (lift (Cf n)) = Some (lift c)).
  { rewrite stepn_add, HT. apply csteps_lift. exact Hk. }
  destruct (stepn_csteps_at tm (T + k) (Cf n) (lift c) Hs) as (c' & Hc' & Hl').
  exists (T + k), c'. split; [exact Hc'|].
  rewrite <- cinstr_lift, Hl', cinstr_lift. exact Hc.
Qed.

Theorem boardNw_qhtr : forall t0 B,
  stepn tm0 t0 InitES = Some (lift (fam_cfg F (ds0, 0, ph0))) ->
  existsb (fun tg => cfires tm0 CTape.c0 t0 tg) pins = true ->
  (t0 <=? B) = true ->
  NonHalt tm0 /\ QHBoundTr B tm0 /\ QuasiHaltsTr tm0.
Proof.
  intros t0 B Hboot Hwit Hle.
  apply (lap_qh_stage tm0 pins (fun p => Cf (Nat.pred (Pos.to_nat p)))
           1%positive t0 B).
  - simpl. unfold CfN; simpl. exact Hboot.
  - intros p _.
    destruct (lapNw (Nat.pred (Pos.to_nat p))) as (m & c & Hm & Hrun & Hl).
    exists m, c. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (fire_everyNw t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End BoardNwTr.
