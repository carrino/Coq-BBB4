(** * Checkers.LadderCheckSweepTr: positional counters whose carry SWEEPS the
    run of top digits after the digit it increments (SCOPING_INSTR 7.4.LE4).

    LE2 found DN rows ([0RB0LA_0RC1RB_0LD1RC_1LA1LD], ...) whose increment of
    [t^n d . t^m e rest] writes [d + 1] and then walks across [t^m] to [e]
    and back before returning to the anchor; LE4 found ten.  [LadderCheck]'s
    interior class is [t^n d X] with [X] opaque, and an arm has ONE run index,
    so the class [t^n d t^m e Y] (two run lengths) is not an arm.  But its
    increment is three one-index rules in a row:

    - the carry [A d ra]: from the anchor over [t^n] to the incremented
      digit, stopping on its LAST cell (the pivot) with the rest of the
      counter, [X], still opaque on the counter side;
    - the excursion [P d k ph rm]: from the pivot across [t^m] to the word
      [e] (kind [k = e < b - 1]) or to the terminator of phase [ph] (kind
      [k = b - 1], the counter's end) and back to the pivot, the tape
      unchanged, both tails opaque (the counter-side one known empty at the
      end);
    - the return [C d k ra]: from the pivot back to the anchor, [X] opaque
      again.

    Each is an ordinary [LadderNest.ReachL] program with its own index, and
    composing them needs only [csteps_lift] / [stepn_csteps_at]: up to
    [lift], the configuration [A] lands on IS the one [P] starts from (the
    counter side of [A]'s right-hand side and the far side of [P]'s are
    empty, so the opaque tails carry the rest), and likewise [P] to [C].
    The family, the class split, the fill arms and the liveness are
    [LadderCheck]'s positional ones, unchanged ([Inv], [iter_total],
    [tops_cof_pv], [fill_top]).

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

(** ** 1. Sides and composition *)

Section Sides.

Variable F : Fam.

(** the counter side and the far side of a symbolic configuration *)
Definition ctrS (c : sconf) : sside := if fm_left F then c_l c else c_r c.
Definition othS (c : sconf) : sside := if fm_left F then c_r c else c_l c.

(** the word the excursion turns at: digit [k], or the terminator of phase
    [ph] at the counter's end ([k = b - 1]) *)
Definition swE (k ph : nat) : list Sym :=
  if k <? fm_b F - 1 then dig F k else nth ph (fm_tails F) [].

(** the far tail and the counter tail, placed *)
Definition tailsS (XO XC : list Sym) : list Sym * list Sym :=
  if fm_left F then (XC, XO) else (XO, XC).

Lemma cden_split : forall c XO XC j,
  ctrS c = sflat [] ->
  cden (fst (tailsS XO XC)) (snd (tailsS XO XC)) j c
  = if fm_left F
    then (c_st c, (XC, c_h c, sden XO j (c_r c)))
    else (c_st c, (sden XO j (c_l c), c_h c, XC)).
Proof.
  intros [q l h r] XO XC j H. unfold ctrS, tailsS, cden in *; cbn in *.
  destruct (fm_left F); subst; rewrite sden_flat; reflexivity.
Qed.

Lemma cden_split2 : forall c XO XC j,
  othS c = sflat [] ->
  cden (fst (tailsS XO XC)) (snd (tailsS XO XC)) j c
  = if fm_left F
    then (c_st c, (sden XC j (c_l c), c_h c, XO))
    else (c_st c, (XO, c_h c, sden XC j (c_r c))).
Proof.
  intros [q l h r] XO XC j H. unfold othS, tailsS, cden in *; cbn in *.
  destruct (fm_left F); subst; rewrite sden_flat; reflexivity.
Qed.

Lemma tailsS_cls : forall X,
  tailsS [] X = (tailL F X, tailR F X).
Proof. intros X. unfold tailsS, tailL, tailR. destruct (fm_left F); reflexivity. Qed.

End Sides.

Section Compose.

Variable tm : TM.

Definition ReachC (c c' : cconf) : Prop :=
  exists m c'', csteps tm m c = Some c'' /\ lift c'' = lift c'.

Lemma reachC_trans : forall c1 c2 c3, ReachC c1 c2 -> ReachC c2 c3 -> ReachC c1 c3.
Proof.
  intros c1 c2 c3 (m1 & d1 & H1 & L1) (m2 & d2 & H2 & L2).
  assert (Hs : stepn tm (m1 + m2) (lift c1) = Some (lift d2)).
  { rewrite stepn_add, (csteps_lift _ _ _ _ H1), L1. apply csteps_lift. exact H2. }
  destruct (stepn_csteps_at tm (m1 + m2) c1 (lift d2) Hs) as (d & Hd & Ld).
  exists (m1 + m2), d. split; [exact Hd | rewrite Ld, L2; reflexivity].
Qed.

Lemma reachC_pos : forall c1 c2 c3 m1 d1,
  0 < m1 -> csteps tm m1 c1 = Some d1 -> lift d1 = lift c2 -> ReachC c2 c3 ->
  exists m d, 0 < m /\ csteps tm m c1 = Some d /\ lift d = lift c3.
Proof.
  intros c1 c2 c3 m1 d1 Hm H1 L1 (m2 & d2 & H2 & L2).
  assert (Hs : stepn tm (m1 + m2) (lift c1) = Some (lift d2)).
  { rewrite stepn_add, (csteps_lift _ _ _ _ H1), L1. apply csteps_lift. exact H2. }
  destruct (stepn_csteps_at tm (m1 + m2) c1 (lift d2) Hs) as (d & Hd & Ld).
  exists (m1 + m2), d. split; [lia | split; [exact Hd | rewrite Ld, L2; reflexivity]].
Qed.

End Compose.

(** ** 2. The board *)

Section BoardSwTr.

Variable tm0   : TM.
Variable pins  : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable F     : Fam.
Variable NPH   : nat.
Variable AA    : nat -> nat -> LRule.               (** carry: digit, index *)
Variable N0a sta : nat.
Variable AP    : nat -> nat -> nat -> nat -> LRule. (** excursion: digit, kind, phase, index *)
Variable N0p stp : nat.
Variable AC    : nat -> nat -> nat -> LRule.        (** return: digit, kind, index *)
Variable Afill : nat -> nat -> LRule.
Variable N0f stf : nat.
Variable fm1 fm2 : nat -> nat -> nat.
Variable pv    : nat.
Variable rsv   : list LRule.
Variable vsegs : nat -> Instr -> list nseg.
Variable visI  : nat -> Instr -> list lstep.
Variable ds0   : list nat.
Variable ph0   : nat.

Local Notation b := (fm_b F).
Local Notation tw := (dig F (fm_b F - 1)).

Hypothesis Hb    : 1 < b.
Hypothesis Hcode : fm_code F = Binary.
Hypothesis Hstep : fm_step F = 1.
Hypothesis Hfpre : forall ph, ph < NPH ->
  Forall (fun d => d < b) (f_pre (fam_fill F ph)).
Hypothesis Hfsuf : forall ph, ph < NPH ->
  Forall (fun d => d < b) (f_suf (fam_fill F ph)).
Hypothesis Hfmid : forall ph, ph < NPH -> f_mid (fam_fill F ph) < b.
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

Hypothesis Hbnd0 : Forall (fun d => d < b) ds0.
Hypothesis Hlen0 : 0 < length ds0.
Hypothesis Hph0  : ph0 < NPH.

(** *** The carry *)
Hypothesis Hsta : 0 < sta.
Hypothesis HAaS : forall d ra, d < b - 1 -> ra < N0a + sta ->
  ReachL tm (negb (fm_left F)) (fm_left F) (lr_lhs (AA d ra)) (lr_rhs (AA d ra)).
Hypothesis HAaL : forall d ra, d < b - 1 -> ra < N0a + sta ->
  lr_lhs (AA d ra) = cls_conf F (cls_side F [] (b - 1) ra (astride N0a sta ra) [d]).
Hypothesis HAaC : forall d ra, d < b - 1 -> ra < N0a + sta ->
  ctrS F (lr_rhs (AA d ra)) = sflat [].

(** *** The excursion: it starts where every carry of its digit stops *)
Hypothesis Hstp : 0 < stp.
Hypothesis HApS : forall d k ph rm, d < b - 1 -> k < b -> ph < NPH -> rm < N0p + stp ->
  ReachL tm ((k =? b - 1) && fm_left F) ((k =? b - 1) && negb (fm_left F))
    (lr_lhs (AP d k ph rm)) (lr_rhs (AP d k ph rm)).
Hypothesis HApQ : forall d k ph rm ra, d < b - 1 -> k < b -> ph < NPH -> rm < N0p + stp ->
  ra < N0a + sta ->
  c_st (lr_lhs (AP d k ph rm)) = c_st (lr_rhs (AA d ra))
  /\ c_h (lr_lhs (AP d k ph rm)) = c_h (lr_rhs (AA d ra)).
Hypothesis HApL : forall d k ph rm, d < b - 1 -> k < b -> ph < NPH -> rm < N0p + stp ->
  othS F (lr_lhs (AP d k ph rm)) = sflat []
  /\ ctrS F (lr_lhs (AP d k ph rm)) = blk (rep tw rm) tw (astride N0p stp rm) (swE F k ph).
Hypothesis HApR : forall d k ph rm, d < b - 1 -> k < b -> ph < NPH -> rm < N0p + stp ->
  othS F (lr_rhs (AP d k ph rm)) = sflat []
  /\ ctrS F (lr_rhs (AP d k ph rm)) = ctrS F (lr_lhs (AP d k ph rm)).

(** *** The return: it starts where every excursion of its digit and kind
    stops, with the carry's far side *)
Hypothesis HAcS : forall d k ra, d < b - 1 -> k < b -> ra < N0a + sta ->
  ReachL tm (negb (fm_left F)) (fm_left F) (lr_lhs (AC d k ra)) (lr_rhs (AC d k ra)).
Hypothesis HAcQ : forall d k ra ph rm, d < b - 1 -> k < b -> ra < N0a + sta ->
  ph < NPH -> rm < N0p + stp ->
  c_st (lr_lhs (AC d k ra)) = c_st (lr_rhs (AP d k ph rm))
  /\ c_h (lr_lhs (AC d k ra)) = c_h (lr_rhs (AP d k ph rm)).
Hypothesis HAcL : forall d k ra, d < b - 1 -> k < b -> ra < N0a + sta ->
  othS F (lr_lhs (AC d k ra)) = othS F (lr_rhs (AA d ra))
  /\ ctrS F (lr_lhs (AC d k ra)) = sflat [].
Hypothesis HAcR : forall d k ra, d < b - 1 -> k < b -> ra < N0a + sta ->
  lr_rhs (AC d k ra) = cls_conf F (cls_side F [] 0 ra (astride N0a sta ra) [S d]).

(** *** The fill arms, as in [LadderCheck] *)
Hypothesis Hstf : 0 < stf.
Hypothesis HN0f : 0 < N0f.
Hypothesis HAfS : forall r ph, 0 < r -> r < N0f + stf -> ph < NPH ->
  ReachL tm true true (lr_lhs (Afill r ph)) (lr_rhs (Afill r ph)).
Hypothesis HAfL : forall r ph, 0 < r -> r < N0f + stf -> ph < NPH ->
  lr_lhs (Afill r ph)
    = cls_conf F (run_side F (b - 1) r (astride N0f stf r) 0 ph [] []).
Hypothesis HAfR : forall r ph, 0 < r -> r < N0f + stf -> ph < NPH ->
  lr_rhs (Afill r ph)
    = cls_conf F (run_side F (f_mid (fam_fill F ph)) (fm1 r ph)
                    (astride N0f stf r) (fm2 r ph) (f_to (fam_fill F ph))
                    (f_pre (fam_fill F ph)) (f_suf (fam_fill F ph))).

Hypothesis Hrsv : Forall (RuleSound tm false false) rsv.
Hypothesis Hfire : forall r t, ~ In t pins -> 0 < r -> r < N0f + stf ->
  nfire tm true true rsv (vsegs r t) (visI r t) (lr_lhs (Afill r pv)) = Some t.

(** the interior increment of [t^n d t^m e Y] (or [t^n d t^m] at the end),
    by carry, excursion and return *)
Lemma sweep_lap : forall n d m k rest ph p, d < b - 1 -> k < b -> ph < NPH ->
  (k < b - 1 -> exists rest', rest = k :: rest') ->
  (k = b - 1 -> rest = []) ->
  exists mm c', 0 < mm
    /\ csteps tm mm (fam_cfg F (repeat (b - 1) n ++ d :: repeat (b - 1) m ++ rest, p, ph)) = Some c'
    /\ lift c' = lift (fam_cfg F (repeat 0 n ++ S d :: repeat (b - 1) m ++ rest, p, ph)).
Proof.
  intros n d m k rest ph p Hd Hk Hph Hkc Hke.
  remember (aoff N0a sta n) as ra eqn:Era.
  assert (Hralt : ra < N0a + sta) by (subst ra; apply arm_index_lt; assumption).
  assert (Hn : ra + astride N0a sta ra * acnt N0a sta n = n)
    by (subst ra; apply arm_index; assumption).
  remember (aoff N0p stp m) as rm eqn:Erm.
  assert (Hrmlt : rm < N0p + stp) by (subst rm; apply arm_index_lt; assumption).
  assert (Hm : rm + astride N0p stp rm * acnt N0p stp m = m)
    by (subst rm; apply arm_index; assumption).
  set (jn := acnt N0a sta n) in *. set (jm := acnt N0p stp m) in *.
  (* the tails: Y after the turning word, X after the digit *)
  set (Y := if k <? b - 1 then cls_tail F (tl rest) ph else []).
  set (X := rep tw m ++ swE F k ph ++ Y).
  assert (HX : flat_map (dig F) (repeat (b - 1) m ++ rest) ++ nth ph (fm_tails F) [] = X).
  { unfold X, Y, swE. rewrite flat_map_app, flat_map_repeat_nil, <- app_assoc. f_equal.
    destruct (Nat.ltb_spec k (b - 1)) as [Hlt|Hge].
    - destruct (Hkc Hlt) as (rest' & ->). cbn [flat_map tl]. unfold cls_tail.
      rewrite <- app_assoc. reflexivity.
    - assert (k = b - 1) by lia. rewrite (Hke H). cbn [flat_map]. rewrite app_nil_r.
      reflexivity. }
  (* the anchor, as the carry's lhs *)
  assert (H0 : fam_cfg F (repeat (b - 1) n ++ d :: repeat (b - 1) m ++ rest, p, ph)
               = cden (tailL F X) (tailR F X) jn (lr_lhs (AA d ra))).
  { rewrite (HAaL d ra Hd Hralt). symmetry. apply cden_cls_conf.
    rewrite <- Hn at 1.
    transitivity (fam_cells F ([] ++ repeat (b - 1) (ra + astride N0a sta ra * jn)
                                  ++ [d] ++ (repeat (b - 1) m ++ rest)) ph); [reflexivity|].
    rewrite (fam_cells_class F [] (b - 1) ra (astride N0a sta ra) jn [d]
               (repeat (b - 1) m ++ rest) ph).
    unfold cls_tail. rewrite HX. reflexivity. }
  (* the end, as the return's rhs *)
  assert (H3 : fam_cfg F (repeat 0 n ++ S d :: repeat (b - 1) m ++ rest, p, ph)
               = cden (tailL F X) (tailR F X) jn (lr_rhs (AC d k ra))).
  { rewrite (HAcR d k ra Hd Hk Hralt). symmetry. apply cden_cls_conf.
    rewrite <- Hn at 1.
    transitivity (fam_cells F ([] ++ repeat 0 (ra + astride N0a sta ra * jn)
                                  ++ [S d] ++ (repeat (b - 1) m ++ rest)) ph); [reflexivity|].
    rewrite (fam_cells_class F [] 0 ra (astride N0a sta ra) jn [S d]
               (repeat (b - 1) m ++ rest) ph).
    unfold cls_tail. rewrite HX. reflexivity. }
  (* the carry *)
  destruct (HAaS d ra Hd Hralt (tailL F X) (tailR F X) jn) as (m1 & d1 & Hm1 & Hc1 & Hl1).
  { intros He. unfold tailL. destruct (fm_left F); [discriminate|reflexivity]. }
  { intros He. unfold tailR. rewrite He. reflexivity. }
  rewrite H0, H3.
  apply (reachC_pos tm _ (cden (tailL F X) (tailR F X) jn (lr_rhs (AA d ra))) _ m1 d1 Hm1 Hc1 Hl1).
  (* the far side the carry leaves *)
  set (XO := sden [] jn (othS F (lr_rhs (AA d ra)))).
  destruct (HApL d k ph rm Hd Hk Hph Hrmlt) as (HPo & HPc).
  destruct (HApR d k ph rm Hd Hk Hph Hrmlt) as (HPo' & HPc').
  destruct (HApQ d k ph rm ra Hd Hk Hph Hrmlt Hralt) as (HPq & HPh).
  destruct (HAcL d k ra Hd Hk Hralt) as (HCo & HCc).
  destruct (HAcQ d k ra ph rm Hd Hk Hralt Hph Hrmlt) as (HCq & HCh).
  (* the counter side of the excursion is X *)
  assert (HXP : sden Y jm (ctrS F (lr_lhs (AP d k ph rm))) = X).
  { rewrite HPc, blk_den, app_assoc, <- rep_add, Hm. reflexivity. }
  (* carry -> excursion: the same configuration *)
  assert (E1 : cden (tailL F X) (tailR F X) jn (lr_rhs (AA d ra))
               = cden (fst (tailsS F XO Y)) (snd (tailsS F XO Y)) jm (lr_lhs (AP d k ph rm))).
  { pose proof (cden_split2 F (lr_lhs (AP d k ph rm)) XO Y jm HPo) as S1.
    pose proof (cden_split F (lr_rhs (AA d ra)) [] X jn (HAaC d ra Hd Hralt)) as S2.
    unfold XO, tailsS, ctrS, othS, tailL, tailR in *.
    destruct (fm_left F) eqn:EL; rewrite ?EL in *; cbn beta iota delta [fst snd] in *;
      rewrite S1, S2, HPq, HPh, HXP; reflexivity. }
  (* excursion -> return *)
  assert (E2 : cden (fst (tailsS F XO Y)) (snd (tailsS F XO Y)) jm (lr_rhs (AP d k ph rm))
               = cden (tailL F X) (tailR F X) jn (lr_lhs (AC d k ra))).
  { pose proof (cden_split2 F (lr_rhs (AP d k ph rm)) XO Y jm HPo') as S1.
    pose proof (cden_split F (lr_lhs (AC d k ra)) [] X jn HCc) as S2.
    assert (HXP' : sden Y jm (ctrS F (lr_rhs (AP d k ph rm))) = X) by (rewrite HPc'; exact HXP).
    unfold XO, tailsS, ctrS, othS, tailL, tailR in *.
    destruct (fm_left F) eqn:EL; rewrite ?EL in *; cbn beta iota delta [fst snd] in *;
      rewrite S1, S2, HCq, HCh, HCo, HXP'; reflexivity. }
  rewrite E1.
  apply (reachC_trans tm _ (cden (fst (tailsS F XO Y)) (snd (tailsS F XO Y)) jm
                              (lr_rhs (AP d k ph rm)))).
  - destruct (HApS d k ph rm Hd Hk Hph Hrmlt (fst (tailsS F XO Y)) (snd (tailsS F XO Y)) jm)
      as (m2 & d2 & _ & Hc2 & Hl2).
    + intros He. unfold tailsS, Y. apply andb_true_iff in He as [Hk1 Hl].
      apply Nat.eqb_eq in Hk1. rewrite Hl. cbn [fst].
      destruct (Nat.ltb_spec k (b - 1)); [lia | reflexivity].
    + intros He. unfold tailsS, Y. apply andb_true_iff in He as [Hk1 Hl].
      apply Nat.eqb_eq in Hk1. apply negb_true_iff in Hl. rewrite Hl. cbn [snd].
      destruct (Nat.ltb_spec k (b - 1)); [lia | reflexivity].
    + exists m2, d2. split; [exact Hc2 | exact Hl2].
  - rewrite E2.
    destruct (HAcS d k ra Hd Hk Hralt (tailL F X) (tailR F X) jn) as (m3 & d3 & _ & Hc3 & Hl3).
    + intros He. unfold tailL. destruct (fm_left F); [discriminate|reflexivity].
    + intros He. unfold tailR. rewrite He. reflexivity.
    + exists m3, d3. split; [exact Hc3 | exact Hl3].
Qed.

(** The lap, by [LadderCheck]'s case split and, inside the interior class,
    the run after the digit split once more *)
Lemma board_lapS : forall s, Inv F NPH s ->
  exists s' m c', fam_succ F s = Some s' /\ 0 < m
    /\ csteps tm m (fam_cfg F s) = Some c' /\ lift c' = lift (fam_cfg F s').
Proof.
  intros [[ds p] ph] Hi. pose proof Hi as Hi0. destruct Hi as (Hbnd & Hlen & Hph).
  destruct (digs_decomp (b - 1) ds) as [Htop | (n & d & rest & -> & Hd)].
  - (* the top: a fill arm *)
    remember (aoff N0f stf (length ds)) as r eqn:Er.
    assert (Hr0 : 0 < r) by (subst r; apply arm_index_pos; assumption).
    assert (Hrlt : r < N0f + stf) by (subst r; apply arm_index_lt; assumption).
    assert (Hk : r + astride N0f stf r * acnt N0f stf (length ds) = length ds)
      by (subst r; apply arm_index; assumption).
    assert (Hist : fam_is_top F ds = true).
    { rewrite Htop at 1. apply pos1_is_top; assumption. }
    exists (filled F ph (length ds), p, f_to (fam_fill F ph)).
    destruct (HAfS r ph Hr0 Hrlt Hph [] [] (acnt N0f stf (length ds))
                (fun _ => eq_refl) (fun _ => eq_refl)) as (m & c' & Hm & Hc & Hl).
    exists m, c'. split; [|split; [exact Hm|split]].
    + unfold fam_succ.
      rewrite (fill_top F NPH Hb Hcode Hstep Hfs ds ph Hph Hlen Hist), Hist. reflexivity.
    + rewrite <- Hc. f_equal.
      rewrite (HAfL r ph Hr0 Hrlt Hph).
      assert (Hc0 : fam_cells F ds ph
                    = sden [] (acnt N0f stf (length ds))
                        (run_side F (b - 1) r (astride N0f stf r) 0 ph [] []))
        by (rewrite Htop at 1; apply cells_top; exact Hk).
      pose proof (cden_cls_conf F _ [] _ ds p ph Hc0) as H.
      rewrite tailL_nil, tailR_nil in H. symmetry. exact H.
    + rewrite Hl. f_equal. rewrite (HAfR r ph Hr0 Hrlt Hph).
      assert (Hc0 : fam_cells F (filled F ph (length ds)) (f_to (fam_fill F ph))
                    = sden [] (acnt N0f stf (length ds))
                        (run_side F (f_mid (fam_fill F ph)) (fm1 r ph)
                           (astride N0f stf r) (fm2 r ph) (f_to (fam_fill F ph))
                           (f_pre (fam_fill F ph)) (f_suf (fam_fill F ph)))).
      { apply cells_filled. pose proof (Hfm12 r ph Hr0 Hrlt Hph). lia. }
      pose proof (cden_cls_conf F _ [] _ _ p _ Hc0) as H.
      rewrite tailL_nil, tailR_nil in H. exact H.
  - (* the interior: the run after the digit, and what ends it *)
    apply Forall_app in Hbnd as [Hrun Hrest'].
    inversion Hrest' as [|? ? Hdb Hrest]; subst.
    assert (Hdlt : d < b - 1) by lia.
    exists (repeat 0 n ++ S d :: rest, p, ph).
    assert (Hsucc : fam_succ F (repeat (b - 1) n ++ d :: rest, p, ph)
                    = Some (repeat 0 n ++ S d :: rest, p, ph)).
    { assert (Hns : fam_next F (repeat (b - 1) n ++ d :: rest) ph
                    = Some (repeat 0 n ++ S d :: rest))
        by exact (pos1_class_succ F d Hb Hcode Hstep Hdlt n rest ph Hrest I).
      unfold fam_succ. rewrite Hns.
      rewrite (pos1_class_not_top F d n rest Hb Hcode Hstep Hdlt Hrest).
      reflexivity. }
    destruct (digs_decomp (b - 1) rest) as [Hall | (m & e & rest' & Hre & He)].
    + (* the run reaches the counter's end *)
      destruct (sweep_lap n d (length rest) (b - 1) [] ph p Hdlt ltac:(lia) Hph
                  (fun H => ltac:(lia)) (fun _ => eq_refl)) as (mm & c' & Hmm & Hc & Hl).
      rewrite app_nil_r, <- Hall in Hc, Hl.
      exists mm, c'. split; [exact Hsucc | split; [exact Hmm | split; assumption]].
    + (* the run ends at a digit below the top *)
      rewrite Hre in Hrest. apply Forall_app in Hrest as [_ Hrest2].
      inversion Hrest2 as [|? ? Heb _]; subst.
      assert (Helt : e < b - 1) by lia.
      destruct (sweep_lap n d m e (e :: rest') ph p Hdlt ltac:(lia) Hph
                  (fun _ => ex_intro _ rest' eq_refl) (fun H => ltac:(lia)))
        as (mm & c' & Hmm & Hc & Hl).
      exists mm, c'. split; [exact Hsucc | split; [exact Hmm | split; assumption]].
Qed.

Local Notation Cf := (CfB F ds0 ph0).

Lemma lapS : forall n, exists m c',
  0 < m /\ csteps tm m (Cf n) = Some c' /\ lift c' = lift (Cf (S n)).
Proof.
  intros n.
  destruct (iter_total F NPH Hb Hcode Hstep Hfpre Hfsuf Hfmid Hfs Hfto n
              (ds0, 0, ph0) (inv0 F NPH ds0 ph0 Hbnd0 Hlen0 Hph0)) as (s & Hit & Hi).
  destruct (board_lapS s Hi) as (s' & m & c' & Hsucc & Hm & Hrun & Hl).
  exists m, c'. unfold CfB. rewrite Hit.
  split; [exact Hm | split; [exact Hrun|]].
  replace (S n) with (n + 1) by lia.
  rewrite fam_iter_add, Hit. simpl. rewrite Hsucc. exact Hl.
Qed.

Lemma fireS : forall t N, ~ In t pins ->
  exists n k c, N <= n /\ csteps tm k (Cf n) = Some c /\ cinstr c = t.
Proof.
  intros t N Hnp.
  destruct (tops_cof_pv F NPH pv Hb Hcode Hstep Hfpre Hfsuf Hfmid Hfs Hfto
              Hcyc (ds0, 0, ph0) N (inv0 F NPH ds0 ph0 Hbnd0 Hlen0 Hph0))
    as (n & s' & HN & Hit & Htop & Hi' & Hph).
  exists n.
  destruct s' as [[ds' p'] ph']. simpl in Htop. simpl in Hph. subst ph'.
  destruct Hi' as (Hbnd' & Hlen' & _).
  assert (Hsh : ds' = repeat (b - 1) (length ds'))
    by (apply pos1_top_shape; assumption).
  remember (aoff N0f stf (length ds')) as r eqn:Er.
  assert (Hr0 : 0 < r) by (subst r; apply arm_index_pos; assumption).
  assert (Hrlt : r < N0f + stf) by (subst r; apply arm_index_lt; assumption).
  assert (Hk : r + astride N0f stf r * acnt N0f stf (length ds') = length ds')
    by (subst r; apply arm_index; assumption).
  assert (Hden : Cf n = cden [] [] (acnt N0f stf (length ds')) (lr_lhs (Afill r pv))).
  { unfold CfB. rewrite Hit, (HAfL r pv Hr0 Hrlt Hpv).
    rewrite <- (cden_cls_conf F
                  (run_side F (b - 1) r (astride N0f stf r) 0 pv [] [])
                  [] (acnt N0f stf (length ds')) ds' p' pv).
    - unfold tailL, tailR; destruct (fm_left F); reflexivity.
    - rewrite Hsh at 1. apply cells_top. exact Hk. }
  destruct (nfire_sound tm true true rsv (vsegs r t) (visI r t)
              (lr_lhs (Afill r pv)) t Hrsv (Hfire r t Hnp Hr0 Hrlt)
              [] [] (acnt N0f stf (length ds'))
              (fun _ => eq_refl) (fun _ => eq_refl)) as (k & c & Hc & Ht).
  exists k, c. rewrite Hden. split; [exact HN | split; [exact Hc | exact Ht]].
Qed.

Theorem boardS_neverqhtr : forall t0,
  stepn tm t0 InitES = Some (lift (fam_cfg F (ds0, 0, ph0))) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros t0 Hboot.
  apply (glue_neverqhtrN tm0 pins Cf).
  - exists t0. exact Hboot.
  - intros n. destruct (lapS n) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [exact Hl | exact Hm]].
  - intros t Hnp N. exact (fireS t N Hnp).
Qed.

Lemma reachS : forall d n,
  exists Tm, stepn tm Tm (lift (Cf n)) = Some (lift (Cf (n + d))).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (Tm & HT).
    destruct (lapS (n + d)) as (m & c' & _ & Hm & Hl).
    exists (Tm + m). rewrite stepn_add, HT.
    replace (n + S d) with (S (n + d)) by lia.
    rewrite <- Hl. apply csteps_lift. exact Hm.
Qed.

Lemma fire_everyS : forall t, ~ In t pins -> forall n,
  exists k c', csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t Hnp n.
  destruct (fireS t n Hnp) as (m & k & c' & Hm & Hk & Hc').
  destruct (reachS (m - n) n) as (Tm & HT).
  replace (n + (m - n)) with m in HT by lia.
  assert (Hs : stepn tm (Tm + k) (lift (Cf n)) = Some (lift c')).
  { rewrite stepn_add, HT. apply csteps_lift. exact Hk. }
  destruct (stepn_csteps_at tm (Tm + k) (Cf n) (lift c') Hs) as (c'' & Hc'' & Hl').
  exists (Tm + k), c''. split; [exact Hc''|].
  rewrite <- cinstr_lift, Hl', cinstr_lift. exact Hc'.
Qed.

Theorem boardS_qhtr : forall t0 B,
  stepn tm0 t0 InitES = Some (lift (fam_cfg F (ds0, 0, ph0))) ->
  existsb (fun tg => cfires tm0 CTape.c0 t0 tg) pins = true ->
  (t0 <=? B) = true ->
  NonHalt tm0 /\ QHBoundTr B tm0 /\ QuasiHaltsTr tm0.
Proof.
  intros t0 B Hboot Hwit Hle.
  apply (lap_qh_stage tm0 pins (fun p => Cf (Nat.pred (Pos.to_nat p)))
           1%positive t0 B).
  - unfold CfB. simpl. exact Hboot.
  - intros p _.
    destruct (lapS (Nat.pred (Pos.to_nat p))) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (fire_everyS t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End BoardSwTr.
