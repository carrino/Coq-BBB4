(** * Bin3Lap: the BASE-TWO rows whose lap grows like [3^c], reduced to ONE
      open lemma -- and the reduction is shared by BOTH of them.

    The two rows are

      1RB1LC_1LB1RA_0LC0LD_0RA0RD
      1RB1LC_1LC1RA_0LC0LD_0RA0RD

    one transition apart ([B0]: [1LB] vs [1LC]).  `docs/LADDER_PLAN.md` §4y
    measured them as BASE 2 with a geometric lap, and priced the board as
    "an inner induction over the carry run, and one closer serves both rows".
    `tools/counters/bin3lap.py` and `tools/counters/bin3lem.py` sharpen that
    to an exact anchor and an exact lemma chain; this file is that chain,
    with every link proved except one, which is stated as [Hloop].

    ** The anchor

      Cf p = (qD, ([], S0, Wp p))

    [MonoCounter.Wp] VERBATIM -- 2 cells a digit, LSB nearest the head, the
    even pad cell that [Wp] already carries -- checked cell for cell against
    1,023 and 1,395 consecutive anchor visits with zero mismatches, values
    1, 2, 3, ... with no offset.  So the numeral side is free: [Wp],
    [cview], [cview_some_W] and [cview_none_W] are reused unchanged, exactly
    as [TernCounter] was free for §4y's base-3 row.

    ** The two rows differ in ONE composite, not in their lap

    The only table difference is where [B0] goes.  Over 3,000,000 steps each,
    EVERY [B]-on-[S0] event of BOTH rows has an [S1] to its left
    (`tools/counters/bin3lap.py`), and from there the two rows agree on the
    composite

      (qB, (S1::L, S0, R))  -->  (qD, (ctl L, chd L, S0::S1::R))

    row 1 in four steps ([B0;B1;A1;C1]) and row 2 in two ([B0;C1]).  That is
    [Hbc] below, and [bc_selfB] / [bc_toC] discharge it from each row's own
    [B0].  Everything downstream sees only [Hbc], so ONE closer serves both
    rows and the whole lap difference ([3.5*3^c + c + 2.5] against
    [3^(c+1) + 2c + 1]) is absorbed by an existential step count.

    ** What is proved here, and what is not

    [core] -- the lap's own induction over the carry run -- IS proved, from
    [Hloop].  So is the lap ([lapD]), the visit obligation ([visD]) and the
    closer ([bin3_nqh]).  [Hloop] itself is NOT proved.  It is

      LOOP(k,d) :  (qD, (rep [S0] d ++ S1::M, S1,  rep [S0] (2k+1) ++ S1::R))
               --> (qD, (ctl M,      chd M, rep [S0] (2k+3+d) ++ S1::R))

    verified over an UNKNOWN context on both sides for k = 0..5, d = 0..3 on
    both rows (`tools/counters/bin3lem.py`), and [tick] below proves the
    k = 0 case outright.  What §4y did not price is that k >= 1 is not one
    more induction over the carry run: LOOP(k,0) runs the counter through a
    whole k-digit field and then a DESCENDING CASCADE of
    LOOP(0,0), LOOP(1,0), ..., LOOP(k-1,2) -- the shape
    [Counters/NestedLapCascade.v] is named for, "2j+1 counts in all".  The
    step counts confirm it exactly (row 2, k = 3:
    [1 + 72 + 9 + 6 + 18 + 56 = 162]).

    Axiom footprint: none of its own. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape MonoCounter LapGlue.
Import ListNotations.

(** ** The field numeral

    `Hloop`'s inner run counts a FIXED-WIDTH field whose top digit is not a
    digit at all: the marker [S1] sitting above it plays that part.  So the
    field word is [MonoCounter.Wp] with its top digit dropped,

      Wp p = Fld p ++ [S0; S1]

    and [cview] transfers verbatim -- [cview_some_F] and [cview_none_F] below
    are [cview_some_W] and [cview_none_W] with [Wp] read as [Fld]. *)

Fixpoint Fld (p : positive) : list Sym :=
  match p with
  | xH => []
  | xO q => S0 :: S0 :: Fld q
  | xI q => S0 :: S1 :: Fld q
  end.

Lemma Wp_Fld : forall p, Wp p = Fld p ++ [S0; S1].
Proof. induction p; simpl; rewrite ?IHp; reflexivity. Qed.

Lemma cview_some_F : forall p j q, cview p = (j, Some q) ->
  Fld p = rep [S0; S1] j ++ S0 :: S0 :: Fld q /\
  Fld (Pos.succ p) = rep [S0; S0] j ++ S0 :: S1 :: Fld q.
Proof.
  induction p; intros j q H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E.
    inversion H; subst j r.
    destruct (IHp j' q eq_refl) as (H1 & H2).
    split; simpl; [rewrite H1 | rewrite H2]; reflexivity.
  - inversion H; subst j q. split; reflexivity.
  - discriminate.
Qed.

(** [cview] never returns [(0, None)]: a zero carry means the low bit is
    clear, which is the [xO] case, which always has a tail. *)
Lemma cview_none_S : forall p j, cview p = (j, None) -> exists i, j = S i.
Proof.
  induction p; intros j H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E. inversion H. eauto.
  - discriminate.
  - inversion H. eauto.
Qed.

Lemma cview_none_F : forall p i, cview p = (S i, None) -> Fld p = rep [S0; S1] i.
Proof.
  induction p; intros i H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E.
    inversion H; subst r i.
    destruct (cview_none_S p j' E) as (i' & ->).
    cbn [Fld]. rewrite (IHp i' eq_refl). cbn [rep app]. reflexivity.
  - discriminate.
  - inversion H; subst i. reflexivity.
Qed.

Lemma rep2_length : forall (a b : Sym) k, length (rep [a; b] k) = 2 * k.
Proof.
  intros a b. induction k; cbn [rep]; [reflexivity |].
  rewrite app_length, IHk. cbn [length]. lia.
Qed.

(** The carry is strictly inside the field, so [core] is only ever called at
    a level BELOW the field's width -- which is what makes the whole nest
    well founded. *)
Lemma Fld_carry_lt : forall p j q, cview p = (j, Some q) ->
  2 * j < length (Fld p).
Proof.
  induction p; intros j q H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E. inversion H; subst j r.
    specialize (IHp j' q eq_refl). cbn [Fld length]. lia.
  - inversion H; subst j q. cbn [Fld length]. lia.
  - discriminate.
Qed.

Lemma Fld_succ_length : forall p j q, cview p = (j, Some q) ->
  length (Fld (Pos.succ p)) = length (Fld p).
Proof.
  intros p j q H. destruct (cview_some_F p j q H) as (H1 & H2).
  rewrite H1, H2, !app_length, !rep2_length. reflexivity.
Qed.

(** ** The field run's measure

    [tops p] is the all-ones numeral of [p]'s width; it is FIXED along the
    run (the width does not change until the field is full), so
    [tops p - p] counts the increments left and drops by one each time. *)

Fixpoint tops (p : positive) : positive :=
  match p with
  | xH => xH
  | xO q => xI (tops q)
  | xI q => xI (tops q)
  end.

Lemma tops_le : forall p, Pos.to_nat p <= Pos.to_nat (tops p).
Proof.
  induction p; cbn [tops]; rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO in *; lia.
Qed.

Lemma tops_lt : forall p j q, cview p = (j, Some q) ->
  Pos.to_nat p < Pos.to_nat (tops p).
Proof.
  induction p; intros j q H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E. inversion H; subst r.
    specialize (IHp j' q eq_refl).
    cbn [tops]. rewrite !Pos2Nat.inj_xI. lia.
  - pose proof (tops_le p). cbn [tops].
    rewrite Pos2Nat.inj_xO, Pos2Nat.inj_xI. lia.
  - discriminate.
Qed.

Lemma tops_succ : forall p j q, cview p = (j, Some q) ->
  tops (Pos.succ p) = tops p.
Proof.
  induction p; intros j q H; simpl in H.
  - destruct (cview p) as [j' r] eqn:E. inversion H; subst r.
    cbn [Pos.succ tops]. rewrite (IHp j' q eq_refl). reflexivity.
  - reflexivity.
  - discriminate.
Qed.

Definition gap (p : positive) : nat := Pos.to_nat (tops p) - Pos.to_nat p.

Lemma gap_succ : forall p j q, cview p = (j, Some q) -> gap (Pos.succ p) < gap p.
Proof.
  intros p j q H. unfold gap.
  rewrite (tops_succ p j q H), Pos2Nat.inj_succ.
  pose proof (tops_lt p j q H). lia.
Qed.

(** [Fpow n] is [2^n]: the field at value zero, [n] digits wide. *)
Fixpoint Fpow (n : nat) : positive :=
  match n with 0 => xH | S m => xO (Fpow m) end.

Lemma Fld_Fpow : forall n, Fld (Fpow n) = rep [S0; S0] n.
Proof. induction n; cbn [Fpow Fld rep app]; [reflexivity | rewrite IHn; reflexivity]. Qed.

Section Bin3Lap.

Variable tm : TM.
Variable qA qB qC qD : St.

(** The seven table entries the two rows SHARE.  [B0] is deliberately absent:
    it is the one place they differ, and [Hbc] is where it enters. *)
Hypothesis HA0 : tm qA S0 = Some (mkTrans S1 DR qB).
Hypothesis HA1 : tm qA S1 = Some (mkTrans S1 DL qC).
Hypothesis HB1 : tm qB S1 = Some (mkTrans S1 DR qA).
Hypothesis HC0 : tm qC S0 = Some (mkTrans S0 DL qC).
Hypothesis HC1 : tm qC S1 = Some (mkTrans S0 DL qD).
Hypothesis HD0 : tm qD S0 = Some (mkTrans S0 DR qA).
Hypothesis HD1 : tm qD S1 = Some (mkTrans S0 DR qD).

(** ** Units *)

Lemma uA0 : forall L R, csteps tm 1 (qA,(L,S0,R)) = Some (qB,(S1::L,chd R,ctl R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HA0.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uA1 : forall L R, csteps tm 1 (qA,(L,S1,R)) = Some (qC,(ctl L,chd L,S1::R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HA1.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uB1 : forall L R, csteps tm 1 (qB,(L,S1,R)) = Some (qA,(S1::L,chd R,ctl R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HB1.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uC0 : forall L R, csteps tm 1 (qC,(L,S0,R)) = Some (qC,(ctl L,chd L,S0::R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HC0.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uC1 : forall L R, csteps tm 1 (qC,(L,S1,R)) = Some (qD,(ctl L,chd L,S0::R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HC1.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uD0 : forall L R, csteps tm 1 (qD,(L,S0,R)) = Some (qA,(S0::L,chd R,ctl R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HD0.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma uD1 : forall L R, csteps tm 1 (qD,(L,S1,R)) = Some (qD,(S0::L,chd R,ctl R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HD1.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

(** ** The composite that absorbs [B0]

    The ONLY place the two rows differ, and they differ only in how many
    steps it takes.  Measured: every [B]-on-[S0] event of either row has an
    [S1] to its left, so this shape is the only one that ever occurs. *)

Hypothesis Hbc : forall L R, exists n, 0 < n /\
  csteps tm n (qB,(S1::L,S0,R)) = Some (qD,(ctl L,chd L,S0::S1::R)).

(** [qC] lives strictly inside the composite, so the visit witness for it has
    to come out of the same place.  Both rows supply it (row 1 at step 3 of
    four, row 2 at step 1 of two). *)
Hypothesis HbcC : forall L R, exists k c,
  csteps tm k (qB,(S1::L,S0,R)) = Some c /\ fst c = qC.

Lemma rep0_cons : forall d Y, S0 :: (rep [S0] d ++ Y) = rep [S0] (d + 1) ++ Y.
Proof.
  intros d Y. rewrite rep_add, <- app_assoc. cbn [rep app].
  rewrite rep_slide. reflexivity.
Qed.

(** ** The descent

    [qC] walks left over clear cells and stops on the first set one, which it
    clears; [qD] takes over one cell further down.  [k+2] steps for [k]
    clear cells: the [k] of them, the cell the walk started under, and the
    set cell itself. *)
Lemma phC : forall k L R,
  csteps tm (k + 2) (qC,(rep [S0] k ++ S1 :: L,S0,R))
    = Some (qD,(ctl L,chd L,rep [S0] (k + 2) ++ R)).
Proof.
  induction k as [|k IH]; intros L R.
  - replace (0 + 2) with (1 + 1) by lia.
    replace (rep [S0] 0 ++ S1 :: L) with (S1 :: L) by reflexivity.
    rewrite csteps_add, (uC0 (S1 :: L) R). cbn [chd ctl].
    rewrite (uC1 L (S0 :: R)). cbn [rep app]. reflexivity.
  - replace (rep [S0] (S k) ++ S1 :: L)
      with (S0 :: (rep [S0] k ++ S1 :: L)) by reflexivity.
    replace (S k + 2) with (1 + (k + 2)) by lia.
    rewrite csteps_add, (uC0 (S0 :: (rep [S0] k ++ S1 :: L)) R).
    cbn [chd ctl]. rewrite IH.
    replace (1 + (k + 2)) with (S (k + 2)) by lia.
    cbn [rep app]. rewrite rep_slide. reflexivity.
Qed.

(** ** [Hloop] at [k = 0]

    [qD] clears the cell it stands on, steps onto the marker in [qA], and
    [A1] hands the walk back to [qC] -- which is [phC] with one more clear
    cell than the run started with. *)
Lemma tick : forall d M R,
  csteps tm (d + 6) (qD,(rep [S0] d ++ S1 :: M,S1,rep [S0] 1 ++ S1 :: R))
    = Some (qD,(ctl M,chd M,rep [S0] (0 + 3 + d) ++ S1 :: R)).
Proof.
  intros d M R. cbn [rep app].
  replace (d + 6) with (1 + (1 + (1 + (d + 1 + 2)))) by lia.
  rewrite csteps_add, (uD1 (rep [S0] d ++ S1 :: M) (S0 :: S1 :: R)).
  cbn [chd ctl].
  rewrite csteps_add, (uD0 (S0 :: (rep [S0] d ++ S1 :: M)) (S1 :: R)).
  cbn [chd ctl].
  rewrite csteps_add, (uA1 (S0 :: (S0 :: (rep [S0] d ++ S1 :: M))) R).
  cbn [chd ctl].
  replace (S0 :: (rep [S0] d ++ S1 :: M))
    with (rep [S0] (d + 1) ++ S1 :: M)
    by (rewrite rep_add, <- app_assoc; cbn [rep app];
        rewrite rep_slide; reflexivity).
  rewrite (phC (d + 1) M (S1 :: R)).
  replace (d + 1 + 2) with (0 + 3 + d) by lia. reflexivity.
Qed.

(** ** The outward scan, and the step it cannot take

    [phOUT] crosses set digits: [A0] sets the pad, [B1] steps over the bit,
    two steps and two set cells a digit.  [mark] is what happens when the
    scan runs out of digits -- the MARKER sits where the next pad would be,
    so [A1] fires instead of [A0], [C1] clears the digit below it, and the
    head comes to rest ON a set cell.  That is what the cascade then eats
    two at a time, and it is why the cascade exists at all. *)

Lemma phOUT : forall i L X,
  csteps tm (i + i) (qA,(L,chd (rep [S0;S1] i ++ X),ctl (rep [S0;S1] i ++ X)))
    = Some (qA,(rep [S1] (2 * i) ++ L,chd X,ctl X)).
Proof.
  induction i as [|i IH]; intros L X.
  - cbn [rep app Nat.add]. reflexivity.
  - replace (rep [S0;S1] (S i) ++ X) with (S0 :: S1 :: (rep [S0;S1] i ++ X))
      by (cbn [rep app]; reflexivity).
    cbn [chd ctl].
    replace (S i + S i) with (1 + (1 + (i + i))) by lia.
    rewrite csteps_add, (uA0 L (S1 :: (rep [S0;S1] i ++ X))). cbn [chd ctl].
    rewrite csteps_add, (uB1 (S1 :: L) (rep [S0;S1] i ++ X)).
    rewrite IH.
    replace (2 * S i) with (2 * i + 2) by lia.
    rewrite rep_add, <- app_assoc. cbn [rep app]. reflexivity.
Qed.

Lemma mark : forall i L R,
  csteps tm (i + i + 5) (qD,(L,S0,rep [S0;S1] (S i) ++ S1 :: R))
    = Some (qD,(rep [S1] (2 * i) ++ S0 :: L,S1,rep [S0] 1 ++ S1 :: R)).
Proof.
  intros i L R.
  replace (i + i + 5) with (1 + ((S i + S i) + (1 + 1))) by lia.
  rewrite csteps_add, (uD0 L (rep [S0;S1] (S i) ++ S1 :: R)).
  rewrite csteps_add, (phOUT (S i) (S0 :: L) (S1 :: R)). cbn [chd ctl].
  replace (rep [S1] (2 * S i) ++ S0 :: L)
    with (S1 :: S1 :: (rep [S1] (2 * i) ++ S0 :: L))
    by (replace (2 * S i) with (S (S (2 * i))) by lia;
        cbn [rep app]; reflexivity).
  rewrite csteps_add, (uA1 (S1 :: S1 :: (rep [S1] (2 * i) ++ S0 :: L)) R).
  cbn [chd ctl].
  rewrite (uC1 (S1 :: (rep [S1] (2 * i) ++ S0 :: L)) (S1 :: R)).
  cbn [chd ctl rep app]. reflexivity.
Qed.

(** ** The two propositions, and their mutual descent

    [CORE j] is the lap's carry induction; [LOOP k] is the inner run.
    [CORE (S j)] needs [CORE j] and [LOOP j]; [LOOP (S k)] needs both at
    every level up to [k] -- the field's carries are strictly inside it
    ([Fld_carry_lt]) and the cascade's levels are strictly below it.  So one
    induction on the level proves them together. *)

Definition CORE (j : nat) : Prop :=
  forall M w, chd w = S0 -> chd (ctl w) = S0 ->
  exists n, 0 < n /\
  csteps tm n (qA,(M,chd (rep [S0;S1] j ++ w),ctl (rep [S0;S1] j ++ w)))
    = Some (qD,(ctl M,chd M,rep [S0] (2 * j + 1) ++ S1 :: ctl (ctl w))).

Definition LOOP (k : nat) : Prop :=
  forall d M R, exists n, 0 < n /\
  csteps tm n (qD,(rep [S0] d ++ S1 :: M,S1,rep [S0] (2 * k + 1) ++ S1 :: R))
    = Some (qD,(ctl M,chd M,rep [S0] (2 * k + 3 + d) ++ S1 :: R)).

Lemma core_0 : CORE 0.
Proof.
  intros M w Hw Hw2.
  destruct (Hbc M (ctl (ctl w))) as (n & Hn & Hrun).
  exists (1 + n). split; [lia |].
  replace (2 * 0 + 1) with 1 by lia. cbn [rep app]. rewrite Hw.
  rewrite csteps_add, (uA0 M (ctl w)), Hw2. exact Hrun.
Qed.

Lemma core_S : forall j, CORE j -> LOOP j -> CORE (S j).
Proof.
  intros j IH HL M w Hw Hw2.
  replace (rep [S0;S1] (S j) ++ w)
    with (S0 :: S1 :: (rep [S0;S1] j ++ w)) by (cbn [rep app]; reflexivity).
  cbn [chd ctl].
  destruct (IH (S1 :: S1 :: M) w Hw Hw2) as (n1 & Hn1 & H1).
  destruct (HL 0 M (ctl (ctl w))) as (n2 & Hn2 & H2).
  exists (1 + (1 + (n1 + n2))). split; [lia |].
  rewrite csteps_add, (uA0 M (S1 :: (rep [S0;S1] j ++ w))). cbn [chd ctl].
  rewrite csteps_add, (uB1 (S1 :: M) (rep [S0;S1] j ++ w)).
  rewrite csteps_add, H1. cbn [chd ctl].
  cbn [rep app] in H2.
  replace (2 * S j + 1) with (2 * j + 3 + 0) by lia.
  exact H2.
Qed.

Lemma loop_0 : LOOP 0.
Proof.
  intros d M R. exists (d + 6). split; [lia |].
  replace (2 * 0 + 1) with 1 by lia.
  replace (2 * 0 + 3 + d) with (0 + 3 + d) by lia.
  apply tick.
Qed.

(** The cascade, as one induction on the turn count: every turn is [LOOP]
    one level up, eating two set cells and laying down two clear ones.  The
    LAST turn is the one that carries [d]; every other carries none. *)
Lemma casc : forall t m d M R,
  (forall x, x <= m + t -> LOOP x) ->
  exists n, csteps tm n
      (qD,(rep [S1] (2 * t) ++ rep [S0] d ++ S1 :: M,S1,
           rep [S0] (2 * m + 1) ++ S1 :: R))
    = Some (qD,(ctl M,chd M,rep [S0] (2 * (m + t) + 3 + d) ++ S1 :: R)).
Proof.
  induction t as [|t IH]; intros m d M R HL.
  - destruct (HL m ltac:(lia) d M R) as (n & _ & Hrun).
    exists n. replace (2 * 0) with 0 by lia. cbn [rep app].
    replace (2 * (m + 0) + 3 + d) with (2 * m + 3 + d) by lia.
    exact Hrun.
  - destruct (HL m ltac:(lia) 0
      (rep [S1] (2 * t + 1) ++ rep [S0] d ++ S1 :: M) R) as (n1 & _ & H1).
    destruct (IH (S m) d M R ltac:(intros x Hx; apply HL; lia)) as (n2 & H2).
    exists (n1 + n2).
    replace (rep [S1] (2 * S t) ++ rep [S0] d ++ S1 :: M)
      with (S1 :: (rep [S1] (2 * t + 1) ++ rep [S0] d ++ S1 :: M))
      by (replace (2 * S t) with (S (2 * t + 1)) by lia;
          cbn [rep app]; reflexivity).
    cbn [rep app] in H1.
    rewrite csteps_add, H1.
    replace (rep [S1] (2 * t + 1) ++ rep [S0] d ++ S1 :: M)
      with (S1 :: (rep [S1] (2 * t) ++ rep [S0] d ++ S1 :: M))
      by (replace (2 * t + 1) with (S (2 * t)) by lia;
          cbn [rep app]; reflexivity).
    cbn [chd ctl].
    replace (2 * m + 3 + 0) with (2 * S m + 1) by lia.
    rewrite H2.
    replace (2 * (S m + t) + 3 + d) with (2 * (m + S t) + 3 + d) by lia.
    reflexivity.
Qed.

(** The field run: increments at ONE anchor until the field is full.  The
    measure is [gap] -- the distance to the all-ones numeral, which [tops]
    holds fixed along the run. *)
Lemma field_run : forall g w p L R,
  (forall j, j < w -> CORE j) ->
  gap p <= g ->
  length (Fld p) = 2 * w ->
  exists s, csteps tm s (qD,(L,S0,Fld p ++ S1 :: R))
          = Some (qD,(L,S0,rep [S0;S1] w ++ S1 :: R)).
Proof.
  induction g as [|g IH]; intros w p L R HC Hg Hlen;
    destruct (cview p) as [j r] eqn:E; destruct r as [q|].
  - exfalso. pose proof (tops_lt p j q E). unfold gap in Hg. lia.
  - destruct (cview_none_S p j E) as (i & Hi). subst j.
    pose proof (cview_none_F p i E) as HF.
    rewrite HF in Hlen. rewrite rep2_length in Hlen.
    exists 0. cbn [csteps]. rewrite HF.
    replace w with i by lia. reflexivity.
  - destruct (cview_some_F p j q E) as (H1 & H2).
    assert (Hj : j < w) by (pose proof (Fld_carry_lt p j q E); lia).
    destruct (HC j Hj (S0 :: L) (S0 :: S0 :: (Fld q ++ S1 :: R))
                 eq_refl eq_refl) as (n1 & _ & Hrun).
    destruct (IH w (Pos.succ p) L R HC
                ltac:(pose proof (gap_succ p j q E); lia)
                ltac:(rewrite (Fld_succ_length p j q E); exact Hlen))
      as (s & Hs).
    exists (1 + (n1 + s)).
    rewrite H1, <- app_assoc. cbn [app].
    rewrite csteps_add,
      (uD0 L (rep [S0;S1] j ++ S0 :: S0 :: (Fld q ++ S1 :: R))).
    rewrite csteps_add, Hrun. cbn [chd ctl].
    replace (rep [S0] (2 * j + 1) ++ S1 :: (Fld q ++ S1 :: R))
      with (Fld (Pos.succ p) ++ S1 :: R)
      by (rewrite H2, rep_dbl, rep_add, <- !app_assoc;
          cbn [rep app]; reflexivity).
    exact Hs.
  - destruct (cview_none_S p j E) as (i & Hi). subst j.
    pose proof (cview_none_F p i E) as HF.
    rewrite HF in Hlen. rewrite rep2_length in Hlen.
    exists 0. cbn [csteps]. rewrite HF.
    replace w with i by lia. reflexivity.
Qed.

(** [LOOP (S k)] = D1 ; the field run ; MARK ; the cascade.  Every level it
    calls is strictly below [S k]. *)
Lemma loop_S : forall k,
  (forall j, j <= k -> CORE j) -> (forall m, m <= k -> LOOP m) -> LOOP (S k).
Proof.
  intros k HC HL d M R.
  destruct (field_run (gap (Fpow (S k))) (S k) (Fpow (S k))
              (rep [S0] (d + 1) ++ S1 :: M) R
              (fun j Hj => HC j ltac:(lia)) (le_n _)
              ltac:(rewrite Fld_Fpow, rep2_length; reflexivity)) as (s & Hs).
  destruct (casc k 0 (d + 2) M R (fun x Hx => HL x ltac:(lia))) as (nc & Hc).
  exists (1 + (s + ((k + k + 5) + nc))). split; [lia |].
  replace (2 * S k + 1) with (S (2 * k + 2)) by lia. cbn [rep app].
  rewrite csteps_add,
    (uD1 (rep [S0] d ++ S1 :: M) (S0 :: (rep [S0] (2 * k + 2) ++ S1 :: R))).
  cbn [chd ctl]. rewrite rep0_cons.
  replace (rep [S0] (2 * k + 2)) with (Fld (Fpow (S k)))
    by (rewrite Fld_Fpow, rep_dbl; f_equal; lia).
  rewrite csteps_add, Hs.
  rewrite csteps_add, (mark k (rep [S0] (d + 1) ++ S1 :: M) R).
  rewrite rep0_cons.
  replace (d + 1 + 1) with (d + 2) by lia.
  replace (2 * 0 + 1) with 1 in Hc by lia.
  rewrite Hc.
  replace (2 * (0 + k) + 3 + (d + 2)) with (2 * S k + 3 + d) by lia.
  reflexivity.
Qed.

Lemma core_loop : forall n,
  (forall j, j <= n -> CORE j) /\ (forall m, m <= n -> LOOP m).
Proof.
  induction n as [|n [IHC IHL]].
  - split; intros x Hx; replace x with 0 by lia;
      [apply core_0 | apply loop_0].
  - split; intros x Hx; destruct (Nat.eq_dec x (S n)) as [->|Hne].
    + apply core_S; [apply IHC | apply IHL]; lia.
    + apply IHC. lia.
    + apply loop_S; assumption.
    + apply IHL. lia.
Qed.

Lemma core : forall j, CORE j.
Proof. intro j. destruct (core_loop j) as (H & _). apply H. lia. Qed.



(** The same walk, stopped at the composite's door: this is where [qB] and
    [qC] are witnessed, and it needs no [Hloop]. *)
Lemma coreB : forall j M w, chd w = S0 -> chd (ctl w) = S0 ->
  exists k L, csteps tm k
      (qA,(M,chd (rep [S0;S1] j ++ w),ctl (rep [S0;S1] j ++ w)))
    = Some (qB,(S1 :: L,S0,ctl (ctl w))).
Proof.
  induction j as [|j IH]; intros M w Hw Hw2.
  - cbn [rep app]. rewrite Hw.
    exists 1, M. rewrite (uA0 M (ctl w)), Hw2. reflexivity.
  - replace (rep [S0;S1] (S j) ++ w)
      with (S0 :: S1 :: (rep [S0;S1] j ++ w)) by (cbn [rep app]; reflexivity).
    cbn [chd ctl].
    destruct (IH (S1 :: S1 :: M) w Hw Hw2) as (k & L & H1).
    exists (1 + (1 + k)), L.
    rewrite csteps_add, (uA0 M (S1 :: (rep [S0;S1] j ++ w))).
    cbn [chd ctl].
    rewrite csteps_add, (uB1 (S1 :: M) (rep [S0;S1] j ++ w)).
    exact H1.
Qed.

(** ** The anchor family *)

Definition Cf (p : positive) : cconf := (qD,([],S0,Wp p)).

(** Both [cview] cases put the anchor in the SAME shape, and the difference
    between them is only which [w] the tail is: [S0::S0::Wp q] for an
    interior carry, [[]] for the overflow.  Both satisfy the two [chd]
    side conditions, so one instance of [core] closes both. *)
Lemma anchor_shape : forall p, exists j w,
  Wp p = rep [S0;S1] j ++ w /\ chd w = S0 /\ chd (ctl w) = S0 /\
  Wp (Pos.succ p) = rep [S0] (2 * j + 1) ++ S1 :: ctl (ctl w).
Proof.
  intro p. destruct (cview p) as [j r] eqn:E. destruct r as [q|].
  - destruct (cview_some_W p j q E) as (H1 & H2).
    exists j, (S0 :: S0 :: Wp q).
    split; [exact H1 |]. cbn [chd ctl].
    split; [reflexivity |]. split; [reflexivity |].
    rewrite H2, rep_dbl, rep_add, <- app_assoc.
    cbn [rep app]. reflexivity.
  - destruct (cview_none_W p j E) as (H1 & H2).
    exists j, []. rewrite app_nil_r.
    split; [exact H1 |]. cbn [chd ctl].
    split; [reflexivity |]. split; [reflexivity |].
    rewrite H2, rep_dbl, rep_add, <- app_assoc.
    cbn [rep app]. reflexivity.
Qed.

Lemma lapD : forall p,
  exists n c', csteps tm n (Cf p) = Some c'
               /\ lift c' = lift (Cf (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. unfold Cf.
  destruct (anchor_shape p) as (j & w & Hp & Hw & Hw2 & Hs).
  destruct (core j [S0] w Hw Hw2) as (n & Hn & Hrun).
  exists (1 + n). eexists. split.
  - rewrite csteps_add, Hp, (uD0 [] (rep [S0;S1] j ++ w)).
    exact Hrun.
  - cbn [ctl chd] in *. split; [| lia]. rewrite Hs. reflexivity.
Qed.

(** ** Visits *)

Hypothesis Hcover : forall q, q = qA \/ q = qB \/ q = qC \/ q = qD.

Lemma visD : forall p q,
  exists k c, csteps tm k (Cf p) = Some c /\ fst c = q.
Proof.
  intros p q. unfold Cf.
  destruct (anchor_shape p) as (j & w & Hp & Hw & Hw2 & _).
  destruct (Hcover q) as [-> | [-> | [-> | ->]]].
  - (* qA: one step off the anchor *)
    exists 1, (qA,([S0],chd (Wp p),ctl (Wp p))). split; [| reflexivity].
    apply (uD0 [] (Wp p)).
  - (* qB: the outward scan's stop *)
    destruct (coreB j [S0] w Hw Hw2) as (k & L & H1).
    exists (1 + k), (qB,(S1 :: L,S0,ctl (ctl w))). split; [| reflexivity].
    rewrite csteps_add, Hp, (uD0 [] (rep [S0;S1] j ++ w)). exact H1.
  - (* qC: strictly inside the composite *)
    destruct (coreB j [S0] w Hw Hw2) as (k & L & H1).
    destruct (HbcC L (ctl (ctl w))) as (k2 & c & H2 & Hq).
    exists (1 + (k + k2)), c. split; [| exact Hq].
    rewrite csteps_add, Hp, (uD0 [] (rep [S0;S1] j ++ w)).
    rewrite csteps_add, H1. exact H2.
  - exists 0, (qD,([],S0,Wp p)). split; reflexivity.
Qed.

(** ** The closer

    [Cf : positive -> cconf] fits with no offset, so this is the PLAIN
    [LapGlue.glue_neverqh] -- no arbitrary-index twin needed.  The theorem is
    NEVER-quasihalting because all four states occur in every lap of both
    rows (measured over 1,022 and 1,394 laps), which is [Hvis] verbatim. *)
Variable p0 : positive.
Hypothesis Hboot : exists t0, stepn tm t0 InitES = Some (lift (Cf p0)).

Theorem bin3_nqh : NeverQuasiHaltsSt tm.
Proof.
  apply (glue_neverqh tm Cf p0).
  - exact Hboot.
  - intros p _. apply lapD.
  - intros p q _. apply visD.
Qed.

End Bin3Lap.

(** * The two rows' [B0], and why one closer serves both

    [Hbc] and [HbcC] are the only things downstream of [B0], and each row
    discharges them from its own transition. *)

Section BcRows.

Variable tm : TM.
Variable qA qB qC qD : St.

Hypothesis HA1 : tm qA S1 = Some (mkTrans S1 DL qC).
Hypothesis HB1 : tm qB S1 = Some (mkTrans S1 DR qA).
Hypothesis HC1 : tm qC S1 = Some (mkTrans S0 DL qD).

Lemma vA1 : forall L R, csteps tm 1 (qA,(L,S1,R)) = Some (qC,(ctl L,chd L,S1::R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HA1.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma vB1 : forall L R, csteps tm 1 (qB,(L,S1,R)) = Some (qA,(S1::L,chd R,ctl R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HB1.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma vC1 : forall L R, csteps tm 1 (qC,(L,S1,R)) = Some (qD,(ctl L,chd L,S0::R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HC1.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

(** Row 1, [1RB1LC_1LB1RA_0LC0LD_0RA0RD]: [B0] turns back into [qB], which
    finds the set cell to its left, hands to [qA], and [qA] hands to [qC].
    Four steps. *)
Section RowSelfB.
Hypothesis HB0 : tm qB S0 = Some (mkTrans S1 DL qB).

Lemma vB0self : forall L R,
  csteps tm 1 (qB,(L,S0,R)) = Some (qB,(ctl L,chd L,S1::R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HB0.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma bc_selfB : forall L R, exists n, 0 < n /\
  csteps tm n (qB,(S1::L,S0,R)) = Some (qD,(ctl L,chd L,S0::S1::R)).
Proof.
  intros L R. exists 4. split; [lia |].
  replace 4 with (1 + (1 + (1 + 1))) by lia.
  rewrite csteps_add, (vB0self (S1 :: L) R). cbn [chd ctl].
  rewrite csteps_add, (vB1 L (S1 :: R)). cbn [chd ctl].
  rewrite csteps_add, (vA1 (S1 :: L) R). cbn [chd ctl].
  rewrite (vC1 L (S1 :: R)). reflexivity.
Qed.

Lemma bcC_selfB : forall L R, exists k c,
  csteps tm k (qB,(S1::L,S0,R)) = Some c /\ fst c = qC.
Proof.
  intros L R. exists 3, (qC,(L,S1,S1::R)). split; [| reflexivity].
  replace 3 with (1 + (1 + 1)) by lia.
  rewrite csteps_add, (vB0self (S1 :: L) R). cbn [chd ctl].
  rewrite csteps_add, (vB1 L (S1 :: R)). cbn [chd ctl].
  rewrite (vA1 (S1 :: L) R). cbn [chd ctl]. reflexivity.
Qed.
End RowSelfB.

(** Row 2, [1RB1LC_1LC1RA_0LC0LD_0RA0RD]: [B0] hands straight to [qC], which
    clears the set cell.  Two steps, same endpoint. *)
Section RowToC.
Hypothesis HB0 : tm qB S0 = Some (mkTrans S1 DL qC).

Lemma vB0toC : forall L R,
  csteps tm 1 (qB,(L,S0,R)) = Some (qC,(ctl L,chd L,S1::R)).
Proof.
  intros L R. cbn [csteps cstep]. rewrite HB0.
  cbn [t_next t_dir t_write ctape_move]. reflexivity.
Qed.

Lemma bc_toC : forall L R, exists n, 0 < n /\
  csteps tm n (qB,(S1::L,S0,R)) = Some (qD,(ctl L,chd L,S0::S1::R)).
Proof.
  intros L R. exists 2. split; [lia |].
  replace 2 with (1 + 1) by lia.
  rewrite csteps_add, (vB0toC (S1 :: L) R). cbn [chd ctl].
  rewrite (vC1 L (S1 :: R)). reflexivity.
Qed.

Lemma bcC_toC : forall L R, exists k c,
  csteps tm k (qB,(S1::L,S0,R)) = Some c /\ fst c = qC.
Proof.
  intros L R. exists 1, (qC,(L,S1,S1::R)). split; [| reflexivity].
  rewrite (vB0toC (S1 :: L) R). cbn [chd ctl]. reflexivity.
Qed.
End RowToC.

End BcRows.
