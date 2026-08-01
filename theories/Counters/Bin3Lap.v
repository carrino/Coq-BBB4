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

(** ** The one open lemma

    Verified over an unknown context on both sides for [k = 0..5], [d = 0..3]
    on both rows (`tools/counters/bin3lem.py`); [tick] is its [k = 0] case.
    [k >= 1] is a descending-octave cascade, not a second carry induction --
    see this file's header and `docs/LADDER_PLAN.md` §4z. *)
Hypothesis Hloop : forall k d M R, exists n, 0 < n /\
  csteps tm n (qD,(rep [S0] d ++ S1 :: M,S1,rep [S0] (2 * k + 1) ++ S1 :: R))
    = Some (qD,(ctl M,chd M,rep [S0] (2 * k + 3 + d) ++ S1 :: R)).

(** ** The lap's own induction over the carry run

    The outward scan reads the counter's digits in pairs while they carry
    ([A0] sets the pad, [B1] steps over the set bit), so the carry run peels
    one digit at a time; what closes each level is [Hloop] at that level.
    The tail is handled through [chd]/[ctl] rather than a fixed [S0::S0::],
    which is what lets the OVERFLOW anchor -- whose two top cells are blanks
    the [cconf] does not carry -- be the SAME instance with [w = []], with no
    [lift_app_blank] anywhere. *)
Lemma core : forall j M w, chd w = S0 -> chd (ctl w) = S0 ->
  exists n, 0 < n /\
  csteps tm n (qA,(M,chd (rep [S0;S1] j ++ w),ctl (rep [S0;S1] j ++ w)))
    = Some (qD,(ctl M,chd M,rep [S0] (2 * j + 1) ++ S1 :: ctl (ctl w))).
Proof.
  induction j as [|j IH]; intros M w Hw Hw2.
  - (* base: set the stop digit and hand over to the composite *)
    destruct (Hbc M (ctl (ctl w))) as (n & Hn & Hrun).
    exists (1 + n). split; [lia |].
    replace (2 * 0 + 1) with 1 by lia. cbn [rep app]. rewrite Hw.
    rewrite csteps_add, (uA0 M (ctl w)), Hw2. exact Hrun.
  - (* step: cross one carrying digit, recurse, then close with Hloop *)
    replace (rep [S0;S1] (S j) ++ w)
      with (S0 :: S1 :: (rep [S0;S1] j ++ w)) by (cbn [rep app]; reflexivity).
    cbn [chd ctl].
    destruct (IH (S1 :: S1 :: M) w Hw Hw2) as (n1 & Hn1 & H1).
    destruct (Hloop j 0 M (ctl (ctl w))) as (n2 & Hn2 & H2).
    exists (1 + (1 + (n1 + n2))). split; [lia |].
    rewrite csteps_add, (uA0 M (S1 :: (rep [S0;S1] j ++ w))).
    cbn [chd ctl].
    rewrite csteps_add, (uB1 (S1 :: M) (rep [S0;S1] j ++ w)).
    rewrite csteps_add, H1. cbn [chd ctl].
    cbn [rep app] in H2.
    replace (2 * S j + 1) with (2 * j + 3 + 0) by lia.
    exact H2.
Qed.

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
