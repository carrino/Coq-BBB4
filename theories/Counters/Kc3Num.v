(** * Kc3Num: the KCOPY3 numeral, with a PACKED FRONTIER.

    The counter alphabet of `1RB1RC_1LA1RA_0RC1LD_1LB0LD` is three cells a
    digit -- `docs/RESIDUE_708_DIAGNOSIS.md` reads it as "each bit stored in
    three copies", and the extent law agrees (+9 cells per 8x steps).  But it
    is NOT [Counters/Alph_000_111_111.Ap_Alph_000_111_111], and the difference
    is not a phase or an offset: it is measured, over 250,013 consecutive
    anchor visits, by `tools/counters/kc3lap.py`, which reports

      Wk mismatches 0 / 250013      Ap mismatches 250013 / 250013

    The top TWO digits share four cells rather than six: the leading digit is
    the three-cell marker [S1;S1;S1] and the one below it is a SINGLE cell.
    Everything below that is three cells a digit.  (The same shape the SEP3
    pair in `RESIDUE_708_DIAGNOSIS.md` carries -- "the 2 most significant bits
    have no gap between them" -- one radix up.)  It is forced by the extent
    law: a [3n]-cell uniform word plus a marker does not fit in the [3n-1]
    cells the tape actually holds, so NO choice of anchor can expose [Ap].

    Hence a new fixpoint rather than a re-use.  What DOES transfer verbatim is
    the interface: the three decomposition lemmas below have exactly the shape
    [MonoCounter.cview_some_W]/[cview_none_W] have, so
    [Checkers/LapDecider.v]'s anchor glue consumes them unchanged.  The one
    structural difference is that [cview]'s [Some] case SPLITS: a carry that
    lands on the packed digit ([q0 = xH]) writes one cell where an interior
    carry writes three, so it is its own branch with its own lap constant.

    Axiom footprint: none (closed under the global context). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape MonoCounter.
Import ListNotations.

(** The anchor word, HEAD-OUTWARD (the counter grows leftward against a right
    wall, so this is the [cconf]'s LEFT list): the digits least-significant
    first, three cells each, then the packed top digit in one cell, then the
    three-cell marker. *)
Fixpoint Wk (p : positive) : list Sym :=
  match p with
  | xH => [S1]
  | xO q => match q with
            | xH => [S0; S1; S1; S1]
            | _  => [S0; S0; S0] ++ Wk q
            end
  | xI q => match q with
            | xH => [S1; S1; S1; S1]
            | _  => [S1; S1; S1] ++ Wk q
            end
  end.

(** The two unfolding lemmas.  Away from the frontier the recursion is the
    ordinary digit alphabet; [q <> xH] is exactly "the digit below is not the
    packed one". *)
Lemma Wk_xO : forall q, q <> xH -> Wk (xO q) = [S0; S0; S0] ++ Wk q.
Proof. destruct q; intros H; try reflexivity. congruence. Qed.

(** [xI] needs no side condition: at the frontier [[S1;S1;S1] ++ Wk xH] and
    [Wk (xI xH)] are the SAME list -- a set packed digit under the marker is
    indistinguishable from a fourth marker cell.  Only a CLEAR packed digit
    ([xO xH]) breaks the uniform recursion, which is why exactly one of these
    two lemmas carries a hypothesis. *)
Lemma Wk_xI : forall q, Wk (xI q) = [S1; S1; S1] ++ Wk q.
Proof. destruct q; reflexivity. Qed.

(** ** INTERIOR, away from the frontier *)

Lemma cview_some_Wk : forall p j q0, cview p = (j, Some q0) -> q0 <> xH ->
  Wk p = rep [S1; S1; S1] j ++ [S0; S0; S0] ++ Wk q0 /\
  Wk (Pos.succ p) = rep [S0; S0; S0] j ++ [S1; S1; S1] ++ Wk q0.
Proof.
  induction p as [p IHp | p IHp | ]; intros j q0 H Hq.
  - (* xI p *)
    cbn in H. destruct (cview p) as [j' r] eqn:E.
    inversion H; subst j r.
    destruct (IHp j' q0 eq_refl Hq) as (H1 & H2).
    split.
    + rewrite (Wk_xI p), H1; cbn [rep]; rewrite <- app_assoc; reflexivity.
    + cbn [Pos.succ]. rewrite (Wk_xO (Pos.succ p) (Pos.succ_not_1 p)), H2.
      cbn [rep]; rewrite <- app_assoc; reflexivity.
  - (* xO p *)
    cbn in H. inversion H; subst j q0.
    split; cbn [rep app].
    + exact (Wk_xO p Hq).
    + cbn [Pos.succ]. exact (Wk_xI p).
  - (* xH *) cbn in H; discriminate.
Qed.

(** ** FRONTIER: the carry lands ON the packed digit

    One cell changes where an interior carry changes three, and the marker
    above it is untouched.  This branch does not exist in a uniform digit
    alphabet; it is what the packed frontier costs. *)
Lemma cview_one_Wk : forall p j, cview p = (j, Some xH) ->
  Wk p = rep [S1; S1; S1] j ++ [S0; S1; S1; S1] /\
  Wk (Pos.succ p) = rep [S0; S0; S0] j ++ [S1; S1; S1; S1].
Proof.
  induction p as [p IHp | p IHp | ]; intros j H.
  - (* xI p *)
    cbn in H. destruct (cview p) as [j' r] eqn:E.
    inversion H; subst j r.
    destruct (IHp j' eq_refl) as (H1 & H2).
    split.
    + rewrite (Wk_xI p), H1; cbn [rep]; rewrite <- app_assoc; reflexivity.
    + cbn [Pos.succ]. rewrite (Wk_xO (Pos.succ p) (Pos.succ_not_1 p)), H2.
      cbn [rep]; rewrite <- app_assoc; reflexivity.
  - (* xO p *)
    cbn in H. inversion H; subst j p.
    split; reflexivity.
  - (* xH *) cbn in H; discriminate.
Qed.

(** ** OVERFLOW

    Every digit is set, so the whole field clears and the packed digit is
    re-created one level up: the word grows by exactly three cells, which is
    the [+9 per 8x] extent law at [j -> j+1] per power of two. *)

(** [cview p = (0, None)] never happens, so the overflow count always peels.
    ([LapCertGlue.cview_pos] is the same fact; it is re-proved here so this
    file stays inside [MonoCounter]'s closure.) *)
Lemma cview_none_S : forall p j, cview p = (j, None) -> exists j', j = S j'.
Proof.
  destruct p as [p | p | ]; cbn; intros j H.
  - destruct (cview p) as [jj r]. inversion H. exists jj; reflexivity.
  - discriminate.
  - inversion H. exists 0; reflexivity.
Qed.

Lemma cview_none_Wk : forall p j, cview p = (S j, None) ->
  Wk p = rep [S1; S1; S1] j ++ [S1] /\
  Wk (Pos.succ p) = rep [S0; S0; S0] j ++ [S0; S1; S1; S1].
Proof.
  induction p as [p IHp | p IHp | ]; intros j H.
  - (* xI p: the tail is itself an overflow word, one level down *)
    cbn in H. destruct (cview p) as [j' r] eqn:E.
    inversion H; subst j' r.
    destruct (cview_none_S p j E) as (j0 & Hj); subst j.
    destruct (IHp j0 eq_refl) as (H1 & H2).
    split.
    + rewrite (Wk_xI p), H1; cbn [rep]; rewrite <- app_assoc; reflexivity.
    + cbn [Pos.succ]. rewrite (Wk_xO (Pos.succ p) (Pos.succ_not_1 p)), H2.
      cbn [rep]; rewrite <- app_assoc; reflexivity.
  - (* xO p: cview is [Some] *) cbn in H; discriminate.
  - (* xH: the packed frontier, all set *)
    cbn in H. inversion H; subst j. split; reflexivity.
Qed.
