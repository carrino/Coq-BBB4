(** * DblCounter: the fixed-width reflected-Gray encoding driving the
    double_counter #9 (and the Gray-code sibling #37).

    #9 doubles its (10)-comb by running a j-bit reflected Gray-code
    counter down from G(2^j-1) to G(0)=0 (validated:
    tools/counters/lap9.py, ALL OK).  The counter lives in a
    fixed-width region right of the comb: [gbn w j] is the list of the
    low j Gray bits of [G w = w xor (w>>1)] (LSB first), [slotsf]
    lays each bit into a 3-cell slot [bit; 0; 0], and [grr w j] frames
    the slots with a leading pad [S0] and a trailing anchor [S1]:

      grr w j = S0 :: slotsf (gbn w j) ++ [S1].

    The macro lap chains [kg] gray-decrement mini-laps
    ([CReach.creach_iter]); each flips exactly the bit at [tz w]
    (trailing zeros of [w]) -- the reflected-Gray one-bit-change
    property -- which this file establishes structurally (via
    [Nat.odd]/[Nat.div2], no bitwise-xor algebra):

    - [gbn_even_hd]/[gbn_odd_hd]: the head Gray bit of [2q] / [S(2q)];
    - [grr_odd]: for [w] odd the flip is right at the comb end
      (slot 0), tail shared with [grr (w-1)];
    - [grr_even]: for [w] even the region peels one slot and recurses,
      exposing the [0^(r-1) 1] marker the machine's D-fill run climbs.

    No axioms. *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape.
Import ListNotations.

(** ** The Gray region *)

(** The low [j] Gray bits of [G w], LSB first: bit [k] is
    [w_k xor w_(k+1)], obtained by the [div2] recursion. *)
Fixpoint gbn (w j : nat) : list bool :=
  match j with
  | 0 => []
  | S j' => xorb (Nat.odd w) (Nat.odd (Nat.div2 w)) :: gbn (Nat.div2 w) j'
  end.

(** Each Gray bit becomes a 3-cell slot [bit; 0; 0]. *)
Fixpoint slotsf (bs : list bool) : list Sym :=
  match bs with
  | [] => []
  | b :: bs' => (if b then S1 else S0) :: S0 :: S0 :: slotsf bs'
  end.

(** The full region: leading pad, the slots, trailing anchor. *)
Definition grr (w j : nat) : list Sym :=
  S0 :: slotsf (gbn w j) ++ [S1].

(** Trailing zeros of [w] (0 for [w] odd or [w = 0], up to [fuel]). *)
Fixpoint tzf (fuel w : nat) : nat :=
  match fuel with
  | 0 => 0
  | S f => if Nat.odd w then 0 else S (tzf f (Nat.div2 w))
  end.

(** ** Sanity (validated against tools/counters/lap9.py gray_region) *)

Example gbn_6 : gbn 6 3 = [true; false; true]. Proof. reflexivity. Qed.
Example gbn_4 : gbn 4 3 = [false; true; true]. Proof. reflexivity. Qed.
Example gbn_7 : gbn 7 3 = [false; false; true]. Proof. reflexivity. Qed.
Example gbn_0 : gbn 0 3 = [false; false; false]. Proof. reflexivity. Qed.

Example grr_6 : grr 6 3
  = [S0; S1;S0;S0; S0;S0;S0; S1;S0;S0; S1]. Proof. reflexivity. Qed.

(** ** The head Gray bit of an even / odd value *)

Lemma gbn_even_hd : forall q j,
  gbn (2 * q) (S j) = Nat.odd q :: gbn q j.
Proof.
  intros q j. cbn [gbn].
  rewrite Nat.div2_double.
  rewrite (Nat.odd_mul 2 q). cbn [Nat.odd Nat.even].
  reflexivity.
Qed.

Lemma gbn_odd_hd : forall q j,
  gbn (S (2 * q)) (S j) = negb (Nat.odd q) :: gbn q j.
Proof.
  intros q j. cbn [gbn].
  rewrite Nat.div2_succ_double.
  rewrite Nat.odd_succ, (Nat.even_mul 2 q). cbn [Nat.even Nat.odd].
  rewrite xorb_true_l. reflexivity.
Qed.

(** ** Region decomposition around the flip slot *)

(** [w] odd: the flip is at slot 0 (right at the comb end); the tail
    [grr (w-1)] shares [gbn q] with [grr w] -- only the head bit flips
    ([G] changes one bit).  [w = S (2q)], [w - 1 = 2 q]. *)
Lemma grr_odd : forall q j,
  grr (S (2 * q)) (S j)
    = S0 :: (if negb (Nat.odd q) then S1 else S0)
         :: S0 :: S0 :: slotsf (gbn q j) ++ [S1]
  /\ grr (2 * q) (S j)
    = S0 :: (if Nat.odd q then S1 else S0)
         :: S0 :: S0 :: slotsf (gbn q j) ++ [S1].
Proof.
  intros q j. unfold grr. rewrite gbn_odd_hd, gbn_even_hd.
  cbn [slotsf]. split; reflexivity.
Qed.

(** [w] even: the region peels its slot 0 and recurses into
    [grr q].  When [q] is odd the peeled slot is the marker [S1];
    otherwise it is a low zero the D-fill climbs.  [w = 2 q]. *)
Lemma grr_even : forall q j,
  grr (2 * q) (S j)
    = S0 :: (if Nat.odd q then S1 else S0) :: S0 :: S0
         :: (slotsf (gbn q j) ++ [S1]).
Proof.
  intros q j. unfold grr. rewrite gbn_even_hd. cbn [slotsf]. reflexivity.
Qed.

(** The marker run: [tz]-many low zero slots peel to a [rep] the
    machine's D-fill run climbs in one translated cycle.  For
    [w = 2^(S r) * u] with [u] odd, slots 0..r-1 are zero and slot r
    is the marker. *)
Lemma slotsf_app : forall a b,
  slotsf (a ++ b) = slotsf a ++ slotsf b.
Proof.
  induction a as [| x a IH]; intros b; cbn [slotsf app].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma slotsf_repeat_false : forall n,
  slotsf (repeat false n) = rep [S0; S0; S0] n.
Proof.
  induction n as [| n IH]; cbn [slotsf repeat rep app].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** [gbn] of [2^(S r) * u] with [u] odd: [r] leading zero bits, then
    the marker [true] (slot [r], = [S r - 1]), then the odd core's
    Gray bits (the flip bit is that core's head). *)
Lemma gbn_marker : forall r u j, Nat.odd u = true ->
  gbn (2 ^ S r * u) (S r + j) = repeat false r ++ true :: gbn u j.
Proof.
  induction r as [| r IH]; intros u j Hu.
  - cbn [repeat app]. rewrite Nat.pow_1_r.
    replace (2 * u) with (2 * u) by lia.
    rewrite gbn_even_hd, Hu. reflexivity.
  - replace (2 ^ S (S r) * u) with (2 * (2 ^ S r * u))
      by (cbn [Nat.pow]; lia).
    replace (S (S r) + j) with (S (S r + j)) by lia.
    rewrite gbn_even_hd, IH by exact Hu.
    replace (Nat.odd (2 ^ S r * u)) with false.
    2:{ symmetry. rewrite Nat.odd_mul, Nat.odd_pow by lia.
        cbn [Nat.odd Nat.even]. reflexivity. }
    cbn [repeat app]. reflexivity.
Qed.

(** The corresponding tape: the D-fill run climbs [rep [S0;S0;S0] r]
    to the marker. *)
Lemma grr_even_marker : forall r u j, Nat.odd u = true ->
  grr (2 ^ S r * u) (S r + j)
    = S0 :: rep [S0; S0; S0] r ++ S1 :: S0 :: S0 :: slotsf (gbn u j) ++ [S1].
Proof.
  intros r u j Hu. unfold grr. rewrite gbn_marker by exact Hu.
  rewrite slotsf_app, slotsf_repeat_false. cbn [slotsf].
  rewrite <- app_assoc. reflexivity.
Qed.
