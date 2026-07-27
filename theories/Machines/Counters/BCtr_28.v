(** * BCtr_28: 1RB1LC_1LC1RD_1LA0LC_0RD0RB never quasihalts.

    BBB [blockdbl_counter] certificate #28, the third of the family --
    and, like #11 and #13, a BOUNCER COUNTER once you sample the right
    phase.  BBB models it as a solid block doubling
    (D(j) = 1 0^z 1^m, m = 2^(j+1)-1 -> 2m+1, z = 2j -> z+2), one
    macro lap costing 12*4^n + 6*2^n - 2 steps; docs/HOLDOUTS_WAVE14.md
    filed it with #11/#13 as a nested-lap job.

    Sampled at StA on the junction cell the tape is

      <binary counter of value v, low digit NEAREST> A(0) 1^(2v)

    -- a bouncer of length 2v, affine in the counter's value, with the
    counter on the LEFT this time.  John: "it just switches states on
    the way out and back to make stripes" -- StB/StD alternate outward
    laying [0;1] pairs, StC/StA alternate back turning them into ones.
    One lap is

      S(v) -->+ S(v+1)   in   8v + 4*carry(v) + 10 steps.

    Three differences from BCtr_11/BCtr_13, which is why this file does
    not reuse [BCtrCounter]'s section:

      - the counter sits on the LEFT of the head, not the right;
      - a digit is [b;b] ([00] = 0, [11] = 1), not [S0;b];
      - the bouncer is a run of ONES, and one lap is TWO half-bounces
        (the counter step happens between them), so the bouncer grows
        by 2 rather than 3.

    What carries over verbatim is the reason the counter is cheap: the
    walk stops at the first digit-0 pair, and a pair of BLANK cells
    past the top digit is a digit-0 pair, so overflow and interior
    carry are the same rule ([ctr28] has one base case for both).

    Every statement was validated cell-for-cell against the raw
    simulator (all 512 counter words of length <= 9, bouncers to
    v = 511) before any Coq was written.

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import LapGlue BCtrCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB1LC_1LC1RD_1LA0LC_0RD0RB *)
Definition tm_28 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StC
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S1 DL StA | StC, S1 => mk S0 DL StC
  | StD, S0 => mk S0 DR StD | StD, S1 => mk S0 DR StB
  end.

(** ** The counter word

    [cval], [carry], [crest], [incr], [bits] and their lemmas are
    [BCtrCounter]'s -- they are about the WORD, not the encoding.  Only
    the encoding differs: here a digit is two copies of itself. *)

Fixpoint encw (w : list bool) : list Sym :=
  match w with
  | [] => []
  | b :: t => (if b then S1 else S0) :: (if b then S1 else S0) :: encw t
  end.

(** ** The bounce

    [out2]: two steps eat two cells of bouncer and lay one [0;1] stripe
    behind the head.  [back2]: two steps eat one stripe and lay two
    ones ahead.  Both leave everything beyond untouched, which is what
    lets the counter ride along unread. *)

Lemma out2 : forall L R,
  csteps tm_28 2 (StB, (L, S1, S1 :: R))
  = Some (StB, (S0 :: S1 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

Lemma back2 : forall L R,
  csteps tm_28 2 (StC, (S1 :: L, S0, R))
  = Some (StC, (ctl L, chd L, S1 :: S1 :: R)).
Proof. reflexivity. Qed.

(** Single-step gadgets, used so the compositions rewrite rather than
    [change] (a [change] to [Some _] leaves an unreduced [match]). *)
Lemma stepA0 : forall M R,
  csteps tm_28 1 (StA, (M, S0, R)) = Some (StB, (S1 :: M, chd R, ctl R)).
Proof. reflexivity. Qed.

Lemma stepC0 : forall N R,
  csteps tm_28 1 (StC, (S0 :: N, S0, R)) = Some (StA, (N, S0, S1 :: R)).
Proof. reflexivity. Qed.

Lemma stepD2 : forall N R,
  csteps tm_28 2 (StD, (N, S0, S1 :: R))
  = Some (StB, (S0 :: S0 :: N, chd R, ctl R)).
Proof. reflexivity. Qed.

Lemma carry2 : forall M R,
  csteps tm_28 2 (StC, (S1 :: S1 :: M, S1, R))
  = Some (StC, (M, S1, S0 :: S0 :: R)).
Proof. reflexivity. Qed.

(** ...and the two steps that walk back over the zeros that carry
    walk laid.  This is why one carried digit costs 4, not 2: the
    debris has to be re-crossed, which is exactly what leaves the
    bouncer untouched. *)
Lemma dwalk2 : forall N R,
  csteps tm_28 2 (StD, (N, S0, S0 :: S0 :: R))
  = Some (StD, (S0 :: S0 :: N, S0, R)).
Proof. reflexivity. Qed.

(** Out and back over a bouncer of [2k] cells: ONE induction covers the
    whole half-bounce.  The left context [L] is arbitrary, so the
    counter never enters the argument. *)
Lemma halfbnc : forall k L,
  csteps tm_28 (4 * k + 1)
    (StB, (L, chd (repeat S1 (2 * k)), ctl (repeat S1 (2 * k))))
  = Some (StC, (ctl L, chd L, repeat S1 (2 * k + 1))).
Proof.
  induction k as [|k IH]; intros L.
  - reflexivity.
  - replace (4 * S k + 1) with (2 + ((4 * k + 1) + 2)) by lia.
    replace (2 * S k) with (S (S (2 * k))) by lia.
    change (repeat S1 (S (S (2 * k)))) with (S1 :: S1 :: repeat S1 (2 * k)).
    change (chd (S1 :: S1 :: repeat S1 (2 * k))) with S1.
    change (ctl (S1 :: S1 :: repeat S1 (2 * k))) with (S1 :: repeat S1 (2 * k)).
    rewrite csteps_add, out2, csteps_add, IH.
    change (ctl (S0 :: S1 :: L)) with (S1 :: L).
    change (chd (S0 :: S1 :: L)) with S0.
    rewrite back2.
    replace (2 * S k + 1) with (S (S (2 * k + 1))) by lia.
    reflexivity.
Qed.

(** The first half-bounce, from the anchor: the bouncer grows by one
    and the head comes to rest on its first cell in StC. *)
Lemma bnc1 : forall v M,
  csteps tm_28 (4 * v + 2) (StA, (M, S0, repeat S1 (2 * v)))
  = Some (StC, (M, S1, repeat S1 (2 * v + 1))).
Proof.
  intros v M.
  replace (4 * v + 2) with (1 + (4 * v + 1)) by lia.
  rewrite csteps_add, stepA0, halfbnc. reflexivity.
Qed.

(** The second half-bounce, after the counter step. *)
Lemma bnc2 : forall u N,
  csteps tm_28 (4 * u + 4) (StD, (N, S0, repeat S1 (2 * u + 1)))
  = Some (StA, (N, S0, repeat S1 (2 * u + 2))).
Proof.
  intros u N.
  replace (4 * u + 4) with (2 + ((4 * u + 1) + 1)) by lia.
  replace (2 * u + 1) with (S (2 * u)) by lia.
  change (repeat S1 (S (2 * u))) with (S1 :: repeat S1 (2 * u)).
  rewrite csteps_add, stepD2, csteps_add, halfbnc.
  change (ctl (S0 :: S0 :: N)) with (S0 :: N).
  change (chd (S0 :: S0 :: N)) with S0.
  rewrite stepC0.
  replace (2 * u + 2) with (S (2 * u + 1)) by lia.
  reflexivity.
Qed.

(** ** The counter step

    Between the two half-bounces the head walks LEFT through the
    trailing digit-1 pairs, sets the first digit-0 pair, and walks the
    zeros it laid back off to the right.  The bouncer comes out
    untouched -- the walk's debris exactly cancels.

    ONE induction, with one base case covering both a real digit-0 pair
    and the blank pair past the top digit. *)
Lemma ctr28 : forall w R,
  csteps tm_28 (4 * carry w + 4) (StC, (encw w, S1, R))
  = Some (StD, (encw (incr w), S0, R)).
Proof.
  induction w as [|b t IH]; intros R.
  - reflexivity.
  - destruct b.
    + change (encw (true :: t)) with (S1 :: S1 :: encw t).
      change (encw (incr (true :: t))) with (S0 :: S0 :: encw (incr t)).
      change (carry (true :: t)) with (S (carry t)).
      replace (4 * S (carry t) + 4) with (2 + ((4 * carry t + 4) + 2)) by lia.
      rewrite csteps_add, carry2, csteps_add, IH, dwalk2. reflexivity.
    + reflexivity.
Qed.

(** ** The lap *)

Definition anchor28 (w : list bool) : cconf :=
  (StA, (encw w, S0, repeat S1 (2 * cval w))).

Lemma lap28 : forall w,
  csteps tm_28 (8 * cval w + 4 * carry w + 10) (anchor28 w)
  = Some (anchor28 (incr w)).
Proof.
  intro w. unfold anchor28.
  replace (8 * cval w + 4 * carry w + 10)
     with ((4 * cval w + 2) + ((4 * carry w + 4) + (4 * cval w + 4))) by lia.
  rewrite csteps_add, bnc1, csteps_add, ctr28, bnc2, cval_incr.
  replace (2 * S (cval w)) with (2 * cval w + 2) by lia.
  reflexivity.
Qed.

(** ** Visits: all four states inside one lap *)
Lemma vis28 : forall w q,
  exists k c, csteps tm_28 k (anchor28 w) = Some c /\ fst c = q.
Proof.
  intros w q. destruct q.
  - exists 0. eexists. split; reflexivity.
  - exists 1. eexists. split; [reflexivity | reflexivity].
  - exists (4 * cval w + 2). eexists. split.
    + unfold anchor28. rewrite bnc1. reflexivity.
    + reflexivity.
  - exists ((4 * cval w + 2) + (4 * carry w + 4)). eexists. split.
    + unfold anchor28. rewrite csteps_add, bnc1, ctr28. reflexivity.
    + reflexivity.
Qed.

(** ** Boot and the theorem *)

Definition Cc28 (p : positive) : cconf := anchor28 (bits p).

Lemma boot28 : exists t0, stepn tm_28 t0 InitES = Some (lift (Cc28 1)).
Proof.
  exists 10.
  assert (H : match csteps tm_28 10 c0 with
              | Some c => ceqb c (Cc28 1)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_28 10 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

(** #28 never quasihalts: bbchallenge 1RB1LC_1LC1RD_1LA0LC_0RD0RB. *)
Theorem nqh_1RB1LC_1LC1RD_1LA0LC_0RD0RB : NeverQuasiHaltsSt tm_28.
Proof.
  apply (glue_neverqh tm_28 Cc28 1).
  - exact boot28.
  - intros p _. unfold Cc28. rewrite bits_succ.
    exists (8 * cval (bits p) + 4 * carry (bits p) + 10),
           (anchor28 (incr (bits p))).
    split; [apply lap28 | split; [reflexivity | lia]].
  - intros p q _. apply vis28.
Qed.

Theorem tm_28_nonhalt : NonHalt tm_28.
Proof. apply never_qh_nonhalt, nqh_1RB1LC_1LC1RD_1LA0LC_0RD0RB. Qed.
