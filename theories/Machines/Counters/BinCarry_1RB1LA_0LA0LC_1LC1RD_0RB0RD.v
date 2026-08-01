(** * BinCarry_1RB1LA_0LA0LC_1LC1RD_0RB0RD: the machine never quasihalts.

    A core row `tools/closeout/residue_map.tsv` files as `QUAD` / `Kp` /
    "no interior chain", and the row LADDER_PLAN 4p measures with a constant
    SECOND difference on its arm -- which is why no widening of the ladder's
    `ARM_GRID` reaches it, and why 4t's emitter re-run refuses with "the carry
    ripple is not affine in the run length".  Both measurements are right and
    both are about the LADDER, which needs its arms affine.

    John reads the machine instead: *"a counter where moving the carry bit x
    spots over takes x bounces."*  That is exactly it, and it is the whole
    obstruction -- **the carry is an inner LOOP, not an arm**.  A hand board
    does not care: [LapGlue]'s lap premise existentially quantifies the step
    count, so a quadratic lap costs nothing at all.

    ** The family

    The anchor is the plainest one in the residue: a binary counter, low
    digit NEAREST the head, growing LEFTWARD, with the head on the blank just
    past its low end and nothing to the right --

      Cf p = (StA, (enc p ++ [S0], S0, []))
      enc xH = [S1]   enc (q~0) = S0 :: enc q   enc (q~1) = S1 :: enc q

    -- and it decodes to 0, 1, 2, 3, ... at consecutive anchor visits with no
    exception over 4,000 of them (`tools/counters/wallblock.py` located it;
    the value is the plain base-2 read of the left list).

    ** The lap, and where the quadratic comes from

    One increment with a carry of length [j] is

      2      turn onto the low digit
      j      walk left over the carry's ones           ([cycL] at [StA])
      1      step onto the first zero
      2      turn around into the cascade
      j^2+3j THE CASCADE: j bounces, the k-th costing 2k+4   (this is John's
             "x spots takes x bounces", and the whole quadratic)
      j+3    exit to the next anchor
      -----
      j^2 + 5j + 8   -- measured 8, 14, 22, 32, 44 at j = 0..4, exact

    and each bounce is one [cycR] out over the ones the last bounce restored,
    a four-step turn, and one [cycL] back over the zeros it just wrote.  The
    marker zero moves one cell right per bounce; after [j] of them the carry
    is done.  Every unit rule is [cycR]/[cycL] at unit length one.

    The OVERFLOW (the counter is all ones) is not a separate case: [Cf]
    spells the trailing blank explicitly, so `enc p ++ [S0]` is
    `rep [S1] j ++ S0 :: []` there and the same lemma applies with an empty
    tail.  The one blank that comes out spare at the far end is what
    [LapGlue]'s [lift] premise exists for.

    Every rule below was differentially validated against the raw simulator
    before any Coq was written: the three unit rules over ALL instantiations
    of their unknown left and right context, and the eight-piece chain over
    every carry length 1..6 against five different tails.

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Counters Require Import WTape LapGlue.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB1LA_0LA0LC_1LC1RD_0RB0RD *)
Definition tm_1RB1LA_0LA0LC_1LC1RD_0RB0RD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StA
  | StB, S0 => mk S0 DL StA | StB, S1 => mk S0 DL StC
  | StC, S0 => mk S1 DL StC | StC, S1 => mk S1 DR StD
  | StD, S0 => mk S0 DR StB | StD, S1 => mk S0 DR StD end.
Local Notation tm := tm_1RB1LA_0LA0LC_1LC1RD_0RB0RD.

Lemma chain2 : forall n1 n2 c c1 c2,
  csteps tm n1 c = Some c1 -> csteps tm n2 c1 = Some c2 ->
  csteps tm (n1 + n2) c = Some c2.
Proof. intros. rewrite csteps_add, H. assumption. Qed.

Ltac step_by L := eapply chain2; [apply L|].

(** ** 1. The three unit rules

    Each is a WINDOWED one-step run, so [WTape]'s repetition cycles carry it
    across a whole run in any context. *)

(** Walking left over the carry's ones, in [StA]: the cells do not change. *)
Lemma uWalk : forall k L R,
  csteps tm k (StA, (rep [S1] k ++ L, S1, R))
  = Some (StA, (L, S1, rep [S1] k ++ R)).
Proof.
  intros k L R.
  pose proof (cycL tm 1 StA S1 [S1] [] [S1] eq_refl k L R) as H.
  cbn [app] in H. rewrite Nat.mul_1_l in H. exact H.
Qed.

(** The bounce's outward leg, in [StD]: ones become zeros. *)
Lemma uOut : forall k L R,
  csteps tm k (StD, (L, S1, rep [S1] k ++ R))
  = Some (StD, (rep [S0] k ++ L, S1, R)).
Proof.
  intros k L R.
  pose proof (cycR tm 1 StD S1 [S1] [S0] eq_refl k L R) as H.
  rewrite Nat.mul_1_l in H. exact H.
Qed.

(** The bounce's return leg, in [StC]: zeros become ones again. *)
Lemma uBack : forall k L R,
  csteps tm k (StC, (rep [S0] k ++ L, S0, R))
  = Some (StC, (L, S0, rep [S1] k ++ R)).
Proof.
  intros k L R.
  pose proof (cycL tm 1 StC S0 [S0] [] [S1] eq_refl k L R) as H.
  cbn [app] in H. rewrite Nat.mul_1_l in H. exact H.
Qed.

(** ** 2. One bounce

    Out to the marker zero and back, moving it one cell right.  The [k = 0]
    case is the same four steps with both cycles empty, which is why the
    cost is [2k + 4] with no exception. *)

Lemma outD : forall k L rest,
  csteps tm (S k) (StC, (L, S1, rep [S1] k ++ S0 :: rest))
  = Some (StD, (rep [S0] k ++ S1 :: L, S0, rest)).
Proof.
  intros k L rest. destruct k as [|k].
  - reflexivity.
  - replace (S (S k)) with (1 + (k + 1)) by lia.
    cbn [rep app].
    step_by (eq_refl : csteps tm 1 (StC, (L, S1, S1 :: rep [S1] k ++ S0 :: rest))
                       = Some (StD, (S1 :: L, S1, rep [S1] k ++ S0 :: rest))).
    step_by (uOut k (S1 :: L) (S0 :: rest)).
    reflexivity.
Qed.

Lemma bounce : forall k m L,
  csteps tm (2 * k + 4)
    (StC, (L, S1, rep [S1] k ++ S0 :: rep [S1] (S m) ++ [S0]))
  = Some (StC, (L, S1, rep [S1] (S k) ++ S0 :: rep [S1] m ++ [S0])).
Proof.
  intros k m L.
  replace (2 * k + 4) with (S k + (1 + (1 + (k + 1)))) by lia.
  step_by (outD k L (rep [S1] (S m) ++ [S0])).
  cbn [rep app].
  step_by (eq_refl : csteps tm 1
             (StD, (rep [S0] k ++ S1 :: L, S0, S1 :: rep [S1] m ++ [S0]))
           = Some (StB, (S0 :: rep [S0] k ++ S1 :: L, S1,
                         rep [S1] m ++ [S0]))).
  step_by (eq_refl : csteps tm 1
             (StB, (S0 :: rep [S0] k ++ S1 :: L, S1, rep [S1] m ++ [S0]))
           = Some (StC, (rep [S0] k ++ S1 :: L, S0,
                         S0 :: rep [S1] m ++ [S0]))).
  step_by (uBack k (S1 :: L) (S0 :: rep [S1] m ++ [S0])).
  reflexivity.
Qed.

(** ** 3. The cascade: [n] bounces, and the quadratic is right here *)

Lemma cascade : forall n k L,
  csteps tm (n * n + 3 * n + 2 * k * n)
    (StC, (L, S1, rep [S1] k ++ S0 :: rep [S1] n ++ [S0]))
  = Some (StC, (L, S1, rep [S1] (k + n) ++ S0 :: [S0])).
Proof.
  induction n as [|n IH]; intros k L.
  - replace (0 * 0 + 3 * 0 + 2 * k * 0) with 0 by lia.
    rewrite Nat.add_0_r. cbn [rep app]. reflexivity.
  - replace (S n * S n + 3 * S n + 2 * k * S n)
      with ((2 * k + 4) + (n * n + 3 * n + 2 * (S k) * n)) by lia.
    step_by (bounce k n L).
    rewrite (IH (S k) L).
    replace (S k + n) with (k + S n) by lia. reflexivity.
Qed.

(** ** 4. The lap, at an arbitrary carry length and tail *)

Lemma carry : forall j l,
  csteps tm (j * j + 5 * j + 8)
    (StA, (rep [S1] j ++ S0 :: l, S0, []))
  = Some (StA, (rep [S0] j ++ S1 :: l, S0, [S0])).
Proof.
  intros j l.
  replace (j * j + 5 * j + 8)
    with (1 + (1 + (j + (1 + (1 + (1 + ((j * j + 3 * j + 2 * 0 * j)
                                        + (S j + (1 + 1)))))))))
    by lia.
  (* the turn onto the low digit *)
  step_by (eq_refl : csteps tm 1 (StA, (rep [S1] j ++ S0 :: l, S0, []))
           = Some (StB, (S1 :: rep [S1] j ++ S0 :: l, S0, []))).
  step_by (eq_refl : csteps tm 1 (StB, (S1 :: rep [S1] j ++ S0 :: l, S0, []))
           = Some (StA, (rep [S1] j ++ S0 :: l, S1, [S0]))).
  (* left over the carry's ones, then onto the zero that ends it *)
  step_by (uWalk j (S0 :: l) [S0]).
  step_by (eq_refl : csteps tm 1 (StA, (S0 :: l, S1, rep [S1] j ++ [S0]))
           = Some (StA, (l, S0, S1 :: rep [S1] j ++ [S0]))).
  (* turn around into the cascade *)
  step_by (eq_refl : csteps tm 1 (StA, (l, S0, S1 :: rep [S1] j ++ [S0]))
           = Some (StB, (S1 :: l, S1, rep [S1] j ++ [S0]))).
  step_by (eq_refl : csteps tm 1 (StB, (S1 :: l, S1, rep [S1] j ++ [S0]))
           = Some (StC, (l, S1, S0 :: rep [S1] j ++ [S0]))).
  (* the cascade, at [k = 0] *)
  step_by (cascade j 0 l).
  cbn [rep app plus].
  (* and out to the next anchor *)
  step_by (outD j l [S0]).
  reflexivity.
Qed.

(** ** 5. The numeral, and how a successor splits it *)

Fixpoint enc (p : positive) : list Sym :=
  match p with
  | xH => [S1]
  | xO q => S0 :: enc q
  | xI q => S1 :: enc q
  end.

(** The two shapes a binary successor takes: a carry that stops inside the
    numeral, and a carry that runs off the top.  Nothing else. *)
Lemma enc_succ : forall p,
  (exists j l, enc p = rep [S1] j ++ S0 :: l
               /\ enc (Pos.succ p) = rep [S0] j ++ S1 :: l)
  \/ (exists j, enc p = rep [S1] j
                /\ enc (Pos.succ p) = rep [S0] j ++ [S1]).
Proof.
  induction p as [q IH|q IH|].
  - (* p = q~1: the carry goes one digit further *)
    destruct IH as [(j & l & H1 & H2) | (j & H1 & H2)].
    + left. exists (S j), l. cbn [enc Pos.succ rep app].
      rewrite H1, H2. split; reflexivity.
    + right. exists (S j). cbn [enc Pos.succ rep app].
      rewrite H1, H2. split; reflexivity.
  - (* p = q~0: the carry stops here *)
    left. exists 0, (enc q). cbn [enc Pos.succ rep app].
    split; reflexivity.
  - (* p = 1 *)
    right. exists 1. cbn [enc Pos.succ rep app]. split; reflexivity.
Qed.

(** ** 6. The anchor, and the closer

    [Cf] spells the low end's trailing blank, which is what makes the
    overflow an instance of [carry] rather than a second lemma. *)

Definition Cf (p : positive) : cconf := (StA, (enc p ++ [S0], S0, [])).

Lemma lift_l_blank : forall q l h r,
  lift (q, (l ++ [S0], h, r)) = lift (q, (l, h, r)).
Proof.
  intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity.
Qed.

Lemma lap : forall p, exists n c',
  csteps tm n (Cf p) = Some c' /\ lift c' = lift (Cf (Pos.succ p)) /\ 0 < n.
Proof.
  intros p. unfold Cf.
  destruct (enc_succ p) as [(j & l & H1 & H2) | (j & H1 & H2)].
  - exists (j * j + 5 * j + 8), (StA, (rep [S0] j ++ S1 :: (l ++ [S0]), S0, [S0])).
    rewrite H1, <- app_assoc. cbn [app].
    split; [apply carry|]. split; [|lia].
    rewrite H2, <- app_assoc. cbn [app].
    apply (lift_app_blank StA _ S0 []).
  - exists (j * j + 5 * j + 8), (StA, (rep [S0] j ++ S1 :: [], S0, [S0])).
    rewrite H1.
    split; [apply carry|]. split; [|lia].
    rewrite H2, <- app_assoc. cbn [app].
    rewrite (lift_app_blank StA _ S0 []).
    rewrite <- (lift_l_blank StA (rep [S0] j ++ [S1]) S0 []).
    rewrite <- app_assoc. reflexivity.
Qed.

Lemma boot : csteps tm 8 c0 = Some (StA, ([S1], S0, [S0])).
Proof. vm_compute. reflexivity. Qed.

Lemma boot_lift : lift (StA, ([S1], S0, [S0])) = lift (Cf 1).
Proof.
  transitivity (lift (StA, ([S1], S0, []))).
  - apply (lift_app_blank StA [S1] S0 []).
  - unfold Cf. cbn [enc]. symmetry. apply (lift_l_blank StA [S1] S0 []).
Qed.

(** Every state recurs inside every lap: [StA] at 0 and [StB] at 1 are the
    turn onto the low digit, and [StC] at [j+5] / [StD] at [j+6] are the
    cascade's first bounce -- the offset depends on the anchor, which
    [LapGlue]'s visit premise allows. *)
Lemma visits : forall p q, exists k c,
  csteps tm k (Cf p) = Some c /\ fst c = q.
Proof.
  intros p q. unfold Cf.
  assert (Hs : exists j l, enc p ++ [S0] = rep [S1] j ++ S0 :: l).
  { destruct (enc_succ p) as [(j & l & H1 & _) | (j & H1 & _)].
    - exists j, (l ++ [S0]). rewrite H1, <- app_assoc. reflexivity.
    - exists j, []. rewrite H1. reflexivity. }
  destruct Hs as (j & l & Hs). rewrite Hs.
  assert (Hpre : csteps tm (1 + (1 + (j + (1 + (1 + 1)))))
                   (StA, (rep [S1] j ++ S0 :: l, S0, []))
                 = Some (StC, (l, S1, S0 :: rep [S1] j ++ [S0]))).
  { step_by (eq_refl : csteps tm 1 (StA, (rep [S1] j ++ S0 :: l, S0, []))
             = Some (StB, (S1 :: rep [S1] j ++ S0 :: l, S0, []))).
    step_by (eq_refl : csteps tm 1 (StB, (S1 :: rep [S1] j ++ S0 :: l, S0, []))
             = Some (StA, (rep [S1] j ++ S0 :: l, S1, [S0]))).
    step_by (uWalk j (S0 :: l) [S0]).
    step_by (eq_refl : csteps tm 1 (StA, (S0 :: l, S1, rep [S1] j ++ [S0]))
             = Some (StA, (l, S0, S1 :: rep [S1] j ++ [S0]))).
    step_by (eq_refl : csteps tm 1 (StA, (l, S0, S1 :: rep [S1] j ++ [S0]))
             = Some (StB, (S1 :: l, S1, rep [S1] j ++ [S0]))).
    reflexivity. }
  destruct q.
  - exists 0, (StA, (rep [S1] j ++ S0 :: l, S0, [])). split; reflexivity.
  - exists 1, (StB, (S1 :: rep [S1] j ++ S0 :: l, S0, [])).
    split; reflexivity.
  - exists (1 + (1 + (j + (1 + (1 + 1))))),
           (StC, (l, S1, S0 :: rep [S1] j ++ [S0])).
    split; [exact Hpre | reflexivity].
  - exists ((1 + (1 + (j + (1 + (1 + 1))))) + 1),
           (StD, (S1 :: l, S0, rep [S1] j ++ [S0])).
    split; [|reflexivity].
    eapply chain2; [exact Hpre | reflexivity].
Qed.

Theorem nqh_1RB1LA_0LA0LC_1LC1RD_0RB0RD :
  NeverQuasiHaltsSt tm_1RB1LA_0LA0LC_1LC1RD_0RB0RD.
Proof.
  apply (glue_neverqh tm Cf 1%positive).
  - exists 8. rewrite <- lift_c0.
    rewrite (csteps_lift _ _ _ _ boot), boot_lift. reflexivity.
  - intros p _. apply lap.
  - intros p q _. apply visits.
Qed.
