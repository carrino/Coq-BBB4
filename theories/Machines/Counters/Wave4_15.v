(** * Wave4_15: 1RB0RC_0LC1LB_0LD1LC_1RD0RA never quasihalts.

    BBB [wave4_counter] certificate #15.  Filed as "the mod-4 wave odometer"
    and sized as a port of [WaveCounter]'s parity layer; it is neither.  Read
    at the LEFT RECORD -- head on the leftmost visited cell, [StC], reading
    blank, left list empty -- the tape is

      1^lead 0 1^v0 0 1^v1 0 ... 0 1^vn 0        (blanks beyond)

    and John's reading of the bounce settles what it is: number the zero
    STRIPES [z0 = 0] (the anchor's own blank), [z(k+1)] the k-th after it,
    and take

      bit k  =  (z(k+1) + k) mod 2

    -- equivalently, bit [k] is 1 iff the number of 1s strictly left of that
    stripe is EVEN.  The top stripe-bit is always 0: it is the implicit
    leading 1 of a [positive].  With that reading ONE LAP IS [p -> p+1],
    with no exceptions -- the "spawn" of a new block is just the carry out of
    the top.  So #15 is a plain BINARY COUNTER, it takes [LapGlue]'s closer
    (the one [BCtr_28] uses), and there is no invariant to preserve and no
    mod-4 arithmetic to port: "binary increment terminates" is all the carry
    ever needed.

    The tape is a structural recursion on the positive,

      venc 2 = [2],  venc 3 = [3],  venc m = (m + (m/2 mod 2)) :: venc (m/2)
      lead   = 1 + (m mod 2)

    so [Cf15] needs no [2^k] arithmetic and no bit extraction.

    The lap is binary increment made physical.  [p] EVEN is the no-carry case
    and is a single 10-step window ([ruleA]) -- constant cost, no induction.
    [p] ODD is the carry, and it is

      entry5 . (out6^a . carry5)^j . out6^b . deposit
            . (cross7 . ret1^c)^j . exit1

    where [carry5] is John's "moves the line 2 left and continues on" and the
    deposit is his "moves it 1 left and it bounces" -- [A0 = 1RB] fills the
    line and bounces right into [StB], which walks back.  That walk-back is
    why the deposit is a SWEEP and not a fixed window.

    Every gadget below was checked against a CTape-faithful mirror before any
    Coq was written -- exhaustively, over every [(L,R)] with [|L|,|R| <= 4]
    ([tools/counters/lap15.py]) -- and the ASSEMBLY was replayed symbolically
    from those gadgets alone and diffed against the raw simulator for every
    [p] ([tools/counters/asm15.py]).  The sampled check that sufficed for the
    other counter boards would not have caught the deposit.

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import LapGlue.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB0RC_0LC1LB_0LD1LC_1RD0RA *)
Definition tm_15 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DR StC
  | StB, S0 => mk S0 DL StC | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S0 DL StD | StC, S1 => mk S1 DL StC
  | StD, S0 => mk S1 DR StD | StD, S1 => mk S0 DR StA
  end.

(** ** The single-step joints

    The transition table, one [reflexivity] each, stated through [chd]/[ctl]
    so they are uniform at the ends of the half-tape lists. *)

Lemma jcD : forall L R,
  csteps tm_15 1 (StC, (L, S0, R)) = Some (StD, (ctl L, chd L, S0 :: R)).
Proof. reflexivity. Qed.

Lemma jdR : forall L R,
  csteps tm_15 1 (StD, (L, S0, R)) = Some (StD, (S1 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

Lemma jdA : forall L R,
  csteps tm_15 1 (StD, (L, S1, R)) = Some (StA, (S0 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

Lemma jaB : forall L R,
  csteps tm_15 1 (StA, (L, S0, R)) = Some (StB, (S1 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

Lemma jaC : forall L R,
  csteps tm_15 1 (StA, (L, S1, R)) = Some (StC, (S0 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

Lemma jbB : forall L R,
  csteps tm_15 1 (StB, (L, S1, R)) = Some (StB, (ctl L, chd L, S1 :: R)).
Proof. reflexivity. Qed.

Lemma jbC : forall L R,
  csteps tm_15 1 (StB, (L, S0, R)) = Some (StC, (ctl L, chd L, S0 :: R)).
Proof. reflexivity. Qed.

(** [cons] forms, so the sweeps rewrite against [cbn]-normal shapes. *)
Lemma jdRc : forall L x R,
  csteps tm_15 1 (StD, (L, S0, x :: R)) = Some (StD, (S1 :: L, x, R)).
Proof. reflexivity. Qed.

Lemma jbBc : forall x L R,
  csteps tm_15 1 (StB, (x :: L, S1, R)) = Some (StB, (L, x, S1 :: R)).
Proof. reflexivity. Qed.

(** ** The gadgets

    Each is uniform in the surrounding tape and was checked exhaustively
    over every [(L,R)] with [|L|,|R| <= 4] before being written here. *)

(** [ruleA] is the whole no-carry lap: [p] even, one window, constant cost. *)
Lemma ruleA : forall R,
  csteps tm_15 10 (StC, ([], S0, S1 :: S0 :: S1 :: R))
  = Some (StC, ([], S0, S1 :: S1 :: S0 :: S1 :: S1 :: R)).
Proof. reflexivity. Qed.

(** The carry's entry, off the [1^2] lead. *)
Lemma entry5 : forall R,
  csteps tm_15 5 (StC, ([], S0, S1 :: S1 :: S0 :: R))
  = Some (StC, ([S0; S0; S1; S1], S0, R)).
Proof. reflexivity. Qed.

(** The outward unit: eats three 1s, hands one back -- net two cells per six
    steps.  A run of length [2k+1] therefore costs [6k] and leaves exactly
    one 1, which is the tape-level reason the stripe parities are what the
    counter reads. *)
Lemma out6 : forall L R,
  csteps tm_15 6 (StC, (S0 :: L, S0, S1 :: S1 :: S1 :: R))
  = Some (StC, (S0 :: S1 :: S1 :: L, S0, S1 :: R)).
Proof. reflexivity. Qed.

(** John's "moves the line 2 left and continues on": the scan crosses a
    stripe and carries.  It ends on [A1 = 0RC], which is why it continues. *)
Lemma carry5 : forall L R,
  csteps tm_15 5 (StC, (S0 :: L, S0, S1 :: S1 :: S0 :: R))
  = Some (StC, (S0 :: S0 :: S1 :: S1 :: L, S0, R)).
Proof. reflexivity. Qed.

(** The return unit, one step per cell. *)
Lemma ret1 : forall L R,
  csteps tm_15 1 (StC, (S1 :: L, S1, R)) = Some (StC, (L, S1, S1 :: R)).
Proof. reflexivity. Qed.

(** A stripe passes through the return sweep untouched. *)
Lemma cross7 : forall L R,
  csteps tm_15 7 (StC, (S0 :: S1 :: S1 :: L, S1, R))
  = Some (StC, (L, S1, S0 :: S1 :: S1 :: R)).
Proof. reflexivity. Qed.

(** ...and the last step lands on the new left record. *)
Lemma exit1 : forall R,
  csteps tm_15 1 (StC, ([], S1, R)) = Some (StC, ([], S0, S1 :: R)).
Proof. reflexivity. Qed.

(** ** The sweeps

    Inductions on the count with the tail universally quantified. *)

Lemma repeat_snoc : forall (x : Sym) k L,
  repeat x k ++ x :: L = repeat x (S k) ++ L.
Proof.
  induction k as [|k IH]; intro L; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

(** The debris [out6] lays: [k] copies of [1 1] behind the head. *)
Fixpoint lay (k : nat) (L : list Sym) : list Sym :=
  match k with 0 => L | S i => S1 :: S1 :: lay i L end.

Lemma lay_shift : forall k L, lay k (S1 :: S1 :: L) = S1 :: S1 :: lay k L.
Proof.
  induction k as [|k IH]; intro L; cbn [lay];
    [reflexivity | rewrite IH; reflexivity].
Qed.

(** [out6] iterated over a run of odd length [2k+1]. *)
Lemma out6s : forall k L R,
  csteps tm_15 (6 * k) (StC, (S0 :: L, S0, repeat S1 (2 * k + 1) ++ R))
  = Some (StC, (S0 :: lay k L, S0, S1 :: R)).
Proof.
  induction k as [|k IH]; intros L R.
  - reflexivity.
  - replace (6 * S k) with (6 + 6 * k) by lia.
    replace (2 * S k + 1) with (S (S (2 * k + 1))) by lia.
    cbn [repeat app]. rewrite csteps_add.
    replace (repeat S1 (2 * k + 1) ++ R)
       with (S1 :: repeat S1 (2 * k) ++ R)
       by (replace (2 * k + 1) with (S (2 * k)) by lia; reflexivity).
    rewrite out6.
    replace (S1 :: repeat S1 (2 * k) ++ R)
       with (repeat S1 (2 * k + 1) ++ R)
       by (replace (2 * k + 1) with (S (2 * k)) by lia; reflexivity).
    rewrite IH, lay_shift. reflexivity.
Qed.

(** [ret1] iterated: the return over a run. *)
Lemma ret1s : forall k L R,
  csteps tm_15 k (StC, (repeat S1 k ++ L, S1, R))
  = Some (StC, (L, S1, repeat S1 k ++ R)).
Proof.
  induction k as [|k IH]; intros L R.
  - reflexivity.
  - cbn [repeat app]. replace (S k) with (1 + k) by lia.
    rewrite csteps_add, ret1, IH, repeat_snoc. reflexivity.
Qed.

(** The deposit: John's "moves it 1 left and it bounces".  [A0 = 1RB] fills
    the stripe and bounces right into [StB], which walks back over the laid
    1s until it meets a 0.  That walk-back is why the deposit is not one
    window -- it is TWO, split by the symbol the bounce lands on, and each is
    uniform.  [dep0] is stated through [chd]/[ctl] so that the empty tail --
    which is the SPAWN, John's "pushes the right wall back one and makes
    another 0 stripe" -- is not a separate case. *)

Lemma dep0 : forall L R,
  chd R = S0 ->
  csteps tm_15 6 (StC, (S0 :: L, S0, S1 :: S0 :: R))
  = Some (StC, (S0 :: S1 :: S1 :: L, S1, S0 :: ctl R)).
Proof.
  intros L R H.
  replace 6 with (1 + (1 + (1 + (1 + (1 + 1))))) by lia.
  rewrite csteps_add, jcD. cbn [chd ctl].
  rewrite csteps_add, jdRc.
  rewrite csteps_add, jdRc.
  rewrite csteps_add, jdA. cbn [chd ctl].
  rewrite csteps_add, jaB, H.
  rewrite jbC. cbn [chd ctl].
  reflexivity.
Qed.

Lemma dep2 : forall L R,
  csteps tm_15 8 (StC, (S0 :: L, S0, S1 :: S0 :: S1 :: R))
  = Some (StC, (S1 :: L, S1, S0 :: S1 :: S1 :: R)).
Proof. reflexivity. Qed.

(** ** The abstract state: a positive, and the tape it names *)

Fixpoint wblocks (v : list nat) : list Sym :=
  match v with
  | [] => []
  | x :: t => repeat S1 x ++ S0 :: wblocks t
  end.

(** [pod p] is [p mod 2]: [xH] is 1, which is odd. *)
Definition pod (p : positive) : nat :=
  match p with xO _ => 0 | _ => 1 end.

Fixpoint venc (p : positive) : list nat :=
  match p with
  | xH => []
  | xO xH => [2]
  | xI xH => [3]
  | xO q => (2 * Pos.to_nat q + pod q) :: venc q
  | xI q => (2 * Pos.to_nat q + 1 + pod q) :: venc q
  end.

Definition Cf15 (p : positive) : cconf :=
  (StC, ([], S0, repeat S1 (1 + pod p)
                 ++ S0 :: wblocks (venc p))).
