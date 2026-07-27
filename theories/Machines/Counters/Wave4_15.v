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

(** ** The outward phase

    Each carried block costs [out6^a . carry5]: a block of EVEN length
    [2a+2] is eaten two cells at a time until two remain, and [carry5] --
    John's "moves the line 2 left and continues on" -- crosses the stripe and
    carries.  The deposit block is the first ODD one, which is where the
    scan stops.  One induction over the carried blocks. *)

Fixpoint owtape (l : list nat) (R : list Sym) : list Sym :=
  match l with
  | [] => R
  | a :: t => repeat S1 (2 * a + 2) ++ S0 :: owtape t R
  end.

Fixpoint owcost (l : list nat) : nat :=
  match l with [] => 0 | a :: t => (6 * a + 5) + owcost t end.

Fixpoint owdeb (l : list nat) (M : list Sym) : list Sym :=
  match l with [] => M | a :: t => owdeb t (S0 :: S1 :: S1 :: lay a M) end.

Lemma outward : forall l M R,
  csteps tm_15 (owcost l) (StC, (S0 :: M, S0, owtape l R))
  = Some (StC, (S0 :: owdeb l M, S0, R)).
Proof.
  induction l as [|a t IH]; intros M R.
  - reflexivity.
  - cbn [owcost owtape owdeb].
    replace (repeat S1 (2 * a + 2) ++ S0 :: owtape t R)
       with (repeat S1 (2 * a + 1) ++ S1 :: S0 :: owtape t R)
       by (replace (2 * a + 2) with (S (2 * a + 1)) by lia;
           rewrite <- repeat_snoc; reflexivity).
    replace (6 * a + 5 + owcost t) with (6 * a + (5 + owcost t)) by lia.
    rewrite csteps_add, out6s.
    rewrite csteps_add, carry5, IH. reflexivity.
Qed.

(** ** The return sweep

    After the deposit the head walks back over the debris the outward phase
    laid, and that walk is ONE structural recursion: [cross7] eats a stripe
    group [S0 S1 S1], [ret1] eats a single 1, and [exit1] lands on the new
    left record.  The outward and return phases are therefore SEQUENTIAL
    inductions over the same shape, not nested ones. *)

Inductive Deb : list Sym -> Prop :=
| DebN : Deb []
| Deb1 : forall D, Deb D -> Deb (S1 :: D)
| DebG : forall D, Deb D -> Deb (S0 :: S1 :: S1 :: D).

Fixpoint bcost (D : list Sym) : nat :=
  match D with
  | S0 :: S1 :: S1 :: t => 7 + bcost t
  | S1 :: t => 1 + bcost t
  | _ => 1
  end.

Fixpoint back (D R : list Sym) : list Sym :=
  match D with
  | S0 :: S1 :: S1 :: t => back t (S0 :: S1 :: S1 :: R)
  | S1 :: t => back t (S1 :: R)
  | _ => S1 :: R
  end.

(** The debris the outward phase lays is [Deb]-shaped, which is what lets
    the return sweep consume it. *)
Lemma lay_Deb : forall a M, Deb M -> Deb (lay a M).
Proof.
  induction a as [|a IH]; intros M H; cbn [lay];
    [exact H | apply Deb1, Deb1, IH, H].
Qed.

Lemma owdeb_Deb : forall l M, Deb M -> Deb (owdeb l M).
Proof.
  induction l as [|a t IH]; intros M H; cbn [owdeb].
  - exact H.
  - apply IH, DebG, lay_Deb, H.
Qed.

Lemma backsweep : forall D, Deb D -> forall R,
  csteps tm_15 (bcost D) (StC, (D, S1, R)) = Some (StC, ([], S0, back D R)).
Proof.
  induction 1 as [|D HD IH|D HD IH]; intro R.
  - apply exit1.
  - cbn [bcost back]. rewrite csteps_add, ret1, IH. reflexivity.
  - cbn [bcost back]. rewrite csteps_add, cross7, IH. reflexivity.
Qed.

(** ** What the return sweep reconstructs

    [back] is a pure list computation, so what the debris turns back into is
    provable without touching the machine.  These two lemmas push [back]
    through the two shapes the outward phase builds. *)

Lemma back_lay : forall a M R,
  back (lay a M) R = back M (repeat S1 (2 * a) ++ R).
Proof.
  induction a as [|a IH]; intros M R; cbn [lay].
  - reflexivity.
  - cbn [back]. rewrite IH. f_equal.
    replace (2 * S a) with (S (S (2 * a))) by lia.
    rewrite <- repeat_snoc, <- repeat_snoc. reflexivity.
Qed.

Fixpoint bta (l : list nat) (R : list Sym) : list Sym :=
  match l with
  | [] => R
  | a :: t => repeat S1 (2 * a) ++ S0 :: S1 :: S1 :: bta t R
  end.

Lemma back_owdeb : forall l M R,
  back (owdeb l M) R = back M (bta l R).
Proof.
  induction l as [|a t IH]; intros M R; cbn [owdeb bta].
  - reflexivity.
  - rewrite IH. cbn [back]. rewrite back_lay. reflexivity.
Qed.

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

(** The two shapes of an anchor.  [pod] is 0 on [xO] and 1 on [xI], so the
    lead is one cell on an even [p] and two on an odd one; both are
    [reflexivity], which keeps every later rewrite off [cbn]. *)

Lemma Cf15_even : forall r,
  Cf15 (xO r) = (StC, ([], S0, S1 :: S0 :: wblocks (venc (xO r)))).
Proof. reflexivity. Qed.

Lemma Cf15_odd : forall q,
  Cf15 (xI q) = (StC, ([], S0, S1 :: S1 :: S0 :: wblocks (venc (xI q)))).
Proof. reflexivity. Qed.

(** ** The encoding's arithmetic

    [venc] is a [Fixpoint] with two literal base cases, so it is unfolded
    through these two equations rather than by [cbn] -- [cbn] on [venc (xO
    (xI s))] leaves the inner match half-reduced. *)

Lemma venc_xO : forall q, q <> xH ->
  venc (xO q) = (2 * Pos.to_nat q + pod q) :: venc q.
Proof.
  destruct q as [s|s|]; intro H;
    [reflexivity | reflexivity | exfalso; apply H; reflexivity].
Qed.

Lemma venc_xI : forall q, q <> xH ->
  venc (xI q) = (2 * Pos.to_nat q + 1 + pod q) :: venc q.
Proof.
  destruct q as [s|s|]; intro H;
    [reflexivity | reflexivity | exfalso; apply H; reflexivity].
Qed.

(** Rule A's whole arithmetic: [xO r -> xI r] bumps the HEAD block by one
    and leaves the tail alone.  The head is at least 2, so it splits. *)
Lemma venc_bump : forall r, exists c t,
  venc (xO r) = S c :: t /\ venc (xI r) = S (S c) :: t.
Proof.
  intro r. destruct r as [s|s|].
  - exists (2 * Pos.to_nat (xI s)), (venc (xI s)).
    rewrite (venc_xO (xI s)) by discriminate.
    rewrite (venc_xI (xI s)) by discriminate.
    cbn [pod]. split; f_equal; lia.
  - pose proof (Pos2Nat.is_pos (xO s)).
    exists (2 * Pos.to_nat (xO s) - 1), (venc (xO s)).
    rewrite (venc_xO (xO s)) by discriminate.
    rewrite (venc_xI (xO s)) by discriminate.
    cbn [pod]. split; f_equal; lia.
  - exists 1, []. split; reflexivity.
Qed.

(** ** The even lap

    [p] even is one [ruleA] window: the lead goes [1 -> 2] and the frontier
    block gains a 1.  No induction, no scan. *)

Lemma Cf15_evenc : forall r c t, venc (xO r) = S c :: t ->
  Cf15 (xO r)
  = (StC, ([], S0, S1 :: S0 :: S1 :: (repeat S1 c ++ S0 :: wblocks t))).
Proof. intros r c t E. rewrite Cf15_even, E. reflexivity. Qed.

Lemma Cf15_oddc : forall r c t, venc (xI r) = S (S c) :: t ->
  Cf15 (xI r)
  = (StC, ([], S0, S1 :: S1 :: S0 :: S1 :: S1
                   :: (repeat S1 c ++ S0 :: wblocks t))).
Proof. intros r c t E. rewrite Cf15_odd, E. reflexivity. Qed.

Lemma lapE : forall r, csteps tm_15 10 (Cf15 (xO r)) = Some (Cf15 (xI r)).
Proof.
  intro r. destruct (venc_bump r) as (c & t & E0 & E1).
  rewrite (Cf15_evenc r c t E0), (Cf15_oddc r c t E1).
  apply ruleA.
Qed.

(** ** The scan

    [p] odd is the carry, and the carry walks the block vector from the
    frontier: a block of EVEN length [2b+2] is carried over ([out6^b .
    carry5]) and the first ODD block [2a+1] is where the deposit lands.
    [Scan bl l a rest bl'] records that walk -- [l] the carried blocks,
    [a] the deposit block, [rest] what is beyond it -- and carries the
    RESULT vector [bl'] alongside, so the two directions of the lap are one
    induction each.

    [btail] is what the deposit does at the stopping block: with a block
    beyond it the deposit adds 2 there and 1 to the next (John's "moves it
    1 left and it bounces"); with nothing beyond, it adds 1 and SPAWNS a
    length-2 block -- the carry out of the top, i.e. the new leading 1. *)

Definition btail (a : nat) (rest : list nat) : list nat :=
  match rest with
  | [] => [2 * a + 2; 2]
  | c :: t => (2 * a + 3) :: S c :: t
  end.

Inductive Scan : list nat -> list nat -> nat -> list nat -> list nat -> Prop :=
| ScanD : forall a rest,
    Scan ((2 * a + 1) :: rest) [] a rest (btail a rest)
| ScanC : forall b bl l a rest bl',
    Scan bl l a rest bl' ->
    Scan ((2 * b + 2) :: bl) (b :: l) a rest ((2 * b + 2) :: bl').

(** The outward phase's tape is exactly what the scan describes. *)
Lemma Scan_in : forall bl l a rest bl', Scan bl l a rest bl' ->
  wblocks bl = owtape l (repeat S1 (2 * a + 1) ++ S0 :: wblocks rest).
Proof.
  intros bl l a rest bl' H.
  induction H as [a rest | b bl l a rest bl' H IH].
  - reflexivity.
  - cbn [wblocks owtape]. rewrite IH. reflexivity.
Qed.

(** ...and the carried blocks come back untouched, which is why the return
    sweep rebuilds [owtape l] over whatever the deposit left. *)
Lemma Scan_out : forall bl l a rest bl', Scan bl l a rest bl' ->
  wblocks bl' = owtape l (wblocks (btail a rest)).
Proof.
  intros bl l a rest bl' H.
  induction H as [a rest | b bl l a rest bl' H IH].
  - reflexivity.
  - cbn [wblocks owtape]. rewrite IH. reflexivity.
Qed.

(** The deposit block always has a block of length >= 1 beyond it, or
    nothing at all; the middle case ("a length-0 block") never arises. *)
Definition hdok (rest : list nat) : Prop :=
  match rest with [] => True | c :: _ => 1 <= c end.

Lemma ScanD' : forall x a rest, x = 2 * a + 1 ->
  Scan (x :: rest) [] a rest (btail a rest).
Proof. intros x a rest E. subst x. constructor. Qed.

Lemma ScanC' : forall x b bl l a rest bl', x = 2 * b + 2 ->
  Scan bl l a rest bl' -> Scan (x :: bl) (b :: l) a rest (x :: bl').
Proof. intros x b bl l a rest bl' E H. subst x. constructor. exact H. Qed.

(** Every odd [p] has a scan, and the vector it produces is [venc] of the
    successor.  This is binary increment: the even blocks are the 1-digits
    the carry rides over, the odd block is the 0 it lands on.  The
    induction is on the positive itself -- [xI (xO s)] stops at once
    (rule A's block is odd), [xI (xI s)] carries one block and recurses. *)
Lemma Scan_venc : forall q, exists l a rest,
  Scan (venc (xI q)) l a rest (venc (xO (Pos.succ q))) /\ hdok rest.
Proof.
  induction q as [s IH | s IH | ].
  - (* q = xI s: the frontier block is even -- carry over it *)
    destruct IH as (l & a & rest & HS & Hh).
    exists (Pos.to_nat (xI s) :: l), a, rest. split; [| exact Hh].
    rewrite (venc_xI (xI s)) by discriminate.
    change (Pos.succ (xI s)) with (xO (Pos.succ s)).
    replace (venc (xO (xO (Pos.succ s))))
       with ((2 * Pos.to_nat (xI s) + 1 + pod (xI s)) :: venc (xO (Pos.succ s))).
    + apply ScanC'; [cbn [pod]; lia | exact HS].
    + rewrite (venc_xO (xO (Pos.succ s))) by discriminate.
      cbn [pod]. f_equal.
      rewrite Pos2Nat.inj_xO, Pos2Nat.inj_xI, Pos2Nat.inj_succ. lia.
  - (* q = xO s: the frontier block is odd -- deposit here *)
    destruct (venc_bump s) as (c & t & E0 & E1).
    exists [], (Pos.to_nat (xO s)), (venc (xO s)).
    split; [| rewrite E0; cbn [hdok]; lia].
    rewrite (venc_xI (xO s)) by discriminate.
    change (Pos.succ (xO s)) with (xI s).
    replace (venc (xO (xI s))) with (btail (Pos.to_nat (xO s)) (venc (xO s))).
    + apply ScanD'. cbn [pod]. lia.
    + rewrite E0. cbn [btail].
      rewrite (venc_xO (xI s)) by discriminate. rewrite E1.
      cbn [pod]. rewrite Pos2Nat.inj_xO, Pos2Nat.inj_xI. f_equal. lia.
  - exists [], 1, []. split; [exact (ScanD 1 []) | exact I].
Qed.

(** ** The odd lap

    [entry5 . outward . out6s] takes the anchor to the deposit's window;
    the deposit and the return sweep finish it.  [[S0;S1;S1]] is the debris
    [entry5] leaves behind -- the seed the return sweep ends on. *)

Lemma Deb_seed : Deb [S0; S1; S1].
Proof. apply DebG, DebN. Qed.

Lemma back_G : forall D R, back (S0 :: S1 :: S1 :: D) R = back D (S0 :: S1 :: S1 :: R).
Proof. reflexivity. Qed.

Lemma back_1 : forall D R, back (S1 :: D) R = back D (S1 :: R).
Proof. reflexivity. Qed.

(** [bta] rebuilds exactly the blocks [owtape] ate: the return sweep is the
    outward sweep run backwards, which is why no second induction is
    needed. *)
Lemma owtape_bta : forall l Y, S1 :: S1 :: bta l Y = owtape l (S1 :: S1 :: Y).
Proof.
  induction l as [|a t IH]; intro Y; cbn [bta owtape].
  - reflexivity.
  - rewrite <- IH.
    replace (2 * a + 2) with (S (S (2 * a))) by lia.
    cbn [repeat app]. reflexivity.
Qed.

(** What the whole debris turns back into: the carried blocks, then a run
    of [2a+2] ones and whatever the deposit put beyond them. *)
Lemma back_frame : forall l a X,
  back (lay a (owdeb l [S0; S1; S1])) X
  = S1 :: S0 :: owtape l (repeat S1 (2 * a + 2) ++ X).
Proof.
  intros l a X.
  rewrite back_lay, back_owdeb, back_G, owtape_bta.
  replace (2 * a + 2) with (2 + 2 * a) by lia.
  reflexivity.
Qed.

(** The outward half: from the anchor to the deposit's window. *)
Lemma lapO_pre : forall q l a rest bl', Scan (venc (xI q)) l a rest bl' ->
  csteps tm_15 (5 + (owcost l + 6 * a)) (Cf15 (xI q))
  = Some (StC, (S0 :: lay a (owdeb l [S0; S1; S1]), S0,
                S1 :: S0 :: wblocks rest)).
Proof.
  intros q l a rest bl' HS.
  rewrite Cf15_odd, (Scan_in _ _ _ _ _ HS).
  rewrite csteps_add, entry5.
  rewrite csteps_add, outward, out6s.
  reflexivity.
Qed.

(** The spawn: nothing beyond the deposit block, so [dep0]'s [chd]/[ctl]
    make the new stripe for free. *)
Lemma lapO_spawn : forall l a,
  csteps tm_15 (6 + bcost (S0 :: S1 :: S1 :: lay a (owdeb l [S0; S1; S1])))
    (StC, (S0 :: lay a (owdeb l [S0; S1; S1]), S0, S1 :: S0 :: wblocks []))
  = Some (StC, ([], S0, S1 :: S0 :: owtape l (wblocks (btail a [])))).
Proof.
  intros l a.
  rewrite csteps_add, (dep0 (lay a (owdeb l [S0; S1; S1])) (wblocks []) eq_refl).
  rewrite (backsweep _ (DebG _ (lay_Deb a _ (owdeb_Deb l _ Deb_seed)))).
  rewrite back_G, back_frame. reflexivity.
Qed.

(** The interior deposit: a block of length [S c] beyond, so [dep2]. *)
Lemma lapO_dep : forall l a c rest,
  csteps tm_15 (8 + bcost (S1 :: lay a (owdeb l [S0; S1; S1])))
    (StC, (S0 :: lay a (owdeb l [S0; S1; S1]), S0,
           S1 :: S0 :: wblocks (S c :: rest)))
  = Some (StC, ([], S0, S1 :: S0 :: owtape l (wblocks (btail a (S c :: rest))))).
Proof.
  intros l a c rest. cbn [wblocks repeat app].
  rewrite csteps_add, dep2.
  rewrite (backsweep _ (Deb1 _ (lay_Deb a _ (owdeb_Deb l _ Deb_seed)))).
  rewrite back_1, back_frame.
  cbn [btail wblocks]. do 2 f_equal.
  rewrite repeat_snoc.
  replace (S (2 * a + 2)) with (2 * a + 3) by lia.
  cbn [repeat app]. reflexivity.
Qed.

(** One odd lap, with the deposit window exposed so the [StB] visit can
    reuse the outward half. *)
Lemma lapO : forall q, exists n1 n2 L R,
  0 < n1
  /\ csteps tm_15 n1 (Cf15 (xI q)) = Some (StC, (S0 :: L, S0, S1 :: S0 :: R))
  /\ csteps tm_15 n2 (StC, (S0 :: L, S0, S1 :: S0 :: R))
     = Some (Cf15 (xO (Pos.succ q))).
Proof.
  intro q. destruct (Scan_venc q) as (l & a & rest & HS & Hh).
  exists (5 + (owcost l + 6 * a)).
  assert (Hout : wblocks (venc (xO (Pos.succ q)))
                 = owtape l (wblocks (btail a rest)))
    by exact (Scan_out _ _ _ _ _ HS).
  destruct rest as [|c rest'].
  - exists (6 + bcost (S0 :: S1 :: S1 :: lay a (owdeb l [S0; S1; S1]))),
           (lay a (owdeb l [S0; S1; S1])), (wblocks []).
    split; [lia|]. split; [exact (lapO_pre _ _ _ _ _ HS)|].
    rewrite lapO_spawn, Cf15_even, Hout. reflexivity.
  - destruct c as [|c']; [cbn [hdok] in Hh; lia|].
    exists (8 + bcost (S1 :: lay a (owdeb l [S0; S1; S1]))),
           (lay a (owdeb l [S0; S1; S1])), (wblocks (S c' :: rest')).
    split; [lia|]. split; [exact (lapO_pre _ _ _ _ _ HS)|].
    rewrite lapO_dep, Cf15_even, Hout. reflexivity.
Qed.

(** ** Visits: all four states inside every lap *)

Lemma vis4 : forall R,
  csteps tm_15 4 (StC, ([], S0, S1 :: R)) = Some (StA, ([S0; S1; S1], chd R, ctl R)).
Proof. reflexivity. Qed.

Lemma vis5B : forall R,
  csteps tm_15 5 (StC, ([], S0, S1 :: S0 :: R))
  = Some (StB, ([S1; S0; S1; S1], chd R, ctl R)).
Proof. reflexivity. Qed.

(** The deposit's first five steps: [A0 = 1RB] is the only door into
    [StB], and on an odd [p] it is the deposit that opens it. *)
Lemma depB : forall L R,
  csteps tm_15 5 (StC, (S0 :: L, S0, S1 :: S0 :: R))
  = Some (StB, (S1 :: S0 :: S1 :: S1 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

Lemma Cf15_hd : forall p, exists R, Cf15 p = (StC, ([], S0, S1 :: R)).
Proof. destruct p as [q|r|]; eexists; reflexivity. Qed.

Lemma vis15 : forall p q, (2 <= p)%positive ->
  exists k c, csteps tm_15 k (Cf15 p) = Some c /\ fst c = q.
Proof.
  intros p q Hp. destruct q.
  - (* StA *) destruct (Cf15_hd p) as (R & E).
    exists 4. eexists. rewrite E. split; [apply vis4 | reflexivity].
  - (* StB *) destruct p as [q0|r|].
    + destruct (Scan_venc q0) as (l & a & rest & HS & _).
      exists (5 + (owcost l + 6 * a) + 5).
      eexists. split.
      * rewrite csteps_add, (lapO_pre _ _ _ _ _ HS). apply depB.
      * reflexivity.
    + exists 5. eexists. rewrite Cf15_even.
      split; [apply vis5B | reflexivity].
    + lia.
  - (* StC *) exists 0. eexists. split; reflexivity.
  - (* StD *) destruct (Cf15_hd p) as (R & E).
    exists 1. eexists. rewrite E. split; reflexivity.
Qed.

(** ** Boot and the theorem *)

Lemma boot15 : exists t0, stepn tm_15 t0 InitES = Some (lift (Cf15 2)).
Proof.
  exists 17.
  assert (H : match csteps tm_15 17 c0 with
              | Some c => ceqb c (Cf15 2)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_15 17 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

(** #15 never quasihalts: bbchallenge 1RB0RC_0LC1LB_0LD1LC_1RD0RA. *)
Theorem nqh_1RB0RC_0LC1LB_0LD1LC_1RD0RA : NeverQuasiHaltsSt tm_15.
Proof.
  apply (glue_neverqh tm_15 Cf15 2).
  - exact boot15.
  - intros p Hp. destruct p as [q|r|].
    + destruct (lapO q) as (n1 & n2 & L & R & Hn & H1 & H2).
      exists (n1 + n2), (Cf15 (xO (Pos.succ q))).
      split; [rewrite csteps_add, H1; exact H2 | split; [reflexivity | lia]].
    + exists 10, (Cf15 (xI r)).
      split; [apply lapE | split; [reflexivity | lia]].
    + lia.
  - intros p q Hp. apply vis15, Hp.
Qed.

Theorem tm_15_nonhalt : NonHalt tm_15.
Proof. apply never_qh_nonhalt, nqh_1RB0RC_0LC1LB_0LD1LC_1RD0RA. Qed.
