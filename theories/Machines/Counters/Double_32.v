(** * Double_32: 1RB1LD_1RC0RB_1LA0RC_0LD0LA never quasihalts.

    BBB [double_counter] certificate #32, and the last (4,2) holdout of
    the mxdys S(n) survey to come off the board.  BBB models it as a
    COMB COUNTER: the clean event is head-on-rightmost-1 with comb count
    [a = 2^j], [a -> 2a], one macro lap costing [36k^2 + 29k - 4] steps
    -- a [Theta(k^2)] quadratic bounce, which is why the macro reading is
    the expensive one.  (BBB's own notes record an earlier [a = 2^j-1]
    guess as having TIMED OUT.)

    Sampled at the LEFT RECORD instead -- head on the leftmost visited
    cell, [StA], reading blank -- the machine is a plain rewriting system
    on a block word.  Writing the tape as

      (001)^j  followed by  0^a1 1^b1 0^a2 1^b2 ...   (blanks beyond)

    the left record recurs three times per increment of the comb, and the
    three rewritings between them are UNIFORM in everything except [j]:

      R1   0 1^m 0^p 1^q X  ->  0^(m+2) 1^2 0^(p-2) 1^q X    8j + 2m + 5
      R2   0^a 1^2 X        ->  (j+1),  1 0^(a-3) 1^2 X      8j + 5
      R3   1 0^b 1^c X      ->  0 1^4 0^(b-3) 1^c X          8j + 11

    Only R1 traverses a run; R2 and R3 rewrite a bounded window at the
    front of the tape and return, so their cost is the comb traversal
    [8j] plus a constant.  Composing R1;R2;R3 gives the one-line law

      (001)^j 0 1^m 0^p 1^q X
        -->+  (001)^(j+1) 0 1^4 0^(m-4) 1^2 0^(p-2) 1^q X

    in [24j + 2m + 29] steps.  The macro doubling [a -> 2a] is a
    CONSEQUENCE of iterating this, never an assumption -- which is what
    makes the quadratic macro lap irrelevant.  [WaveCounter.wglue_neverqh]
    takes an arbitrary anchor type with a total successor and a preserved
    invariant, so no closed form for [j] or for the block word is needed
    at any point, and this file needs no new closer.

    The [8j] is [rc5]/[lc3]: five steps out and three back per comb
    block.  The [2m] in R1 is [b1]/[d0], the outward and return sweeps
    over the [1^m] run.  Every gadget below is uniform in the surrounding
    tape and is a one-line [reflexivity]; all nine were checked
    differentially against a CTape-faithful mirror
    ([tools/counters/gadgets32.py]) before any Coq was written, as were
    the sweep inductions, the three rule statements and the composed lap
    ([tools/counters/rules32.py]).

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape WaveCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB1LD_1RC0RB_1LA0RC_0LD0LA *)
Definition tm_32 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StD
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S0 DR StB
  | StC, S0 => mk S1 DL StA | StC, S1 => mk S0 DR StC
  | StD, S0 => mk S0 DL StD | StD, S1 => mk S0 DL StA
  end.

(** ** The nine step gadgets

    Verbatim from the measured table (there written with [++]; a literal
    window is spelled out here so that the compositions [rewrite] against
    [cbn]-normal forms without further plumbing).  Each is uniform in the
    left context [L], the tail [R] and -- for the leftward pair -- the
    middle [M]; [chd]/[ctl] are what make them uniform at the ends of the
    half-tape lists, so no gadget carries a length side condition. *)

(** Rightward: [bt4] crosses the boot cell, [rc5] one comb block --
    five steps out per [001]. *)
Lemma bt4 : forall L R,
  csteps tm_32 4 (StA, (L, S0, S0 :: S1 :: S0 :: R))
  = Some (StA, (S1 :: S1 :: L, S0, S1 :: R)).
Proof. reflexivity. Qed.

Lemma rc5 : forall L R,
  csteps tm_32 5 (StA, (L, S0, S1 :: S0 :: S1 :: S0 :: R))
  = Some (StA, (S1 :: S0 :: S1 :: L, S0, S1 :: R)).
Proof. reflexivity. Qed.

(** Turnarounds. *)
Lemma tn4 : forall L R,
  csteps tm_32 4 (StA, (L, S0, S1 :: S0 :: S0 :: R))
  = Some (StA, (S0 :: S1 :: L, S1, S1 :: R)).
Proof. reflexivity. Qed.

Lemma tn6 : forall L R,
  csteps tm_32 6 (StA, (L, S0, S1 :: S0 :: S1 :: S1 :: S0 :: S0 :: R))
  = Some (StA, (S0 :: S1 :: S0 :: S1 :: L, S0, S1 :: S0 :: R)).
Proof. reflexivity. Qed.

Lemma md3 : forall L R,
  csteps tm_32 3 (StA, (L, S0, S0 :: S0 :: S1 :: R))
  = Some (StA, (S1 :: L, S1, S1 :: S1 :: R)).
Proof. reflexivity. Qed.

(** Leftward -- three steps back per comb block.  Note [la2] consumes
    TWO cells from the left, not one: same shape as [lc3]. *)
Lemma lc3 : forall M R,
  csteps tm_32 3 (StA, (S0 :: S1 :: M, S1, R))
  = Some (StA, (ctl M, chd M, S0 :: S0 :: S1 :: R)).
Proof. reflexivity. Qed.

Lemma la2 : forall M R,
  csteps tm_32 2 (StA, (S1 :: M, S1, R))
  = Some (StA, (ctl M, chd M, S0 :: S1 :: R)).
Proof. reflexivity. Qed.

(** The two run sweeps R1 needs. *)
Lemma b1 : forall L R,
  csteps tm_32 1 (StB, (L, S1, R))
  = Some (StB, (S0 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

Lemma d0 : forall L R,
  csteps tm_32 1 (StD, (L, S0, R))
  = Some (StD, (ctl L, chd L, S0 :: R)).
Proof. reflexivity. Qed.

(** ** Single-step joints

    The five transitions that glue the gadgets together, plus [cons]
    forms of [b1]/[d0] for the sweep inductions.  These are stated as
    lemmas rather than discharged on the nose: a [change] to [Some _]
    leaves an unreduced [match] and the next [rewrite] cannot find its
    subterm. *)

Lemma sA0 : forall L x R,
  csteps tm_32 1 (StA, (L, S0, x :: R)) = Some (StB, (S1 :: L, x, R)).
Proof. reflexivity. Qed.

Lemma sB0 : forall L R,
  csteps tm_32 1 (StB, (L, S0, R)) = Some (StC, (S1 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

Lemma sC0 : forall x L R,
  csteps tm_32 1 (StC, (x :: L, S0, R)) = Some (StA, (L, x, S1 :: R)).
Proof. reflexivity. Qed.

Lemma sA1 : forall x L R,
  csteps tm_32 1 (StA, (x :: L, S1, R)) = Some (StD, (L, x, S1 :: R)).
Proof. reflexivity. Qed.

Lemma sD1 : forall L R,
  csteps tm_32 1 (StD, (L, S1, R)) = Some (StA, (ctl L, chd L, S0 :: R)).
Proof. reflexivity. Qed.

Lemma b1c : forall L x R,
  csteps tm_32 1 (StB, (L, S1, x :: R)) = Some (StB, (S0 :: L, x, R)).
Proof. reflexivity. Qed.

Lemma d0c : forall x L R,
  csteps tm_32 1 (StD, (x :: L, S0, R)) = Some (StD, (L, x, S0 :: R)).
Proof. reflexivity. Qed.

(** ** The comb, in its three phases

    [comb] is the tape's [(001)^j]; walking it rightward the head reads
    it out of phase as [(010)^*] ([outp]) and lays [(101)^*] behind it
    ([inp]).  All three take their tail as an argument, so composing
    them is [cbn] rather than [app] associativity. *)

Fixpoint comb (j : nat) (X : list Sym) : list Sym :=
  match j with 0 => X | S i => S0 :: S0 :: S1 :: comb i X end.

Fixpoint outp (k : nat) (X : list Sym) : list Sym :=
  match k with 0 => X | S i => S0 :: S1 :: S0 :: outp i X end.

Fixpoint inp (k : nat) (X : list Sym) : list Sym :=
  match k with 0 => X | S i => S1 :: S0 :: S1 :: inp i X end.

Lemma comb_shift : forall k X, comb k (S0 :: S0 :: S1 :: X) = S0 :: S0 :: S1 :: comb k X.
Proof.
  induction k as [|k IH]; intro X; cbn [comb];
    [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma outp_shift : forall k X, outp k (S0 :: S1 :: S0 :: X) = S0 :: S1 :: S0 :: outp k X.
Proof.
  induction k as [|k IH]; intro X; cbn [outp];
    [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma inp_shift : forall k X, inp k (S1 :: S0 :: S1 :: X) = S1 :: S0 :: S1 :: inp k X.
Proof.
  induction k as [|k IH]; intro X; cbn [inp];
    [reflexivity | rewrite IH; reflexivity].
Qed.

(** The one cell of phase shift that turns the comb into what [rc5]
    reads: from the left record the head is on a [0], not on a block
    boundary. *)
Lemma comb_outp : forall i U, S0 :: S1 :: comb i U = outp i (S0 :: S1 :: U).
Proof.
  induction i as [|i IH]; intro U; cbn [comb outp];
    [reflexivity | rewrite <- IH; reflexivity].
Qed.

Lemma repeat_snoc : forall (x : Sym) k L,
  repeat x k ++ x :: L = repeat x (S k) ++ L.
Proof.
  induction k as [|k IH]; intro L; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

(** ** The four sweep inductions

    Each is an induction on the count with the tail universally
    quantified, so the untouched part of the tape never enters. *)

(** [rc5] iterated: the outward half of the [8j]. *)
Lemma rcs : forall k L Z,
  csteps tm_32 (5 * k) (StA, (L, S0, S1 :: outp k Z))
  = Some (StA, (inp k L, S0, S1 :: Z)).
Proof.
  induction k as [|k IH]; intros L Z.
  - reflexivity.
  - replace (5 * S k) with (5 + 5 * k) by lia.
    cbn [outp]. rewrite csteps_add, rc5, IH, inp_shift. reflexivity.
Qed.

(** [lc3] iterated and closed off by [la2]: the return half of the
    [8j], landing exactly on the next left record. *)
Lemma retsw : forall k X,
  csteps tm_32 (3 * k + 2)
    (StA, (ctl (inp k [S1;S1]), chd (inp k [S1;S1]), X))
  = Some (StA, ([], S0, S0 :: S1 :: comb k X)).
Proof.
  induction k as [|k IH]; intro X.
  - reflexivity.
  - replace (3 * S k + 2) with (3 + (3 * k + 2)) by lia.
    cbn [inp chd ctl]. rewrite csteps_add, lc3, IH, comb_shift. reflexivity.
Qed.

(** The same return sweep entered one [lc3] earlier, which is the shape
    R2 and R3 hand back. *)
Lemma retsw1 : forall k X,
  csteps tm_32 (3 * S k + 2) (StA, (S0 :: S1 :: inp k [S1;S1], S1, X))
  = Some (StA, ([], S0, S0 :: S1 :: comb (S k) X)).
Proof.
  intros k X. replace (3 * S k + 2) with (3 + (3 * k + 2)) by lia.
  rewrite csteps_add, lc3, retsw, comb_shift. reflexivity.
Qed.

(** [b1] iterated: out along the [1^m] run, laying blanks. *)
Lemma b1s : forall k L R,
  csteps tm_32 k (StB, (L, S1, repeat S1 k ++ R))
  = Some (StB, (repeat S0 k ++ L, S1, R)).
Proof.
  induction k as [|k IH]; intros L R.
  - reflexivity.
  - cbn [repeat app]. replace (S k) with (1 + k) by lia.
    rewrite csteps_add, b1c, IH, repeat_snoc. reflexivity.
Qed.

(** [d0] iterated: back along the blanks [b1] laid.  The debris the
    outward walk leaves is exactly what the return walk re-crosses,
    which is why the run comes out shifted rather than shortened. *)
Lemma d0s : forall k L R,
  csteps tm_32 k (StD, (repeat S0 k ++ L, S0, R))
  = Some (StD, (L, S0, repeat S0 k ++ R)).
Proof.
  induction k as [|k IH]; intros L R.
  - reflexivity.
  - cbn [repeat app]. replace (S k) with (1 + k) by lia.
    rewrite csteps_add, d0c, IH, repeat_snoc. reflexivity.
Qed.

(** The comb traversal out, from the left record: [bt4] then [rc5^i]. *)
Lemma out32 : forall i L Z,
  csteps tm_32 (4 + 5 * i) (StA, (L, S0, S0 :: S1 :: S0 :: outp i Z))
  = Some (StA, (inp i (S1 :: S1 :: L), S0, S1 :: Z)).
Proof.
  intros i L Z. rewrite csteps_add, bt4, rcs. reflexivity.
Qed.

(** ** The three rules

    All three start and end on a left record: [StA], left list empty,
    head on the leftmost visited cell.  The comb has length [S i]
    (resp. [S (S i)] for R3, which needs two blocks of run-up). *)

(** R1's outward leg, stopped at the turnaround.  Split out because it
    is also the only place the machine visits [StD] early enough for
    [vis32] -- [bt4] and [rc5] never do. *)
Lemma R1D : forall i m Y,
  chd Y = S0 -> chd (ctl Y) = S0 ->
  csteps tm_32 (5 * i + m + 9)
    (StA, ([], S0, S0 :: S1 :: comb i (S0 :: (repeat S1 m ++ Y))))
  = Some (StD, (repeat S0 m ++ (S1 :: inp i [S1;S1]),
                S0, S1 :: S1 :: ctl (ctl Y))).
Proof.
  intros i m Y H1 H2.
  replace (5 * i + m + 9)
     with ((4 + 5 * i) + (1 + (m + (1 + (1 + (1 + 1)))))) by lia.
  rewrite comb_outp, outp_shift.
  rewrite csteps_add, out32.
  rewrite csteps_add, sA0.
  rewrite csteps_add, b1s.
  rewrite csteps_add, b1, H1.
  rewrite csteps_add, sB0, H2.
  rewrite csteps_add, sC0, sA1.
  reflexivity.
Qed.

(** R1: [0 1^m 0^p 1^q X -> 0^(m+2) 1^2 0^(p-2) 1^q X] in [8j+2m+5].
    The tail [Y] is arbitrary given that its first two cells are blank
    -- that is the [p >= 2] side condition, stated through [chd]/[ctl]
    so that [Y = []] (an all-blank tail) is not a separate case. *)
Lemma R1 : forall i m Y,
  chd Y = S0 -> chd (ctl Y) = S0 ->
  csteps tm_32 (8 * S i + 2 * m + 5)
    (StA, ([], S0, S0 :: S1 :: comb i (S0 :: (repeat S1 m ++ Y))))
  = Some (StA, ([], S0, S0 :: S1 :: comb i
             (repeat S0 (S (S m)) ++ (S1 :: S1 :: ctl (ctl Y))))).
Proof.
  intros i m Y H1 H2.
  replace (8 * S i + 2 * m + 5)
     with ((5 * i + m + 9) + (m + (1 + (1 + (3 * i + 2))))) by lia.
  rewrite csteps_add, R1D by assumption.
  rewrite csteps_add, d0s.
  rewrite csteps_add, d0c.
  rewrite csteps_add, sD1, retsw.
  reflexivity.
Qed.

(** R2: [0^a 1^2 X -> 1 0^(a-3) 1^2 X] with the comb one longer, in
    [8j+5].  The head rewrites the three blanks at the front of the
    [0^a] run and returns, so the tail [T] is wholly arbitrary. *)
Lemma R2 : forall i T,
  csteps tm_32 (8 * S i + 5)
    (StA, ([], S0, S0 :: S1 :: comb i (S0 :: S0 :: S0 :: T)))
  = Some (StA, ([], S0, S0 :: S1 :: comb (S i) (S1 :: T))).
Proof.
  intros i T.
  replace (8 * S i + 5) with ((4 + 5 * i) + (4 + (3 * S i + 2))) by lia.
  rewrite comb_outp, outp_shift.
  rewrite csteps_add, out32.
  rewrite csteps_add, tn4, retsw1.
  reflexivity.
Qed.

(** R3: [1 0^b 1^c X -> 0 1^4 0^(b-3) 1^c X] in [8j+11].  Same bounded
    window; the extra block of run-up before the turnaround -- [tn6]
    ahead of [tn4] -- is what makes this [0^(b-3)] and not [0^(b-2)]. *)
Lemma R3 : forall i T,
  csteps tm_32 (8 * S (S i) + 11)
    (StA, ([], S0, S0 :: S1 :: comb (S i) (S1 :: S0 :: S0 :: S0 :: T)))
  = Some (StA, ([], S0, S0 :: S1 :: comb (S i)
             (S0 :: S1 :: S1 :: S1 :: S1 :: T))).
Proof.
  intros i T.
  replace (8 * S (S i) + 11)
     with ((4 + 5 * i) + (6 + (4 + (3 + (3 + (2 + (3 * S i + 2))))))) by lia.
  rewrite comb_outp. cbn [outp].
  rewrite csteps_add, out32.
  rewrite csteps_add, tn6.
  rewrite csteps_add, tn4.
  rewrite csteps_add, lc3. cbn [chd ctl].
  rewrite csteps_add, md3.
  rewrite csteps_add, la2. cbn [chd ctl].
  rewrite retsw1.
  reflexivity.
Qed.

(** ** The abstract state

    [(j, L)] with [L] a block word [[(a1,b1); (a2,b2); ...]] denoting
    [0^a1 1^b1 0^a2 1^b2 ...] and an implicit blank tail.  No closed
    form for either component is ever needed. *)

Definition blk : Type := (nat * nat)%type.

Fixpoint wden (L : list blk) : list Sym :=
  match L with
  | [] => []
  | (a, b) :: t => repeat S0 a ++ repeat S1 b ++ wden t
  end.

(** [nrm] merges a zero-length [0]-run into the previous [1]-run.  This
    is a DENOTATIONAL identity, so it costs one rewrite rather than a
    normalisation theory. *)
Definition nrm (L : list blk) : list blk :=
  match L with
  | (a, b) :: (0, c) :: t => (a, b + c) :: t
  | _ => L
  end.

Lemma wden_nrm : forall L, wden (nrm L) = wden L.
Proof.
  intros [|[a b] [|[p c] t]]; try reflexivity.
  destruct p; [|reflexivity].
  cbn [nrm wden]. rewrite repeat_app, <- !app_assoc. reflexivity.
Qed.

(** R1 consumes two blanks off the block following the lead. *)
Definition dec2 (L : list blk) : list blk :=
  match L with [] => [] | (p, q) :: t => (p - 2, q) :: t end.

(** The composed successor: one turn of R1 -> R2 -> R3. *)
Definition nextL (L : list blk) : list blk :=
  match L with
  | [] => []
  | (_, m) :: rest => nrm ((1, 4) :: nrm ((m - 4, 2) :: dec2 rest))
  end.

Definition lead1 (L : list blk) : nat :=
  match L with [] => 0 | (_, m) :: _ => m end.

Definition next32 (a : nat * list blk) : nat * list blk :=
  (S (fst a), nextL (snd a)).

Definition Cf32 (a : nat * list blk) : cconf :=
  (StA, ([], chd (comb (fst a) (wden (snd a))),
             ctl (comb (fst a) (wden (snd a))))).

Lemma Cf32_S : forall i L,
  Cf32 (S i, L) = (StA, ([], S0, S0 :: S1 :: comb i (wden L))).
Proof. reflexivity. Qed.

(** ** The invariant

    Lead block [(1, m)] with [m] even and [>= 4]; every later block has
    both runs even and [>= 2].  [m >= 4] is R3's [b >= 3]; the [2]s are
    R1's [p >= 2]; evenness is what makes [m - 4] and [p - 2] land back
    in range after the rewriting, and it is preserved because both
    decrements are by an even amount. *)

Definition OkB (x : blk) : Prop :=
  (exists u, fst x = 2 + 2 * u) /\ (exists v, snd x = 2 + 2 * v).

Definition LeadOk (L : list blk) : Prop :=
  match L with
  | [] => False
  | (a, m) :: rest => a = 1 /\ (exists k, m = 4 + 2 * k) /\ Forall OkB rest
  end.

Definition Inv32 (a : nat * list blk) : Prop :=
  1 <= fst a /\ LeadOk (snd a).

Lemma Inv32_next : forall a, Inv32 a -> Inv32 (next32 a).
Proof.
  intros [j L] [Hj HL]. split; [cbn; lia|].
  cbn [snd next32] in *. destruct L as [|[a m] rest]; [contradiction|].
  destruct HL as (-> & (k & ->) & Hrest).
  cbn [nextL].
  destruct rest as [|[p q] t].
  - (* nothing after the lead: only the lead merge can fire *)
    destruct k as [|k]; cbn; (split; [reflexivity | split]).
    + exists 1; lia.
    + constructor.
    + exists 0; lia.
    + constructor; [split; cbn; [exists k; lia | exists 0; lia] | constructor].
  - pose proof (Forall_inv Hrest) as Hp.
    pose proof (Forall_inv_tail Hrest) as Ht.
    destruct Hp as ((u & Hu) & (v & Hv)). cbn in Hu, Hv. subst p q.
    (* the four normalisation branches, on whether m-4 and p-2 vanish *)
    destruct k as [|k]; destruct u as [|u]; cbn;
      (split; [reflexivity | split]).
    + (* m = 4, p = 2: both merges fire *) exists (2 + v); lia.
    + assumption.
    + (* m = 4, p >= 4: only the lead merge fires *) exists 1; lia.
    + constructor; [split; cbn; [exists u; lia | exists v; lia] | assumption].
    + (* m >= 6, p = 2: only the inner merge fires *) exists 0; lia.
    + constructor; [split; cbn; [exists k; lia | exists (1 + v); lia]
                   | assumption].
    + (* m >= 6, p >= 4: no merge *) exists 0; lia.
    + constructor; [split; cbn; [exists k; lia | exists 0; lia]|].
      constructor; [split; cbn; [exists u; lia | exists v; lia] | assumption].
Qed.

(** The two blanks R1 eats off the following block, read through
    [chd]/[ctl] so that the empty tail is not a separate case. *)
Lemma wden_dec2 : forall rest, Forall OkB rest ->
  chd (wden rest) = S0 /\ chd (ctl (wden rest)) = S0
  /\ ctl (ctl (wden rest)) = wden (dec2 rest).
Proof.
  intros [|[p q] t] H; [repeat split; reflexivity|].
  destruct (Forall_inv H) as ((u & Hu) & _). cbn in Hu.
  assert (H2 : 2 <= p) by lia.
  destruct p as [|[|p]]; try lia.
  cbn [wden dec2 repeat app chd ctl Nat.sub]. rewrite Nat.sub_0_r.
  repeat split; reflexivity.
Qed.

(** ** The lap *)

Definition lapn (a : nat * list blk) : nat :=
  24 * fst a + 2 * lead1 (snd a) + 29.

Lemma lap32 : forall a, Inv32 a ->
  csteps tm_32 (lapn a) (Cf32 a) = Some (Cf32 (next32 a)).
Proof.
  intros [j L] [Hj HL]. cbn [fst snd] in *.
  destruct j as [|i]; [lia|].
  destruct L as [|[a m] rest]; [contradiction|].
  destruct HL as (-> & (k & Hm) & Hrest).
  destruct (wden_dec2 rest Hrest) as (HY1 & HY2 & HY3).
  unfold lapn, next32. cbn [fst snd lead1 nextL].
  rewrite Cf32_S, Cf32_S.
  replace (24 * S i + 2 * m + 29)
     with ((8 * S i + 2 * m + 5) + ((8 * S i + 5) + (8 * S (S i) + 11))) by lia.
  cbn [wden repeat app].
  (* R1: the 1^m run turns into 0^(m+2) 1^2 *)
  rewrite csteps_add, R1 by assumption.
  rewrite HY3.
  (* R2: three blanks off the front of the 0^(m+2) run, comb grows *)
  replace (S (S m)) with (S (S (S (3 + 2 * k)))) by lia.
  cbn [repeat app].
  rewrite csteps_add, R2.
  (* R3: three more, which is what makes 0^a -> 0^(a-3) *)
  replace (3 + 2 * k) with (S (S (S (2 * k)))) by lia.
  cbn [repeat app].
  rewrite R3.
  (* land on the normalised block word *)
  rewrite wden_nrm. cbn [wden]. rewrite wden_nrm.
  rewrite Hm. replace (4 + 2 * k - 4) with (2 * k) by lia.
  cbn [wden repeat app]. reflexivity.
Qed.

(** ** Visits: all four states inside one lap *)

Lemma vis32 : forall a q, Inv32 a ->
  exists n c, csteps tm_32 n (Cf32 a) = Some c /\ fst c = q.
Proof.
  intros [j L] q [Hj HL]. cbn [fst snd] in *.
  destruct j as [|i]; [lia|].
  destruct L as [|[a m] rest]; [contradiction|].
  destruct HL as (-> & (k & Hm) & Hrest).
  destruct (wden_dec2 rest Hrest) as (HY1 & HY2 & _).
  rewrite Cf32_S. cbn [wden repeat app].
  destruct q.
  - exists 0. eexists. split; reflexivity.
  - exists 1. eexists. split; [reflexivity | reflexivity].
  - exists 2. eexists. split; [reflexivity | reflexivity].
  - exists (5 * i + m + 9). eexists.
    split; [apply R1D; assumption | reflexivity].
Qed.

(** ** Boot and the theorem *)

Definition a0_32 : nat * list blk := (1, [(1, 4)]).

Lemma boot32 : exists t0, stepn tm_32 t0 InitES = Some (lift (Cf32 a0_32)).
Proof.
  exists 24.
  assert (H : match csteps tm_32 24 c0 with
              | Some c => ceqb c (Cf32 a0_32)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_32 24 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

(** #32 never quasihalts: bbchallenge 1RB1LD_1RC0RB_1LA0RC_0LD0LA. *)
Theorem nqh_1RB1LD_1RC0RB_1LA0RC_0LD0LA : NeverQuasiHaltsSt tm_32.
Proof.
  apply (wglue_neverqh tm_32 (nat * list blk) next32 Inv32 Cf32 a0_32).
  - split; [cbn; lia|].
    cbn. split; [reflexivity | split; [exists 0; reflexivity | constructor]].
  - exact Inv32_next.
  - exact boot32.
  - intros a Ha. exists (lapn a), (Cf32 (next32 a)).
    split; [apply lap32; exact Ha | split; [reflexivity|]].
    unfold lapn. lia.
  - exact vis32.
Qed.

Theorem tm_32_nonhalt : NonHalt tm_32.
Proof. apply never_qh_nonhalt, nqh_1RB1LD_1RC0RB_1LA0RC_0LD0LA. Qed.
