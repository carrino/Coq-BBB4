(** * NestC_1RB0RB_1LC1LD_0LC1RA_0LD0RA: a doubling nested bouncer.

    bbchallenge 1RB0RB_1LC1LD_0LC1RA_0LD0RA, one of the undecided core
    rows (tools/closeout/core_rows.txt).  Every anchor search in the
    repo reports `no-anchor` for it (tools/closeout/residue_map.tsv),
    and rightly so: it is NOT a positional counter.  Its tape is almost
    blank at every record --

      t=1      1 [0]              t=57     1 0000 [0]
      t=4      1 0 [0]            t=120    1 00000 [0]
      t=11     1 00 [0]           t=247    1 000000 [0]
      t=26     1 000 [0]          ...

    -- one written [S1] at the far left, a gap of blanks, the head at the
    right end, and the gap growing by ONE per record while the time
    between records DOUBLES.  All the work is invisible to a probe that
    only reads records.

    The family that does see it carries TWO gap lengths.  Write

      P a b :  1 0^a [A:0] 0^b 1

    -- a wall on the left, the head on a blank with [a] blanks behind it
    and [b] ahead, and a lone marker at the right edge.  Then the whole
    orbit is two rules:

      P a (S b)  -->  P (S a) b       in  2^(b+3) - 1 steps
      P a 0      -->  P 0 (S a)       in  a + 8 steps

    so the head walks the gap once per record, each hop costing twice
    the last, and the wrap widens the gap by one.  [P 0 n --> P 0 (S n)]
    is therefore [2^(n+3)] steps, which is the doubling seen above.

    The hop is where the machine hides.  It is NOT a chain, and not a
    counter lap either: it is a NESTED recursion, [Th (S f) = 2*Th f + 1],
    and unfolding it needs four rules at once, all with the same cost
    [Th f] and all uniform in the deep word [M] and the far side [R]:

      Bz f :  B  0^f 1 M [0] R    -->  B  0^(f+1) 1 M [R0] R'
      Bo f :  B  0^f 1 M [1] R    -->  B  0^(f+2) M   [R0] R'
      Cz f :  C  0^f 1 M [0] R    -->  B  0^f 1 1 M   [R0] R'
      Dz f :  D  0^f 1 M [0] R    -->  B  0^f 1 0 M   [R0] R'

    ([Bz]'s left word is written head-outward, so [0^f 1 M] means [f]
    blanks between the head and the nearest [S1].)  Each of the four is
    one step plus TWO of the others at [f-1]:

      Bz (S f) = B0 . Cz f . Bo f        Cz (S f) = C0 . Cz f . Bz f
      Bo (S f) = B1 . Dz f . Bo f        Dz (S f) = D0 . Dz f . Bz f

    and that mutual recursion is exactly the doubling.  The pairing is
    the machine's own: [C] leaves the [S1] it turns on and [D] clears it,
    which is why [Cz] plants a [S1] and [Dz] plants a [S0] -- the two
    rules differ in one cell and in nothing else.

    A hop [P a (S b) --> P (S a) b] is then [A0], then [Bz 0], [Bz 1],
    ... [Bz b] chained across the gap (each [Bz] eats one cell of it),
    then [B1], a [D] sweep home and [D1].

    No closed form for the step counts is needed anywhere: [Th], the
    chain total [ST] and the descent total [Dn] are defined by the same
    recursions the proofs use.  Every rule was checked differentially
    against the raw simulator (exact [cconf], exact totals) for
    [f = 0..9] against six deep contexts, including both tape edges,
    before any of this was written. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue LinCarry.
Import ListNotations.

(** [rep1_cons], [rep1_snoc] and [lift_pad_eq] are the generic list facts
    of [Counters/LinCarry.v]; nothing else is borrowed from there. *)

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).

(** 1RB0RB_1LC1LD_0LC1RA_0LD0RA *)
Definition tm_nc : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DR StB
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DL StD
  | StC, S0 => mk S0 DL StC | StC, S1 => mk S1 DR StA
  | StD, S0 => mk S0 DL StD | StD, S1 => mk S0 DR StA
  end.

(** ** The eight transitions, as one-step gadgets

    Stated with [chd]/[ctl] so they fire at the tape edges too. *)

Lemma gA0 : forall l r,
  cstep tm_nc (StA, (l, S0, r)) = Some (StB, (S1 :: l, chd r, ctl r)).
Proof. reflexivity. Qed.
Lemma gA1 : forall l r,
  cstep tm_nc (StA, (l, S1, r)) = Some (StB, (S0 :: l, chd r, ctl r)).
Proof. reflexivity. Qed.
Lemma gB0 : forall l r,
  cstep tm_nc (StB, (l, S0, r)) = Some (StC, (ctl l, chd l, S1 :: r)).
Proof. reflexivity. Qed.
Lemma gB1 : forall l r,
  cstep tm_nc (StB, (l, S1, r)) = Some (StD, (ctl l, chd l, S1 :: r)).
Proof. reflexivity. Qed.
Lemma gC0 : forall l r,
  cstep tm_nc (StC, (l, S0, r)) = Some (StC, (ctl l, chd l, S0 :: r)).
Proof. reflexivity. Qed.
Lemma gC1 : forall l r,
  cstep tm_nc (StC, (l, S1, r)) = Some (StA, (S1 :: l, chd r, ctl r)).
Proof. reflexivity. Qed.
Lemma gD0 : forall l r,
  cstep tm_nc (StD, (l, S0, r)) = Some (StD, (ctl l, chd l, S0 :: r)).
Proof. reflexivity. Qed.
Lemma gD1 : forall l r,
  cstep tm_nc (StD, (l, S1, r)) = Some (StA, (S0 :: l, chd r, ctl r)).
Proof. reflexivity. Qed.

Lemma stepN : forall a b c c',
  csteps tm_nc a c = Some c' -> csteps tm_nc (a + b) c = csteps tm_nc b c'.
Proof. intros a b c c' H. rewrite csteps_add, H. reflexivity. Qed.

Local Ltac go H := erewrite (stepR tm_nc _ _ _ (H _ _)); cbn [chd ctl].
Local Ltac gorun H := erewrite (stepN _ _ _ _ H).
Local Ltac expose := rewrite rep1_cons; cbn [app].

(** ** The nested hop

    [Th f] is the hop's cost.  No closed form: the recursion below IS
    [Th]'s definition, and [Th f = 2^(f+2) - 1]. *)

Fixpoint Th (f : nat) : nat := match f with O => 3 | S g => S (Th g + Th g) end.

Lemma four_rules : forall f,
  (forall M R, csteps tm_nc (Th f) (StB, (rep [S0] f ++ S1 :: M, S0, R))
     = Some (StB, (rep [S0] (S f) ++ S1 :: M, chd R, ctl R)))
  /\ (forall M R, csteps tm_nc (Th f) (StB, (rep [S0] f ++ S1 :: M, S1, R))
     = Some (StB, (rep [S0] (S (S f)) ++ M, chd R, ctl R)))
  /\ (forall M R, csteps tm_nc (Th f) (StC, (rep [S0] f ++ S1 :: M, S0, R))
     = Some (StB, (rep [S0] f ++ S1 :: S1 :: M, chd R, ctl R)))
  /\ (forall M R, csteps tm_nc (Th f) (StD, (rep [S0] f ++ S1 :: M, S0, R))
     = Some (StB, (rep [S0] f ++ S1 :: S0 :: M, chd R, ctl R))).
Proof.
  induction f as [|f (IHz & IHo & IHc & IHd)].
  - cbn [Th rep app]. split; [|split; [|split]]; intros M R.
    + go gB0. go gC1. go gA1. reflexivity.
    + go gB1. go gD1. go gA1. reflexivity.
    + go gC0. go gC1. go gA0. reflexivity.
    + go gD0. go gD1. go gA0. reflexivity.
  - cbn [Th]. split; [|split; [|split]]; intros M R; expose.
    + go gB0. gorun (IHc M (S1 :: R)). cbn [chd ctl].
      exact (IHo (S1 :: M) R).
    + go gB1. gorun (IHd M (S1 :: R)). cbn [chd ctl].
      rewrite (IHo (S0 :: M) R), rep1_snoc. reflexivity.
    + go gC0. gorun (IHc M (S0 :: R)). cbn [chd ctl].
      exact (IHz (S1 :: M) R).
    + go gD0. gorun (IHd M (S0 :: R)). cbn [chd ctl].
      exact (IHz (S0 :: M) R).
Qed.

Definition Bz f := proj1 (four_rules f).
Definition Bo f := proj1 (proj2 (four_rules f)).

(** ** Crossing the gap

    [Bz e] eats one cell of the gap and deepens the wall by one, so the
    hop's crossing is [Bz 0], [Bz 1], ... [Bz (e+b)] chained. *)

Fixpoint ST (e b : nat) : nat :=
  match b with O => Th e | S c => Th e + ST (S e) c end.

Lemma chain : forall b e M R,
  csteps tm_nc (ST e b) (StB, (rep [S0] e ++ S1 :: M, S0, rep [S0] b ++ S1 :: R))
    = Some (StB, (rep [S0] (S (e + b)) ++ S1 :: M, S1, R)).
Proof.
  induction b as [|b IH]; intros e M R; cbn [ST].
  - rewrite Nat.add_0_r. cbn [rep app].
    rewrite (Bz e M (S1 :: R)). reflexivity.
  - expose. gorun (Bz e M (S0 :: (rep [S0] b ++ S1 :: R))). cbn [chd ctl].
    rewrite IH. replace (e + S b) with (S e + b) by lia. reflexivity.
Qed.

(** ** The two sweeps home

    [C] and [D] both walk left over blanks, writing blanks; they differ
    only in what they do to the [S1] they stop on, which is one step
    later. *)

Lemma sweepD : forall k M R,
  csteps tm_nc (S k) (StD, (rep [S0] k ++ S1 :: M, S0, R))
    = Some (StD, (M, S1, rep [S0] (S k) ++ R)).
Proof.
  induction k as [|k IH]; intros M R.
  - cbn [rep app]. go gD0. reflexivity.
  - expose. go gD0. rewrite IH, rep1_snoc. reflexivity.
Qed.

Lemma sweepC : forall k M R,
  csteps tm_nc (S k) (StC, (rep [S0] k ++ S1 :: M, S0, R))
    = Some (StC, (M, S1, rep [S0] (S k) ++ R)).
Proof.
  induction k as [|k IH]; intros M R.
  - cbn [rep app]. go gC0. reflexivity.
  - expose. go gC0. rewrite IH, rep1_snoc. reflexivity.
Qed.

(** ** The anchor family and its two rules *)

Definition P (a b : nat) : cconf :=
  (StA, (rep [S0] a ++ [S1], S0, rep [S0] b ++ [S1])).

Lemma hop : forall a b,
  csteps tm_nc (S (ST 0 b + S (S (S b)))) (P a (S b)) = Some (P (S a) b).
Proof.
  intros a b. unfold P. expose.
  go gA0.
  gorun (chain b 0 (rep [S0] a ++ [S1]) []). rewrite Nat.add_0_l.
  expose. go gB1.
  replace (S (S b)) with (S b + 1) by lia.
  gorun (sweepD b (rep [S0] a ++ [S1]) [S1]).
  expose. go gD1. reflexivity.
Qed.

Lemma wrap : forall a, csteps tm_nc (a + 8) (P a 0) = Some (P 0 (S a)).
Proof.
  intros a. unfold P. cbn [rep app].
  replace (a + 8) with (S (S (S (S (S (S (S a) + 1)))))) by lia.
  go gA0. go gB1. go gD1. go gA1. go gB0.
  gorun (sweepC (S a) [] [S1]).
  expose. go gC1. reflexivity.
Qed.

(** ** The lap: the gap empties, then widens by one *)

Fixpoint Dn (b : nat) : nat :=
  match b with O => 0 | S c => S (ST 0 c + S (S (S c))) + Dn c end.

Lemma descend : forall b a, csteps tm_nc (Dn b) (P a b) = Some (P (a + b) 0).
Proof.
  induction b as [|b IH]; intros a; cbn [Dn].
  - rewrite Nat.add_0_r. reflexivity.
  - gorun (hop a b). rewrite IH. replace (S a + b) with (a + S b) by lia.
    reflexivity.
Qed.

Lemma lap : forall n,
  csteps tm_nc (Dn n + (n + 8)) (P 0 n) = Some (P 0 (S n)).
Proof.
  intros n. gorun (descend n 0). cbn [Nat.add]. apply wrap.
Qed.

(** ** Bootstrap, visits and the theorem *)

Definition Cf (p : positive) : cconf := P 0 (Pos.to_nat p).

Lemma boot_nc : exists t0, stepn tm_nc t0 InitES = Some (lift (Cf 1)).
Proof.
  exists 15.
  assert (H : match csteps tm_nc 15 c0 with
              | Some c => ceqb c (Cf 1)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_nc 15 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

(** [A] and [B] open every lap and [C] follows at once while the gap is
    non-empty; [D] is the sweep home, which the descent reaches. *)
Lemma vis_nc : forall n q,
  exists k c, csteps tm_nc k (P 0 (S n)) = Some c /\ fst c = q.
Proof.
  intros n q.
  assert (HD : csteps tm_nc (Dn (S n) + 2) (P 0 (S n))
                 = Some (StD, (rep [S0] (S n) ++ [S1], S1, [S1]))).
  { gorun (descend (S n) 0). unfold P. cbn [Nat.add rep app].
    go gA0. go gB1. reflexivity. }
  destruct q.
  - exists 0. eexists. split; reflexivity.
  - exists 1. unfold P. expose. eexists.
    split; [go gA0; reflexivity | reflexivity].
  - exists 2. unfold P. expose. eexists.
    split; [go gA0; go gB0; reflexivity | reflexivity].
  - exists (Dn (S n) + 2). eexists. split; [exact HD | reflexivity].
Qed.

(** 1RB0RB_1LC1LD_0LC1RA_0LD0RA never quasihalts. *)
Theorem nqh_1RB0RB_1LC1LD_0LC1RA_0LD0RA : NeverQuasiHaltsSt tm_nc.
Proof.
  apply (glue_neverqh tm_nc Cf 1).
  - exact boot_nc.
  - intros p _. unfold Cf. rewrite Pos2Nat.inj_succ.
    exists (Dn (Pos.to_nat p) + (Pos.to_nat p + 8)), (P 0 (S (Pos.to_nat p))).
    split; [apply lap|]. split; [reflexivity|].
    destruct (Pos.to_nat p) as [|m] eqn:E; cbn [Dn]; lia.
  - intros p q _. unfold Cf.
    destruct (Pos.to_nat p) as [|m] eqn:E.
    + exfalso. pose proof (Pos2Nat.is_pos p). lia.
    + apply vis_nc.
Qed.

Theorem tm_nc_nonhalt : NonHalt tm_nc.
Proof. apply never_qh_nonhalt, nqh_1RB0RB_1LC1LD_0LC1RA_0LD0RA. Qed.
