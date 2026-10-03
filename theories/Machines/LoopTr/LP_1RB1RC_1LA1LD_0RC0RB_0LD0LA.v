(** * LP_1RB1RC_1LA1LD_0RC0RB_0LD0LA: a moving one with a recursive count
    behind it, worked from the right (SCOPING_INSTR 7.4.LE12).

    At its anchor [B] reads the blank right of [1 0^n]; a lap writes the
    marker and erases everything between the left [1] and the marker,
    ending one cell wider: [Cf i = B [0] | 1 0^(i+4)].

    Two erasers, mutually recursive.  [EA a b]: [A] on the first cell of
    [0^(b+1) 1], the wall [1 0^a] on its left, erases the marker and ends
    in [B] just right of it.  [EB a b]: [B] on the first cell of [0^b 1],
    the wall [1 0^a] on its left, erases the wall instead and ends in [A]
    just left of it.  [EA a b] runs [EB 0 b] and then [EA (a-1) (b+1)];
    [EB a b] runs [EA (a-1) 0] and then [EB (a+1) (b-1)].  The proof is a
    strong induction on the measure [a + b], then on [a] (for [EA]) or [b]
    (for [EB]).  The count is again Hanoi-like, but no counter reading is
    needed.

    Hand-stated, kernel-checked.  Axiom footprint: [functional_extensionality_dep]. *)
From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Definition tm_1RB1RC_1LA1LD_0RC0RB_0LD0LA : TM := fun q s => match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB)
  | StA, S1 => Some (mkTrans S1 DR StC)
  | StB, S0 => Some (mkTrans S1 DL StA)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DR StC)
  | StC, S1 => Some (mkTrans S0 DR StB)
  | StD, S0 => Some (mkTrans S0 DL StD)
  | StD, S1 => Some (mkTrans S0 DL StA)
  end.
Local Notation tm := (tm_wrap_trs tm_1RB1RC_1LA1LD_0RC0RB_0LD0LA []).
Local Notation z := (rep [S0]).

(** [rfix] after folding [S0 :: rep [S0] n ++ l] into [rep [S0] (S n) ++ l] *)
Ltac zfix := unfold cL, cR; cbn [chd ctl rep app]; repeat rewrite rep1_fold;
  match goal with |- Reach0 _ ?a ?b => replace b with a; [apply reach0_refl | feq] end.

Lemma csweep : forall b L R, Reach0 tm (cR StC L (z b ++ R)) (cR StC (z b ++ L) R).
Proof. apply sweepR. intros L R. rr 1. r0. Qed.

Lemma dsweep : forall b L R, Reach0 tm (cL StD (z b ++ L) R) (cL StD L (z b ++ R)).
Proof. apply sweepL. intros L R. rr 1. r0. Qed.

Definition EA a b := forall X R,
  Reach1 tm (cR StA (z a ++ S1 :: X) (z (S b) ++ S1 :: R)) (cR StB (z (a + S b + 1) ++ S1 :: X) R).

Definition EB a b := forall X R,
  Reach1 tm (cR StB (z a ++ S1 :: X) (z b ++ S1 :: R)) (cL StA X (z (a + b + 1) ++ S1 :: R)).

Lemma erase : forall n, (forall a b, a + S b = n -> EA a b) /\ (forall a b, a + b = n -> EB a b).
Proof.
  intros n. induction n as [n IH] using lt_wf_ind.
  assert (HB : forall b a, a + b = n -> EB a b).
  { intros b. induction b as [|b IHb]; intros a Hab X R.
    - rr 1. rt (dsweep a (S1 :: X) (S1 :: R)). rr 1. zfix.
    - destruct a as [|a].
      + rr 3. rt (IHb 1 ltac:(lia) X R). zfix.
      + rr 1. rt (proj1 (IH (S a) ltac:(lia)) a 0 ltac:(lia) X (z b ++ S1 :: R)).
        rt (IHb (a + 1 + 1) ltac:(lia) X R). zfix. }
  split; [|intros a b Hab; exact (HB b a Hab)].
  intros a. induction a as [|a IHa]; intros b Hab X R.
  - rr 1. rt (proj2 (IH b ltac:(lia)) 0 b eq_refl (S1 :: X) R).
    rr 1. rt (csweep (0 + b + 1) (S1 :: X) (S1 :: R)). rr 1. zfix.
  - rr 1. rt (proj2 (IH b ltac:(lia)) 0 b eq_refl (z (S a) ++ S1 :: X) R).
    rt (IHa (0 + b + 1) ltac:(lia) X R). zfix.
Qed.

Definition Cf (i : nat) : cconf := (StB, (z (i + 4) ++ [S1], S0, [])).

Lemma lap : forall i, Reach1 tm (Cf i) (Cf (S i)).
Proof.
  intros i. unfold Cf. replace (i + 4) with (S (i + 3)) by lia. cbn [rep app].
  rr 1. rt (proj1 (erase (i + 3 + 1)) (i + 3) 0 ltac:(lia) [] []). zfix.
Qed.

Lemma fires : forall t, ~ In t [] -> forall i, Fires tm (Cf i) t.
Proof.
  intros [q s] _ i. unfold Cf. replace (i + 4) with (S (S (S (S i)))) by lia. cbn [rep app].
  destruct q, s; fire_find.
Qed.

Theorem nqhtr_1RB1RC_1LA1LD_0RC0RB_0LD0LA : NeverQuasiHaltsTr tm_1RB1RC_1LA1LD_0RC0RB_0LD0LA.
Proof.
  apply (boardS_neverqhtr tm_1RB1RC_1LA1LD_0RC0RB_0LD0LA [] Cf lap fires 57).
  apply boot_ok. vm_compute. reflexivity.
Qed.
