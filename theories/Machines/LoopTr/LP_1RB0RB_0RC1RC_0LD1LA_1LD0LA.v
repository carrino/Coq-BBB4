(** * LP_1RB0RB_0RC1RC_0LD1LA_1LD0LA (SCOPING_INSTR 7.4.LE10)

    A Gray-style counter.  The macro step at [A] on cell [j] flips cell
    [j]; if cell [j+2] is 1, [A] moves to [j+1], else [D] moves to [j+1].
    [D] writes 1 over 0s leftwards and turns a 1 into 0, then hands back to
    [A].  Entered at its left end, a region exits one cell to the left with
    exactly one bit flipped (a Gray increment).  There are four entry
    shapes, [E1] .. [E4] (head [1]/[0] before [0 1^k 0] / [1^k 0]).  They
    are mutually recursive and are proved together by induction on [k].
    The lap is [E3]: [A [0] 0 1^n 0 ->+ A [0] 0 1^(n+1) 0], one cell to the
    left.  [walk] carries the head along [1^m] to where [C0], [D0] and [D1]
    fire.

    Hand-stated, kernel-checked.  Axiom footprint: [functional_extensionality_dep]. *)
From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Definition tm_1RB0RB_0RC1RC_0LD1LA_1LD0LA : TM := fun q s => match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB) | StA, S1 => Some (mkTrans S0 DR StB)
  | StB, S0 => Some (mkTrans S0 DR StC) | StB, S1 => Some (mkTrans S1 DR StC)
  | StC, S0 => Some (mkTrans S0 DL StD) | StC, S1 => Some (mkTrans S1 DL StA)
  | StD, S0 => Some (mkTrans S1 DL StD) | StD, S1 => Some (mkTrans S0 DL StA)
  end.
Local Notation tm := (tm_wrap_trs tm_1RB0RB_0RC1RC_0LD1LA_1LD0LA []).
Local Notation o := (rep [S1]).
Local Notation z := (rep [S0]).

Definition E1 k := forall L Y,
  Reach1 tm (StA, (L, S1, S0 :: o k ++ S0 :: Y)) (cL StD L (S1 :: S1 :: o k ++ S0 :: Y)).
Definition E2 k := forall L Y,
  Reach1 tm (StA, (L, S0, o k ++ S0 :: Y)) (cL StD L (S1 :: o k ++ S0 :: Y)).
Definition E3 k := forall L Y,
  Reach1 tm (StA, (L, S0, S0 :: o k ++ S0 :: Y)) (cL StA L (S0 :: S1 :: o k ++ S0 :: Y)).
Definition E4 k := forall L Y,
  Reach1 tm (StA, (L, S1, o k ++ S0 :: Y)) (cL StA L (S0 :: o k ++ S0 :: Y)).

Lemma ee : forall k, E1 k /\ E3 k /\ E2 (S k) /\ E4 (S k).
Proof.
  induction k as [|k (H1 & H3 & H2 & H4)].
  - assert (e1 : E1 0) by (intros L Y; rr 5; r0).
    assert (e3 : E3 0) by (intros L Y; rr 5; r0).
    split; [exact e1|]. split; [exact e3|]. split.
    + intros L Y. rr 4. rt (e1 L Y). r0.
    + intros L Y. rr 4. rt (e3 L Y). r0.
  - assert (e1 : E1 (S k)).
    { intros L Y. rr 3. rt (H2 (S0 :: L) Y). rr 1. r0. }
    assert (e3 : E3 (S k)).
    { intros L Y. rr 3. rt (H2 (S1 :: L) Y). rr 1. r0. }
    split; [exact e1|]. split; [exact e3|]. split.
    + intros L Y. rr 3. rt (H4 (S1 :: L) Y). rt (e1 L Y). r0.
    + intros L Y. rr 3. rt (H4 (S0 :: L) Y). rt (e3 L Y). r0.
Qed.

Lemma walk : forall m L Y,
  Reach0 tm (StA, (L, S1, o (S m) ++ S0 :: Y)) (StA, (z m ++ L, S1, S1 :: S0 :: Y)).
Proof.
  induction m as [|m IH]; intros L Y; [r0|].
  rr 3. rt (IH (S0 :: L) Y). rewrite rep1_snoc. r0.
Qed.

Definition Cf (i : nat) : cconf := (StA, ([], S0, S0 :: o (S (S i)) ++ [S0])).

Lemma lap : forall i, Reach1 tm (Cf i) (Cf (S i)).
Proof. intros i. unfold Cf. rt1 (proj1 (proj2 (ee (S (S i)))) [] []). r0. Qed.

Lemma tail6 : forall i, Reach0 tm (Cf i) (StA, (z i ++ [S1; S1], S1, S1 :: S0 :: [])).
Proof. intros i. unfold Cf. rr 6. exact (walk i [S1; S1] []). Qed.

Lemma fires : forall t, ~ In t [] -> forall i, Fires tm (Cf i) t.
Proof.
  intros [q s] _ i. destruct q, s;
    first [ unfold Cf; fire_find | eapply fire_back; [apply tail6|]; fire_find ].
Qed.

Theorem nqhtr_1RB0RB_0RC1RC_0LD1LA_1LD0LA : NeverQuasiHaltsTr tm_1RB0RB_0RC1RC_0LD1LA_1LD0LA.
Proof.
  apply (boardS_neverqhtr _ [] Cf lap fires 18).
  apply boot_ok. vm_compute. reflexivity.
Qed.
