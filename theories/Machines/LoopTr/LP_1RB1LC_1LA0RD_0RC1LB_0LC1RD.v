(** * LP_1RB1LC_1LA0RD_0RC1LB_0LC1RD (SCOPING_INSTR 7.4.LE10)

    LE8's "counts at width-dependent offsets".  The counter is read
    LEFTWARDS from [D] on the blank right of the tape: 3-cell digits
    [111] = 0, [101] = 1, LSB nearest.  Its top sits in a short tail
    ([01], [1101], [1001], [1011]).  Every carry [cc] walks [C] left over
    the [101] digits ([cwalk]) and sweeps [D] right back ([dsweep]).  A lap
    is a full count of [w] digits, [t1], then four counts of [w + 1]
    digits separated by [t2] / [t3] / [t4], then [t5]:
    [(111)^w 101] becomes [(111)^(w+2) 101], for odd [w].

    Hand-stated, kernel-checked.  Axiom footprint: [functional_extensionality_dep]. *)
From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Definition tm_1RB1LC_1LA0RD_0RC1LB_0LC1RD : TM := fun q s => match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB) | StA, S1 => Some (mkTrans S1 DL StC)
  | StB, S0 => Some (mkTrans S1 DL StA) | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S0 DR StC) | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StC) | StD, S1 => Some (mkTrans S1 DR StD)
  end.
Local Notation tm := (tm_wrap_trs tm_1RB1LC_1LA0RD_0RC1LB_0LC1RD []).
Local Notation O := [S1; S0; S1].
Local Notation Z := [S1; S1; S1].

(** the counter is read leftwards from [D] on the blank right of the tape *)
Definition Dc (L : list Sym) : cconf := (StD, (L, S0, [])).

Lemma cwalk : forall n L R, Reach0 tm (cL StC (rep O n ++ L) R) (cL StC L (rep Z n ++ R)).
Proof. apply sweepL. intros L R. rr 3. r0. Qed.

Lemma dsweep : forall n L R, Reach0 tm (cR StD L (rep [S1] n ++ R)) (cR StD (rep [S1] n ++ L) R).
Proof. apply sweepR. intros L R. rr 1. r0. Qed.

Lemma cc : forall j X, Reach1 tm (Dc (rep O j ++ Z ++ X)) (Dc (rep Z j ++ O ++ X)).
Proof.
  intros j X. unfold Dc. rr 1. rt (cwalk j (Z ++ X) [S0]). rr 2.
  rewrite rep_triple.
  change (StD, (S0 :: S1 :: X, S1, rep [S1] (j + j + j) ++ [S0]))
    with (cR StD (S0 :: S1 :: X) (rep [S1] (S (j + j + j)) ++ [S0])).
  rt (dsweep (S (j + j + j)) (S0 :: S1 :: X) [S0]).
  cbn [rep app]. rewrite rep1_snoc. r0.
Qed.

Lemma t1 : forall m, Reach1 tm (Dc (rep O (S m) ++ [])) (Dc (rep Z (S m) ++ [S0; S1])).
Proof.
  intros m. unfold Dc. rr 1. rt (cwalk (S m) [] [S0]). rr 5.
  rewrite !rep_triple.
  change (StD, ([S0; S1], S1, ?R)) with (cR StD [S0; S1] (S1 :: R)).
  match goal with |- Reach0 _ (cR StD _ ?R) _ =>
    replace R with (rep [S1] (3 + (m + m + m)) ++ [S0]) by (cbn [rep app]; reflexivity) end.
  rt (dsweep (3 + (m + m + m)) [S0; S1] [S0]).
  rewrite ?rep1_snoc, ?rep1_fold. rfix.
Qed.

Lemma t2 : forall m, Reach1 tm (Dc (rep O (S m) ++ [S0; S1])) (Dc (rep Z (S m) ++ [S1; S1; S0; S1])).
Proof.
  intros m. unfold Dc. rr 1. rt (cwalk (S m) [S0; S1] [S0]). rr 9.
  rewrite !rep_triple.
  change (StD, ([S0; S1], S1, ?R)) with (cR StD [S0; S1] (S1 :: R)).
  match goal with |- Reach0 _ (cR StD _ ?R) _ =>
    replace R with (rep [S1] (5 + (m + m + m)) ++ [S0]) by (cbn [rep app]; reflexivity) end.
  rt (dsweep (5 + (m + m + m)) [S0; S1] [S0]).
  rewrite ?rep1_snoc, ?rep1_fold. rfix.
Qed.

Lemma t3 : forall m, Reach1 tm (Dc (rep O m ++ [S1; S1; S0; S1])) (Dc (rep Z m ++ [S1; S0; S0; S1])).
Proof.
  intros m. unfold Dc. rr 1. rt (cwalk m [S1; S1; S0; S1] [S0]). rr 2.
  rewrite !rep_triple.
  change (StD, ([S0; S0; S1], S1, ?R)) with (cR StD [S0; S0; S1] (S1 :: R)).
  match goal with |- Reach0 _ (cR StD _ ?R) _ =>
    replace R with (rep [S1] (1 + (m + m + m)) ++ [S0]) by (cbn [rep app]; reflexivity) end.
  rt (dsweep (1 + (m + m + m)) [S0; S0; S1] [S0]).
  rewrite ?rep1_snoc, ?rep1_fold. rfix.
Qed.

Lemma t4 : forall m, Reach1 tm (Dc (rep O m ++ [S1; S0; S0; S1])) (Dc (rep Z m ++ [S1; S0; S1; S1])).
Proof.
  intros m. unfold Dc. rr 1. rt (cwalk m [S1; S0; S0; S1] [S0]). rr 4.
  rewrite !rep_triple.
  change (StD, ([S0; S1; S1], S1, ?R)) with (cR StD [S0; S1; S1] (S1 :: R)).
  match goal with |- Reach0 _ (cR StD _ ?R) _ =>
    replace R with (rep [S1] (1 + (m + m + m)) ++ [S0]) by (cbn [rep app]; reflexivity) end.
  rt (dsweep (1 + (m + m + m)) [S0; S1; S1] [S0]).
  rewrite ?rep1_snoc, ?rep1_fold. rfix.
Qed.

Lemma t5 : forall m, Reach1 tm (Dc (rep O m ++ [S1; S0; S1; S1])) (Dc (rep Z (S m) ++ O)).
Proof.
  intros m. unfold Dc. rr 1. rt (cwalk m [S1; S0; S1; S1] [S0]). rr 7.
  rewrite !rep_triple.
  change (StD, ([S0; S1], S1, ?R)) with (cR StD [S0; S1] (S1 :: R)).
  match goal with |- Reach0 _ (cR StD _ ?R) _ =>
    replace R with (rep [S1] (4 + (m + m + m)) ++ [S0]) by (cbn [rep app]; reflexivity) end.
  rt (dsweep (4 + (m + m + m)) [S0; S1] [S0]).
  rewrite ?rep1_snoc, ?rep1_fold. rfix.
Qed.


Lemma count : forall w X, Reach0 tm (Dc (rep Z w ++ X)) (Dc (rep O w ++ X)).
Proof.
  intros w. apply (count_from_carry_lt tm Dc Z O w). intros k Y _. exact (cc k Y).
Qed.

Definition Cf (i : nat) : cconf := Dc (rep Z (S (i + i)) ++ O).

Lemma lap_w : forall w, Reach1 tm (Dc (rep Z (S w) ++ O)) (Dc (rep Z (S (S (S w))) ++ O)).
Proof.
  intros w.
  eapply reach01; [apply (count (S w) O)|].
  change (rep O (S w) ++ O) with (rep O (S w) ++ O ++ []). rewrite app_assoc, rep_comm.
  change (O ++ rep O (S w)) with (rep O (S (S w))).
  rt1 (t1 (S w)). rt (count (S (S w)) [S0; S1]). rt (t2 (S w)).
  rt (count (S (S w)) [S1; S1; S0; S1]). rt (t3 (S (S w))).
  rt (count (S (S w)) [S1; S0; S0; S1]). rt (t4 (S (S w))).
  rt (count (S (S w)) [S1; S0; S1; S1]). rt (t5 (S (S w))). r0.
Qed.

Lemma lap : forall i, Reach1 tm (Cf i) (Cf (S i)).
Proof.
  intros i. unfold Cf. replace (S (S i + S i)) with (S (S (S (i + i)))) by lia. apply lap_w.
Qed.

Lemma tot1 : forall i, Reach0 tm (Cf i) (Dc (rep O (S (S (i + i))) ++ [])).
Proof.
  intros i. unfold Cf. rt (count (S (i + i)) O).
  change (rep O (S (i + i)) ++ O) with (rep O (S (i + i)) ++ O ++ []). rewrite app_assoc, rep_comm. r0.
Qed.

Lemma fires : forall t, ~ In t [] -> forall i, Fires tm (Cf i) t.
Proof.
  intros [q s] _ i. destruct q, s;
  first [ unfold Cf, Dc; fire_find
        | eapply fire_back; [apply tot1|]; unfold Dc; eapply fire_back;
          [rr 1; rt (cwalk (S (S (i + i))) [] [S0]); r0|]; fire_find ].
Qed.

Theorem nqhtr_1RB1LC_1LA0RD_0RC1LB_0LC1RD : NeverQuasiHaltsTr tm_1RB1LC_1LA0RD_0RC1LB_0LC1RD.
Proof.
  apply (boardS_neverqhtr _ [] Cf lap fires 32).
  apply boot_ok. vm_compute. reflexivity.
Qed.
