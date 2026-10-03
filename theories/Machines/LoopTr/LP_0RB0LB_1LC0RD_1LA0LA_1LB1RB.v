(** * LP_0RB0LB_1LC0RD_1LA0LA_1LB1RB (SCOPING_INSTR 7.4.LE10)

    LE8's "pairs of counts sliding two cells per pair".  A binary counter
    over 4-cell digits after [A [0] 11]: [1111] = 1, [1011] = a touched 0,
    [0111] = an untouched 0.  [B] walks right writing [01] over [11]
    pairs ([bwalk]).  [A] walks back two pairs at a time in the shape
    [FA] ([awalk], [sweepFL]).  The carries [c1] / [cU] are linear.  A lap
    counts the whole width by [loop] ([cU w], then a count of the [w]
    touched digits), then three passes [pa] / [pb] / [pc], each followed
    by a count, add one digit: [A [0] 11 (0111)^(i+1)] becomes
    [A [0] 11 (0111)^(i+2)].

    Hand-stated, kernel-checked.  Axiom footprint: [functional_extensionality_dep]. *)
From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Definition tm_0RB0LB_1LC0RD_1LA0LA_1LB1RB : TM := fun q s => match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB) | StA, S1 => Some (mkTrans S0 DL StB)
  | StB, S0 => Some (mkTrans S1 DL StC) | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StA) | StC, S1 => Some (mkTrans S0 DL StA)
  | StD, S0 => Some (mkTrans S1 DL StB) | StD, S1 => Some (mkTrans S1 DR StB)
  end.
Local Notation tm := (tm_wrap_trs tm_0RB0LB_1LC0RD_1LA0LA_1LB1RB []).
Local Notation O := [S1; S1; S1; S1].
Local Notation Z := [S1; S0; S1; S1].
Local Notation U := [S0; S1; S1; S1].
Local Notation Q := [S1; S1].

(** [B] walks right over [11] pairs writing [01] *)
Lemma bwalk : forall n L R, Reach0 tm (cR StB L (rep Q n ++ R)) (cR StB (rep [S1; S0] n ++ L) R).
Proof. apply sweepR. intros L R. rr 2. r0. Qed.

(** the walk back: [A] on a 0 before a 0, two [01] pairs at a time *)
Definition FA (L R : list Sym) : cconf := (StA, (L, S0, S0 :: R)).

Lemma awalk : forall n L R,
  Reach0 tm (FA (rep [S1; S0; S1; S0] n ++ L) R) (FA L (rep Z n ++ R)).
Proof. apply sweepFL. intros L R. unfold FA. rr 6. r0. Qed.

Lemma back : forall j L R,
  Reach1 tm (FA (rep [S1; S0] (j + j) ++ S0 :: L) R) (StA, (L, S0, Q ++ rep Z j ++ R)).
Proof.
  intros j L R. rewrite <- rep_app_dbl. cbn [app].
  eapply reach01; [apply (awalk j (S0 :: L) R)|]. unfold FA. rr 3. r0.
Qed.

Lemma pre : forall j, Q ++ rep O j = rep Q (1 + (j + j)).
Proof. intros j. change (rep Q (1 + (j + j))) with (Q ++ rep Q (j + j)). rewrite <- rep_app_dbl. reflexivity. Qed.

Lemma c1 : forall j L Y,
  Reach1 tm (StA, (L, S0, Q ++ rep O j ++ Z ++ Y)) (StA, (L, S0, Q ++ rep Z j ++ O ++ Y)).
Proof.
  intros j L Y. rewrite app_assoc, pre. rr 1. rt (bwalk (1 + (j + j)) (S0 :: L) (Z ++ Y)). rr 4.
  exact (reach1_0 _ _ _ (back j L (O ++ Y))).
Qed.

Lemma cU : forall j L Y,
  Reach1 tm (StA, (L, S0, Q ++ rep O j ++ U ++ Y)) (StA, (L, S0, Q ++ rep Z j ++ O ++ Y)).
Proof.
  intros j L Y. rewrite app_assoc, pre. rr 1. rt (bwalk (1 + (j + j)) (S0 :: L) (U ++ Y)). rr 2.
  exact (reach1_0 _ _ _ (back j L (O ++ Y))).
Qed.

Lemma pa : forall k L,
  Reach1 tm (StA, (L, S0, Q ++ rep O k ++ [])) (StA, (L, S0, Q ++ rep Z k ++ [S1])).
Proof.
  intros k L. rewrite app_assoc, pre. rr 1. rt (bwalk (1 + (k + k)) (S0 :: L) []). rr 2.
  exact (reach1_0 _ _ _ (back k L [S1])).
Qed.

Lemma pb : forall k L,
  Reach1 tm (StA, (L, S0, Q ++ rep O k ++ [S1])) (StA, (L, S0, Q ++ rep Z k ++ [S1; S1])).
Proof.
  intros k L. rewrite app_assoc, pre. rr 1. rt (bwalk (1 + (k + k)) (S0 :: L) [S1]). rr 4.
  exact (reach1_0 _ _ _ (back k L [S1; S1])).
Qed.

Lemma pc : forall k L,
  Reach1 tm (StA, (L, S0, Q ++ rep O k ++ Q)) (cL StA L (Q ++ rep U (S k))).
Proof.
  intros k L. rewrite app_assoc, pre, <- rep_S_r, <- (app_nil_r (rep Q (S (1 + (k + k))))). rr 1.
  rt (bwalk (S (1 + (k + k))) (S0 :: L) []). rr 2.
  change (S1 :: S0 :: rep [S1; S0] (k + k) ++ S0 :: L)
    with ([S1; S0] ++ rep [S1; S0] (k + k) ++ S0 :: L).
  rewrite <- rep_snoc, <- rep_app_dbl.
  rt (awalk k ([S1; S0] ++ S0 :: L) [S1]). unfold FA. rr 6.
  rewrite (rep_rot S1 [S0; S1; S1] k []), app_nil_r. r0.
Qed.

Lemma count : forall w L Y,
  Reach0 tm (StA, (L, S0, Q ++ rep Z w ++ Y)) (StA, (L, S0, Q ++ rep O w ++ Y)).
Proof.
  intros w L. apply (count_from_carry_lt tm (fun l => (StA, (L, S0, Q ++ l))) Z O w).
  intros k Y _. exact (c1 k L Y).
Qed.

Lemma loop : forall r w L Y,
  Reach0 tm (StA, (L, S0, Q ++ rep O w ++ rep U r ++ Y)) (StA, (L, S0, Q ++ rep O (w + r) ++ Y)).
Proof.
  induction r as [|r IH]; intros w L Y; [rfix|].
  change (rep U (S r) ++ Y) with (U ++ rep U r ++ Y).
  rt (cU w L (rep U r ++ Y)). rt (count w L (O ++ rep U r ++ Y)).
  rewrite (app_assoc (rep O w) O), rep_comm. change (O ++ rep O w) with (rep O (S w)).
  rt (IH (S w) L Y). rfix.
Qed.

Definition Cf (i : nat) : cconf := (StA, ([], S0, Q ++ rep U (S i))).

Lemma tolast : forall i, Reach0 tm (Cf i) (StA, ([], S0, Q ++ rep O (S i) ++ Q)).
Proof.
  intros i. unfold Cf. rewrite <- (app_nil_r (rep U (S i))).
  rt (loop (S i) 0 [] []). cbn [Nat.add].
  rt (pa (S i) []). rt (count (S i) [] [S1]). rt (pb (S i) []). exact (count (S i) [] Q).
Qed.

Lemma lap : forall i, Reach1 tm (Cf i) (Cf (S i)).
Proof. intros i. eapply reach01; [apply tolast|]. exact (pc (S i) []). Qed.

Lemma pc_mid : forall i,
  Reach0 tm (StA, ([], S0, Q ++ rep O (S i) ++ Q)) (FA (S1 :: S0 :: rep [S1; S0] (S i + S i) ++ [S0]) [S1]).
Proof.
  intros i. rewrite app_assoc, pre, <- rep_S_r, <- (app_nil_r (rep Q (S (1 + (S i + S i))))). rr 1.
  rt (bwalk (S (1 + (S i + S i))) [S0] []). rr 2. r0.
Qed.

Lemma topb : forall i, Reach0 tm (Cf i) (StA, ([], S0, Q ++ rep Z (S i) ++ [S1])).
Proof.
  intros i. unfold Cf. rewrite <- (app_nil_r (rep U (S i))).
  rt (loop (S i) 0 [] []). cbn [Nat.add]. exact (reach1_0 _ _ _ (pa (S i) [])).
Qed.

Lemma fires : forall t, ~ In t [] -> forall i, Fires tm (Cf i) t.
Proof.
  intros [q s] _ i. destruct q, s;
  first [ unfold Cf; fire_find
        | eapply fire_back; [apply topb|]; fire_find
        | eapply fire_back; [apply tolast|]; eapply fire_back; [apply pc_mid|]; unfold FA; fire_find ].
Qed.

Theorem nqhtr_0RB0LB_1LC0RD_1LA0LA_1LB1RB : NeverQuasiHaltsTr tm_0RB0LB_1LC0RD_1LA0LA_1LB1RB.
Proof.
  apply (boardS_neverqhtr _ [] Cf lap fires 34).
  apply boot_ok. vm_compute. reflexivity.
Qed.

