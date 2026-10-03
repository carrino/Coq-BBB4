(** * LP_0RB1LC_1LA0RC_1LD1RB_1LA0LD (SCOPING_INSTR 7.4.LE10)

    The same scheme as [LP_0RB0LB_1LC0RD_1LA0LA_1LB1RB] without the
    [11] prefix.  The digits [1111] / [1011] / [0111] start right after
    [A [0]].  The walk back takes four steps per two pairs ([awalk] in the
    shape [FA]).  [cU w] and a count of the low digits run per digit
    ([loop]); [pa] / [pb] / [pc] and two counts add a digit, two cells to
    the left: [A [0] 1111 (0111)^(i+1)] becomes
    [A [0] 1111 (0111)^(i+2)].

    Hand-stated, kernel-checked.  Axiom footprint: [functional_extensionality_dep]. *)
From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Definition tm_0RB1LC_1LA0RC_1LD1RB_1LA0LD : TM := fun q s => match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB) | StA, S1 => Some (mkTrans S1 DL StC)
  | StB, S0 => Some (mkTrans S1 DL StA) | StB, S1 => Some (mkTrans S0 DR StC)
  | StC, S0 => Some (mkTrans S1 DL StD) | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S1 DL StA) | StD, S1 => Some (mkTrans S0 DL StD)
  end.
Local Notation tm := (tm_wrap_trs tm_0RB1LC_1LA0RC_1LD1RB_1LA0LD []).
Local Notation O := [S1; S1; S1; S1].
Local Notation Z := [S1; S0; S1; S1].
Local Notation U := [S0; S1; S1; S1].
Local Notation Q := [S1; S1].

Lemma bwalk : forall n L R, Reach0 tm (cR StB L (rep Q n ++ R)) (cR StB (rep [S1; S0] n ++ L) R).
Proof. apply sweepR. intros L R. rr 2. r0. Qed.

Definition FA (L R : list Sym) : cconf := (StA, (L, S1, R)).

Lemma awalk : forall n L R,
  Reach0 tm (FA (rep [S0; S1; S0; S1] n ++ L) R) (FA L (rep Z n ++ R)).
Proof. apply sweepFL. intros L R. unfold FA. rr 4. r0. Qed.

Lemma ofull : forall j, rep O j = rep Q (j + j).
Proof. intros j. rewrite <- rep_app_dbl. reflexivity. Qed.

(** after the walk over [2 j + 2] pairs and the turn: [A] on the last pair's 1 *)
Lemma back : forall j L R,
  Reach1 tm (FA (S0 :: rep [S1; S0] (S (j + j)) ++ S0 :: L) R) (StA, (L, S0, rep Z (S j) ++ R)).
Proof.
  intros j L R. rewrite (rep_shift S0 S1 (S (j + j))), rep_S_r, <- app_assoc, <- rep_app_dbl.
  eapply reach01; [apply (awalk j ([S0; S1] ++ S0 :: S0 :: L) R)|]. unfold FA. rr 4. r0.
Qed.

Lemma c1 : forall j L Y,
  Reach1 tm (StA, (L, S0, rep O j ++ Z ++ Y)) (StA, (L, S0, rep Z j ++ O ++ Y)).
Proof.
  intros [|j] L Y; [rr 4; r0|].
  rewrite ofull. replace (S j + S j) with (S (S (j + j))) by lia.
  rr 1. rt (bwalk (S (S (j + j))) (S0 :: L) (Z ++ Y)). rr 3.
  exact (reach1_0 _ _ _ (back j L (O ++ Y))).
Qed.


Lemma cU : forall j L Y,
  Reach1 tm (StA, (L, S0, rep O j ++ U ++ Y)) (StA, (L, S0, rep Z j ++ O ++ Y)).
Proof.
  intros [|j] L Y; [rr 2; r0|].
  rewrite ofull. replace (S j + S j) with (S (S (j + j))) by lia.
  rr 1. rt (bwalk (S (S (j + j))) (S0 :: L) (U ++ Y)). rr 1.
  exact (reach1_0 _ _ _ (back j L (O ++ Y))).
Qed.

Lemma pa : forall j L,
  Reach1 tm (StA, (L, S0, rep O (S j) ++ [])) (StA, (L, S0, rep Z (S j) ++ [S1])).
Proof.
  intros j L. rewrite ofull. replace (S j + S j) with (S (S (j + j))) by lia.
  rr 1. rt (bwalk (S (S (j + j))) (S0 :: L) []). rr 1.
  exact (reach1_0 _ _ _ (back j L [S1])).
Qed.

Lemma pb : forall j L,
  Reach1 tm (StA, (L, S0, rep O (S j) ++ [S1])) (StA, (L, S0, rep Z (S j) ++ [S1; S1])).
Proof.
  intros j L. rewrite ofull. replace (S j + S j) with (S (S (j + j))) by lia.
  rr 1. rt (bwalk (S (S (j + j))) (S0 :: L) [S1]). rr 3.
  exact (reach1_0 _ _ _ (back j L [S1; S1])).
Qed.

Lemma pc_mid : forall j L,
  Reach1 tm (StA, (L, S0, rep O (S j) ++ Q)) (FA (S0 :: S0 :: L) (rep Z (S j) ++ [S1])).
Proof.
  intros j L. rewrite ofull. replace (S j + S j) with (S (S (j + j))) by lia.
  change (rep Q (S (S (j + j))) ++ Q) with (rep Q (S (S (j + j))) ++ Q ++ []).
  rewrite (app_assoc (rep Q _) Q []), <- rep_S_r.
  rr 1. rt (bwalk (S (S (S (j + j)))) (S0 :: L) []). rr 1.
  change (StA, (S0 :: S1 :: S0 :: S1 :: S0 :: rep [S1; S0] (j + j) ++ S0 :: L, S1, [S1]))
    with (FA (S0 :: rep [S1; S0] (S (S (j + j))) ++ S0 :: L) [S1]).
  rewrite (rep_shift S0 S1 (S (S (j + j)))).
  replace (S (S (j + j))) with (S j + S j) by lia. rewrite <- rep_app_dbl.
  exact (awalk (S j) (S0 :: S0 :: L) [S1]).
Qed.

Lemma pc : forall j L,
  Reach1 tm (StA, (L, S0, rep O (S j) ++ Q)) (cL StA L (O ++ rep U (S j))).
Proof.
  intros j L. rt1 (pc_mid j L). unfold FA. rr 3.
  rewrite (rep_rot S1 [S0; S1; S1] j []), app_nil_r. r0.
Qed.

Lemma count : forall w L Y,
  Reach0 tm (StA, (L, S0, rep Z w ++ Y)) (StA, (L, S0, rep O w ++ Y)).
Proof.
  intros w L. apply (count_from_carry_lt tm (fun l => (StA, (L, S0, l))) Z O w).
  intros k Y _. exact (c1 k L Y).
Qed.

Lemma loop : forall r w L Y,
  Reach0 tm (StA, (L, S0, rep O w ++ rep U r ++ Y)) (StA, (L, S0, rep O (w + r) ++ Y)).
Proof.
  induction r as [|r IH]; intros w L Y; [rfix|].
  change (rep U (S r) ++ Y) with (U ++ rep U r ++ Y).
  rt (cU w L (rep U r ++ Y)). rt (count w L (O ++ rep U r ++ Y)).
  rewrite (app_assoc (rep O w) O), rep_comm. change (O ++ rep O w) with (rep O (S w)).
  rt (IH (S w) L Y). rfix.
Qed.

Definition Cf (i : nat) : cconf := (StA, ([], S0, O ++ rep U (S i))).

Lemma topa : forall i, Reach0 tm (Cf i) (StA, ([], S0, rep O (S (S i)) ++ [])).
Proof.
  intros i. unfold Cf. rewrite <- (app_nil_r (rep U (S i))).
  change (O ++ rep U (S i) ++ []) with (rep O 1 ++ rep U (S i) ++ []).
  rt (loop (S i) 1 [] []). r0.
Qed.

Lemma tolast : forall i, Reach0 tm (Cf i) (StA, ([], S0, rep O (S (S i)) ++ Q)).
Proof.
  intros i. rt (topa i).
  rt (pa (S i) []). rt (count (S (S i)) [] [S1]). rt (pb (S i) []). exact (count (S (S i)) [] Q).
Qed.

Lemma lap : forall i, Reach1 tm (Cf i) (Cf (S i)).
Proof. intros i. eapply reach01; [apply tolast|]. exact (pc (S i) []). Qed.

Lemma fires : forall t, ~ In t [] -> forall i, Fires tm (Cf i) t.
Proof.
  intros [q s] _ i. destruct q, s;
  first [ unfold Cf; fire_find
        | eapply fire_back; [apply topa|]; fire_find
        | eapply fire_back; [apply tolast|]; eapply fire_back; [apply reach1_0, pc_mid|]; unfold FA; fire_find ].
Qed.

Theorem nqhtr_0RB1LC_1LA0RC_1LD1RB_1LA0LD : NeverQuasiHaltsTr tm_0RB1LC_1LA0RC_1LD1RB_1LA0LD.
Proof.
  apply (boardS_neverqhtr _ [] Cf lap fires 58).
  apply boot_ok. vm_compute. reflexivity.
Qed.
