(** * LP_1RB1RC_1LC1LB_1LD1RA_0RC0LD (SCOPING_INSTR 7.4.LE10)

    LE8's "counts at width-dependent offsets".  At the left end, the
    [D [0]] anchor reads a binary counter over 3-cell digits [100] = 1,
    [000] = 0, LSB first.  Its top two digits sit in a short tail
    ([01], [11], [001], [101]).  Every carry [kk] walks [C] right over the
    [100] digits ([cwalk]), writes the 1 and sweeps [D] back.  A lap
    converts [1^(6i+5)] to digits ([x0], two cells per walk step).  Then
    come four full counts of the [2i+2] low digits, separated by the tail
    steps [kk] / [x2] / [kk], and [x4] turns everything into ones two
    cells further left: [D [0] 1^(6i+5)] becomes [D [0] 1^(6i+11)].

    Hand-stated, kernel-checked.  Axiom footprint: [functional_extensionality_dep]. *)
From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Definition tm_1RB1RC_1LC1LB_1LD1RA_0RC0LD : TM := fun q s => match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB) | StA, S1 => Some (mkTrans S1 DR StC)
  | StB, S0 => Some (mkTrans S1 DL StC) | StB, S1 => Some (mkTrans S1 DL StB)
  | StC, S0 => Some (mkTrans S1 DL StD) | StC, S1 => Some (mkTrans S1 DR StA)
  | StD, S0 => Some (mkTrans S0 DR StC) | StD, S1 => Some (mkTrans S0 DL StD)
  end.
Local Notation tm := (tm_wrap_trs tm_1RB1RC_1LC1LB_1LD1RA_0RC0LD []).
Local Notation O := [S1; S0; S0].
Local Notation Z := [S0; S0; S0].

Lemma cwalk : forall n L R, Reach0 tm (cR StC L (rep O n ++ R)) (cR StC (rep [S1; S1; S1] n ++ L) R).
Proof. apply sweepR. intros L R. rr 5. r0. Qed.

Lemma c2walk : forall n L R, Reach0 tm (cR StC L (rep [S1; S1] n ++ R)) (cR StC (rep [S1; S1] n ++ L) R).
Proof. apply sweepR. intros L R. rr 2. r0. Qed.

Lemma dsweep : forall n L R, Reach0 tm (cL StD (rep [S1] n ++ L) R) (cL StD L (rep [S0] n ++ R)).
Proof. apply sweepL. intros L R. rr 1. r0. Qed.

Lemma bsweep : forall n L R, Reach0 tm (cL StB (rep [S1] n ++ L) R) (cL StB L (rep [S1] n ++ R)).
Proof. apply sweepL. intros L R. rr 1. r0. Qed.

(** the carry into a 0: walk right over [100] digits, write 1, sweep back *)
Lemma kk : forall j L Y,
  Reach1 tm (StD, (L, S0, rep O j ++ S0 :: Y)) (StD, (L, S0, rep Z j ++ S1 :: Y)).
Proof.
  intros j L Y. rr 1. rt (cwalk j (S0 :: L) (S0 :: Y)). rr 1.
  rewrite rep_triple. rt (dsweep (j + j + j) (S0 :: L) (S1 :: Y)). rewrite rep_triple. r0.
Qed.

Lemma count : forall w L Y,
  Reach0 tm (StD, (L, S0, rep Z w ++ Y)) (StD, (L, S0, rep O w ++ Y)).
Proof.
  intros w L. apply (count_from_carry_lt tm (fun l => (StD, (L, S0, l))) Z O w).
  intros k Y _. exact (kk k L (S0 :: S0 :: Y)).
Qed.

Lemma x2 : forall w L,
  Reach1 tm (StD, (L, S0, rep O w ++ [S1; S1])) (StD, (L, S0, rep Z w ++ [S0; S0; S1])).
Proof.
  intros w L. rr 1. rt (cwalk w (S0 :: L) [S1; S1]). rr 3.
  rewrite rep_triple.
  change (StD, (S1 :: rep [S1] (w + w + w) ++ S0 :: L, S1, [S1]))
    with (cL StD (rep [S1] (2 + (w + w + w)) ++ S0 :: L) [S1]).
  rt (dsweep (2 + (w + w + w)) (S0 :: L) [S1]). rewrite rep_triple.
  change (rep [S0] (2 + (w + w + w)) ++ [S1]) with (S0 :: S0 :: rep [S0] (w + w + w) ++ [S1]).
  rewrite !rep1_snoc. r0.
Qed.

Lemma x4 : forall w,
  Reach1 tm (StD, ([], S0, rep O w ++ [S1; S0; S1])) (StD, ([], S0, rep [S1] (5 + (w + w + w)))).
Proof.
  intros w. rr 1. rt (cwalk w [S0] [S1; S0; S1]). rr 3.
  rewrite rep_triple.
  change (StB, (S1 :: rep [S1] (w + w + w) ++ [S0], S1, [S1]))
    with (cL StB (rep [S1] (2 + (w + w + w)) ++ [S0]) [S1]).
  rt (bsweep (2 + (w + w + w)) [S0] [S1]). rr 2.
  rewrite rep1_snoc, app_nil_r. r0.
Qed.

Lemma x0 : forall n,
  Reach1 tm (StD, ([], S0, rep [S1; S1] n ++ [S1])) (StD, ([], S0, rep [S0] (3 + (n + n)) ++ [S1])).
Proof.
  intros n. rr 1. rt (c2walk n [S0] [S1]). rr 6.
  rewrite rep_pair.
  change (StD, (S1 :: S1 :: rep [S1] (n + n) ++ [S0], S1, [S1]))
    with (cL StD (rep [S1] (3 + (n + n)) ++ [S0]) [S1]).
  rt (dsweep (3 + (n + n)) [S0] [S1]). r0.
Qed.

Definition Cf (i : nat) : cconf := (StD, ([], S0, rep [S1] (5 + 6 * i))).

Lemma tokk : forall i, Reach0 tm (Cf i) (StD, ([], S0, rep O (S (S (i + i))) ++ [S0; S1])).
Proof.
  intros i. unfold Cf. set (w := S (S (i + i))).
  replace (5 + 6 * i) with (S ((3 * i + 2) + (3 * i + 2))) by lia.
  rewrite rep_S_r, <- rep_pair.
  rt (x0 (3 * i + 2)).
  replace (rep [S0] (3 + ((3 * i + 2) + (3 * i + 2))) ++ [S1]) with (rep Z w ++ [S0; S1]).
  2: { rewrite rep_triple. replace (3 + (3 * i + 2 + (3 * i + 2))) with (S (w + w + w)) by (unfold w; lia).
       rewrite rep_S_r, <- app_assoc. reflexivity. }
  exact (count w [] [S0; S1]).
Qed.

Lemma tox4 : forall i, Reach0 tm (Cf i) (StD, ([], S0, rep O (S (S (i + i))) ++ [S1; S0; S1])).
Proof.
  intros i. unfold Cf. set (w := S (S (i + i))).
  replace (5 + 6 * i) with (S ((3 * i + 2) + (3 * i + 2))) by lia.
  rewrite rep_S_r, <- rep_pair.
  rt (x0 (3 * i + 2)).
  replace (rep [S0] (3 + ((3 * i + 2) + (3 * i + 2))) ++ [S1]) with (rep Z w ++ [S0; S1]).
  2: { rewrite rep_triple. replace (3 + (3 * i + 2 + (3 * i + 2))) with (S (w + w + w)) by (unfold w; lia).
       rewrite rep_S_r, <- app_assoc. reflexivity. }
  rt (count w [] [S0; S1]). rt (kk w [] [S1]).
  rt (count w [] [S1; S1]). rt (x2 w []).
  rt (count w [] [S0; S0; S1]). rt (kk w [] [S0; S1]).
  exact (count w [] [S1; S0; S1]).
Qed.

Lemma lap : forall i, Reach1 tm (Cf i) (Cf (S i)).
Proof.
  intros i. eapply reach01; [apply tox4|]. rt1 (x4 (S (S (i + i)))). unfold Cf. rfix.
Qed.

Lemma fires : forall t, ~ In t [] -> forall i, Fires tm (Cf i) t.
Proof.
  intros [q s] _ i. destruct q, s;
  first [ unfold Cf; replace (5 + 6 * i) with (S (S (S (S (S (6 * i)))))) by lia; fire_find
        | eapply fire_back; [apply tox4|]; fire_find
        | eapply fire_back; [apply tox4|]; eapply fire_back;
          [rr 1; rt (cwalk (S (S (i + i))) [S0] [S1; S0; S1]); r0|]; fire_find
        | eapply fire_back; [apply tokk|]; eapply fire_back;
          [rr 1; rt (cwalk (S (S (i + i))) [S0] [S0; S1]); r0|]; fire_find ].
Qed.

Theorem nqhtr_1RB1RC_1LC1LB_1LD1RA_0RC0LD : NeverQuasiHaltsTr tm_1RB1RC_1LC1LB_1LD1RA_0RC0LD.
Proof.
  apply (boardS_neverqhtr _ [] Cf lap fires 17).
  apply boot_ok. vm_compute. reflexivity.
Qed.
