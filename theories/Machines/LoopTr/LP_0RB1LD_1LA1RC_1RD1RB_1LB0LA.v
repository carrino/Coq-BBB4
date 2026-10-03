(** * LP_0RB1LD_1LA1RC_1RD1RB_1LB0LA (SCOPING_INSTR 7.4.LE10)

    LE8's "pairs of counts of growing width over a mixed encoding".
    Pairs after the anchor [A [0]]: low digits [01] = 0, [11] = 1, then a
    frontier pair ([00], then [10]), then untouched [10] pairs, then [11].
    All carries are linear ([cB0], [c10], [cend]: [B] walks right over
    [11], [A]/[D] walk back writing [01]).  [loopstep] is a count of the
    low width, the carry into the frontier [00 -> 10], a second count, and
    the carry that moves the frontier one pair right.  [loop] iterates it
    over the untouched pairs.  Then come two more counts and the
    overflows, ending in [final], one cell to the left:
    [A [0] 11 (10)^m 11] becomes [A [0] 11 (10)^(m+3) 11].

    Hand-stated, kernel-checked.  Axiom footprint: [functional_extensionality_dep]. *)
From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Definition tm_0RB1LD_1LA1RC_1RD1RB_1LB0LA : TM := fun q s => match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB) | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DL StA) | StB, S1 => Some (mkTrans S1 DR StC)
  | StC, S0 => Some (mkTrans S1 DR StD) | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S1 DL StB) | StD, S1 => Some (mkTrans S0 DL StA)
  end.
Local Notation tm := (tm_wrap_trs tm_0RB1LD_1LA1RC_1RD1RB_1LB0LA []).
Local Notation Pz := [S0; S0].
Local Notation P1 := [S0; S1].
Local Notation Ph := [S1; S0].
Local Notation P3 := [S1; S1].

Lemma bsweep : forall n L R, Reach0 tm (cR StB L (rep P3 n ++ R)) (cR StB (rep P3 n ++ L) R).
Proof. apply sweepR. intros L R. rr 2. r0. Qed.

Lemma asweep : forall n L R, Reach0 tm (cL StA (rep P3 n ++ L) R) (cL StA L (rep P1 n ++ R)).
Proof. apply sweepL. intros L R. rr 2. r0. Qed.

(** the low carry, and the carry into the frontier *)
Lemma cB0 : forall k x L Y,
  Reach1 tm (StA, (L, S0, rep P3 k ++ S0 :: x :: Y)) (StA, (L, S0, rep P1 k ++ S1 :: x :: Y)).
Proof.
  intros k x L Y. rr 1. rt (bsweep k (S0 :: L) (S0 :: x :: Y)). rr 1.
  rt (asweep k (S0 :: L) (S1 :: x :: Y)). r0.
Qed.

Lemma cend : forall k L,
  Reach1 tm (StA, (L, S0, rep P3 k ++ [])) (StA, (L, S0, rep P1 k ++ [S1])).
Proof.
  intros k L. rr 1. rt (bsweep k (S0 :: L) []). rr 1.
  rt (asweep k (S0 :: L) [S1]). r0.
Qed.

Lemma c10 : forall k x L Y,
  Reach1 tm (StA, (L, S0, rep P3 k ++ S1 :: S0 :: S1 :: x :: Y))
            (StA, (L, S0, rep P1 (S k) ++ S0 :: x :: Y)).
Proof.
  intros k x L Y. rr 1. rt (bsweep k (S0 :: L) (S1 :: S0 :: S1 :: x :: Y)). rr 3.
  rt (asweep (S k) (S0 :: L) (S0 :: x :: Y)). r0.
Qed.

Lemma count : forall w L Y,
  Reach0 tm (StA, (L, S0, rep P1 w ++ Y)) (StA, (L, S0, rep P3 w ++ Y)).
Proof.
  intros w L. apply (count_from_carry_lt tm (fun l => (StA, (L, S0, l))) P1 P3 w).
  intros k Y _. exact (cB0 k S1 L Y).
Qed.

Lemma loopstep : forall w L Z,
  Reach0 tm (StA, (L, S0, rep P1 w ++ Pz ++ Ph ++ Z)) (StA, (L, S0, rep P1 (S w) ++ Pz ++ Z)).
Proof.
  intros w L Z. rt (count w L (Pz ++ Ph ++ Z)). rt (cB0 w S0 L (Ph ++ Z)).
  rt (count w L (Ph ++ Ph ++ Z)). rt (c10 w S0 L Z). r0.
Qed.

Lemma loop : forall r w L Z,
  Reach0 tm (StA, (L, S0, rep P1 w ++ Pz ++ rep Ph r ++ Z)) (StA, (L, S0, rep P1 (w + r) ++ Pz ++ Z)).
Proof.
  induction r as [|r IH]; intros w L Z; [rfix|].
  rt (loopstep w L (rep Ph r ++ Z)). rt (IH (S w) L Z). rfix.
Qed.

Lemma final : forall n,
  Reach1 tm (StA, ([], S0, rep P3 n ++ [S1])) (StA, ([], S0, P3 ++ rep Ph (S n) ++ P3)).
Proof.
  intros n. rr 1. rt (bsweep n [S0] [S1]). rr 6.
  rewrite (rep_shift S1 S1 n [S0]).
  rt (asweep (S n) [S1; S0] [S1]). rr 3.
  change (P3 ++ rep Ph (S n) ++ P3) with (S1 :: S1 :: (rep [S1; S0] (S n) ++ S1 :: [S1])).
  rewrite <- (rep_shift S1 S0 (S n) [S1]). r0.
Qed.

(** the lap for every width [m + 2] *)
Definition Cg (m : nat) : cconf := (StA, ([], S0, P3 ++ rep Ph (S (S m)) ++ P3)).

Lemma setup : forall r,
  Reach1 tm (StA, ([], S0, P3 ++ rep Ph (S (S r)) ++ P3)) (StA, ([], S0, rep P1 2 ++ Pz ++ rep Ph r ++ P3)).
Proof. intros r. rr 1. rgo. Qed.

Lemma tofinal : forall m, Reach0 tm (Cg m) (StA, ([], S0, rep P3 (S (S (2 + m))) ++ [S1])).
Proof.
  intros m. unfold Cg.
  rt (setup m). rt (loop m 2 [] P3).
  set (K := 2 + m).
  rt (count K [] (Pz ++ P3)). rt (cB0 K S0 [] P3).
  rt (count K [] (Ph ++ P3)). rt (c10 K S1 [] []).
  change (S0 :: S1 :: []) with (P1 ++ []). rewrite app_assoc, rep_comm.
  change (P1 ++ rep P1 (S K)) with (rep P1 (S (S K))).
  rt (count (S (S K)) [] []). rt (cend (S (S K)) []).
  rt (count (S (S K)) [] [S1]). r0.
Qed.

Lemma lap_g : forall m, Reach1 tm (Cg m) (Cg (3 + m)).
Proof.
  intros m. eapply reach01; [apply tofinal|]. rt1 (final (S (S (2 + m)))).
  unfold Cg. rfix.
Qed.

Lemma fires_g : forall m t, Fires tm (Cg m) t.
Proof.
  intros m [q s]. destruct q, s;
  first [ unfold Cg; fire_find
        | eapply fire_back; [apply tofinal|]; eapply fire_back;
          [rr 1; rt (bsweep (S (S (2 + m))) [S0] [S1]); r0|]; fire_find ].
Qed.

Definition Cf (i : nat) : cconf := Cg (2 + 3 * i).

Lemma lap : forall i, Reach1 tm (Cf i) (Cf (S i)).
Proof. intros i. unfold Cf. replace (2 + 3 * S i) with (3 + (2 + 3 * i)) by lia. apply lap_g. Qed.

Lemma fires : forall t, ~ In t [] -> forall i, Fires tm (Cf i) t.
Proof. intros t _ i. apply fires_g. Qed.

Theorem nqhtr_0RB1LD_1LA1RC_1RD1RB_1LB0LA : NeverQuasiHaltsTr tm_0RB1LD_1LA1RC_1RD1RB_1LB0LA.
Proof.
  apply (boardS_neverqhtr _ [] Cf lap fires 122).
  apply boot_ok. vm_compute. reflexivity.
Qed.
