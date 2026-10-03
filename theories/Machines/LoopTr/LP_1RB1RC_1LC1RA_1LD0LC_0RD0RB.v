(** * LP_1RB1RC_1LC1RA_1LD0LC_0RD0RB (SCOPING_INSTR 7.4.LE10)

    LE8's "pairs of counts sliding two cells per pair".  At the anchor
    [A [0]] with [111] to its left: low pairs [00] / [10], a frontier
    pair [01] (then [11]), untouched [11] pairs.  Every carry walks [A]
    right ([awalk]), sweeps [C] left over all the ones to the blank
    ([csweep]), and rebuilds [111] in a constant dance ([sd], two cells
    of blank padding).  That is [g] (the low carry and the carry into the
    frontier, for any tail) and [cf2] (the frontier moves).  [loopstep] is
    count, [g], count, [cf2]; [loop] iterates it.  The overflow [fin] runs
    a 7-step unit leftwards over the ones ([dwalk], [sweepFL]):
    [A [0] 01 (11)^(i+1)] becomes [A [0] 01 (11)^(i+2)].

    Hand-stated, kernel-checked.  Axiom footprint: [functional_extensionality_dep]. *)
From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Definition tm_1RB1RC_1LC1RA_1LD0LC_0RD0RB : TM := fun q s => match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB) | StA, S1 => Some (mkTrans S1 DR StC)
  | StB, S0 => Some (mkTrans S1 DL StC) | StB, S1 => Some (mkTrans S1 DR StA)
  | StC, S0 => Some (mkTrans S1 DL StD) | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DR StD) | StD, S1 => Some (mkTrans S0 DR StB)
  end.
Local Notation tm := (tm_wrap_trs tm_1RB1RC_1LC1RA_1LD0LC_0RD0RB []).
Local Notation L3 := [S1; S1; S1].

Lemma awalk : forall n L R, Reach0 tm (cR StA L (rep [S0; S1] n ++ R)) (cR StA (rep [S1; S1] n ++ L) R).
Proof. apply sweepR. intros L R. rr 2. r0. Qed.

Lemma csweep : forall n L R, Reach0 tm (cL StC (rep [S1] n ++ L) R) (cL StC L (rep [S0] n ++ R)).
Proof. apply sweepL. intros L R. rr 1. r0. Qed.

Lemma sd : forall j R,
  Reach0 tm (StC, (S1 :: S1 :: rep [S1; S1] j ++ L3, S1, R))
            (StA, (L3 ++ rep [S0] 2, S0, S0 :: S0 :: rep [S0] (j + j) ++ R)).
Proof.
  intros j R. change (StC, (S1 :: S1 :: rep [S1; S1] j ++ L3, S1, R))
    with (cL StC (S1 :: S1 :: S1 :: rep [S1; S1] j ++ [S1; S1; S1]) R).
  rewrite rep_pair, !rep1_snoc.
  change (S1 :: S1 :: S1 :: S1 :: S1 :: S1 :: rep [S1] (j + j) ++ [])
    with (rep [S1] (6 + (j + j)) ++ []).
  rt (csweep (6 + (j + j)) [] R). rr 22. r0.
Qed.

Lemma gg : forall j rest,
  Reach1 tm (StA, (L3, S0, rep [S1; S0] (S j) ++ S0 :: rest))
            (StA, (L3, S0, rep [S0; S0] (S j) ++ S1 :: rest)).
Proof.
  intros j rest. change (StA, (L3, S0, rep [S1; S0] (S j) ++ S0 :: rest))
    with (cR StA L3 (S0 :: rep [S1; S0] (S j) ++ S0 :: rest)).
  rewrite (rep_shift S0 S1 (S j)).
  eapply reach01; [apply (awalk (S j) L3 (S0 :: S0 :: rest))|]. rr 2.
  rt (sd j (S1 :: rest)).
  apply (reach0_lift_r _ _ _ (StA, (L3 ++ rep [S0] 2, S0, rep [S0; S0] (S j) ++ S1 :: rest))).
  { symmetry. exact (lift_padL 2 _ _ _ _). }
  rewrite rep_pair. replace (S j + S j) with (S (S (j + j))) by lia. r0.
Qed.

Lemma gg0 : forall rest,
  Reach1 tm (StA, (L3, S0, S0 :: rest)) (StA, (L3, S0, S1 :: rest)).
Proof.
  intros rest.
  apply (reach1_lift_r _ _ _ (StA, (L3 ++ rep [S0] 2, S0, S1 :: rest))).
  { symmetry. exact (lift_padL 2 _ _ _ _). }
  rr 1. rgo.
Qed.

Lemma g : forall j rest,
  Reach1 tm (StA, (L3, S0, rep [S1; S0] j ++ S0 :: rest)) (StA, (L3, S0, rep [S0; S0] j ++ S1 :: rest)).
Proof. intros [|j] rest; [apply gg0 | apply gg]. Qed.


Lemma cf2 : forall j Y,
  Reach1 tm (StA, (L3, S0, rep [S1; S0] j ++ [S1; S1; S1; S1] ++ Y))
            (StA, (L3, S0, rep [S0; S0] (S j) ++ [S0; S1] ++ Y)).
Proof.
  intros j Y. change (StA, (L3, S0, rep [S1; S0] j ++ [S1; S1; S1; S1] ++ Y))
    with (cR StA L3 (S0 :: rep [S1; S0] j ++ S1 :: S1 :: S1 :: S1 :: Y)).
  rewrite (rep_shift S0 S1 j).
  change (rep [S0; S1] j ++ S0 :: S1 :: S1 :: S1 :: S1 :: Y) with (rep [S0; S1] j ++ [S0; S1] ++ S1 :: S1 :: S1 :: Y).
  rewrite app_assoc, <- rep_S_r.
  eapply reach01; [apply (awalk (S j) L3 (S1 :: S1 :: S1 :: Y))|]. rr 2.
  rt (sd j (S0 :: S1 :: Y)).
  apply (reach0_lift_r _ _ _ (StA, (L3 ++ rep [S0] 2, S0, rep [S0; S0] (S j) ++ [S0; S1] ++ Y))).
  { symmetry. exact (lift_padL 2 _ _ _ _). }
  rewrite rep_pair. replace (S j + S j) with (S (S (j + j))) by lia.
  change (rep [S0] (S (S (j + j))) ++ [S0; S1] ++ Y) with (S0 :: S0 :: rep [S0] (j + j) ++ S0 :: S1 :: Y).
  rewrite rep1_snoc. r0.
Qed.

Definition FD (L R : list Sym) : cconf := (StD, (L, S1, [S1; S0; S0] ++ R)).

Lemma dwalk : forall n L R, Reach0 tm (FD (rep [S1] n ++ L) R) (FD L (rep [S1] n ++ R)).
Proof. apply sweepFL. intros L R. unfold FD. rr 7. r0. Qed.

Lemma fin : forall r,
  Reach1 tm (StA, (L3, S0, rep [S1; S0] r ++ [S1; S1])) (StA, (L3, S0, [S0; S1] ++ rep [S1; S1] (S r))).
Proof.
  intros r.
  replace ([S0; S1] ++ rep [S1; S1] (S r)) with (S0 :: S1 :: S1 :: rep [S1] (r + r) ++ [S1]).
  2: { rewrite rep_pair, rep1_snoc, app_nil_r. replace (S r + S r) with (S (S (r + r))) by lia. reflexivity. }
  change (StA, (L3, S0, rep [S1; S0] r ++ [S1; S1]))
    with (cR StA L3 (S0 :: rep [S1; S0] r ++ S1 :: [S1])).
  rewrite (rep_shift S0 S1 r).
  change (rep [S0; S1] r ++ S0 :: S1 :: [S1]) with (rep [S0; S1] r ++ [S0; S1] ++ [S1]).
  rewrite app_assoc, <- rep_S_r.
  eapply reach01; [apply (awalk (S r) L3 [S1])|]. rr 9.
  change (StD, (S1 :: rep [S1; S1] r ++ L3, S1, [S1; S0; S0; S1]))
    with (FD (S1 :: rep [S1; S1] r ++ [S1; S1; S1]) [S1]).
  assert (E : S1 :: rep [S1; S1] r ++ [S1; S1; S1] = rep [S1] (4 + (r + r)) ++ [])
    by (rewrite rep_pair, !rep1_snoc; reflexivity).
  rewrite E.
  rt (dwalk (4 + (r + r)) [] [S1]). unfold FD.
  apply (reach0_lift_r _ _ _ (StA, (L3 ++ rep [S0] 2, S0, S0 :: S1 :: S1 :: rep [S1] (r + r) ++ [S1]))).
  { symmetry. exact (lift_padL 2 _ _ _ _). }
  rgo_n 100.
Qed.

Lemma count : forall w Y,
  Reach0 tm (StA, (L3, S0, rep [S0; S0] w ++ Y)) (StA, (L3, S0, rep [S1; S0] w ++ Y)).
Proof.
  intros w. apply (count_from_carry_lt tm (fun l => (StA, (L3, S0, l))) [S0; S0] [S1; S0] w).
  intros k Y _. exact (g k (S0 :: Y)).
Qed.

Lemma loopstep : forall w Z,
  Reach0 tm (StA, (L3, S0, rep [S0; S0] w ++ [S0; S1] ++ [S1; S1] ++ Z))
            (StA, (L3, S0, rep [S0; S0] (S w) ++ [S0; S1] ++ Z)).
Proof.
  intros w Z. rt (count w ([S0; S1] ++ [S1; S1] ++ Z)).
  rt (g w (S1 :: S1 :: S1 :: Z)). rt (count w ([S1; S1; S1; S1] ++ Z)).
  rt (cf2 w Z). r0.
Qed.

Lemma loop : forall r w Z,
  Reach0 tm (StA, (L3, S0, rep [S0; S0] w ++ [S0; S1] ++ rep [S1; S1] r ++ Z))
            (StA, (L3, S0, rep [S0; S0] (w + r) ++ [S0; S1] ++ Z)).
Proof.
  induction r as [|r IH]; intros w Z; [rfix|].
  change (rep [S1; S1] (S r) ++ Z) with ([S1; S1] ++ rep [S1; S1] r ++ Z).
  rt (loopstep w (rep [S1; S1] r ++ Z)). rt (IH (S w) Z). rfix.
Qed.

Definition Cf (i : nat) : cconf := (StA, (L3, S0, [S0; S1] ++ rep [S1; S1] (S i))).

Lemma tofin : forall i, Reach0 tm (Cf i) (StA, (L3, S0, rep [S1; S0] (S i) ++ [S1; S1])).
Proof.
  intros i. unfold Cf. rewrite <- (app_nil_r (rep [S1; S1] (S i))).
  change ([S0; S1] ++ rep [S1; S1] (S i) ++ []) with (rep [S0; S0] 0 ++ [S0; S1] ++ rep [S1; S1] (S i) ++ []).
  rt (loop (S i) 0 []). cbn [Nat.add].
  rt (count (S i) ([S0; S1] ++ [])). rt (g (S i) [S1]). exact (count (S i) [S1; S1]).
Qed.

Lemma lap : forall i, Reach1 tm (Cf i) (Cf (S i)).
Proof. intros i. eapply reach01; [apply tofin|]. exact (fin (S i)). Qed.

Lemma fires : forall t, ~ In t [] -> forall i, Fires tm (Cf i) t.
Proof.
  intros [q s] _ i. destruct q, s;
  first [ unfold Cf; fire_find
        | eapply fire_back; [apply tofin|]; fire_find ].
Qed.

Theorem nqhtr_1RB1RC_1LC1RA_1LD0LC_0RD0RB : NeverQuasiHaltsTr tm_1RB1RC_1LC1RA_1LD0LC_0RD0RB.
Proof.
  apply (boardS_neverqhtr _ [] Cf lap fires 214).
  apply boot_ok. vm_compute. reflexivity.
Qed.
