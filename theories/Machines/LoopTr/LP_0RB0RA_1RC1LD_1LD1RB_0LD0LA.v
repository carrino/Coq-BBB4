(** * LP_0RB0RA_1RC1LD_1LD1RB_0LD0LA (SCOPING_INSTR 7.4.LE10)

    LE8's ratio-3 carries, second class: the same lemmas as
    [LP_0RB0RA_1RC1LD_1LC1RB_0LD0LA] ([C0] goes to [D] here, not [C]).
    The steps between the sweeps are found by [rr_upto] / [rgo].

    Hand-stated, kernel-checked.  Axiom footprint: [functional_extensionality_dep]. *)
From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Definition tm_0RB0RA_1RC1LD_1LD1RB_0LD0LA : TM := fun q s => match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB) | StA, S1 => Some (mkTrans S0 DR StA)
  | StB, S0 => Some (mkTrans S1 DR StC) | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StD) | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S0 DL StD) | StD, S1 => Some (mkTrans S0 DL StA)
  end.
Local Notation tm := (tm_wrap_trs tm_0RB0RA_1RC1LD_1LD1RB_0LD0LA []).
Local Notation P0 := [S0; S0].
Local Notation P1 := [S0; S1].
Local Notation P3 := [S1; S1].

Lemma bsweep : forall n L R, Reach0 tm (cR StB L (rep P1 n ++ R)) (cR StB (rep P3 n ++ L) R).
Proof. apply sweepR. intros L R. rr 2. r0. Qed.

Lemma dsweep : forall n L R, Reach0 tm (cL StD (rep [S0] n ++ L) R) (cL StD L (rep [S0] n ++ R)).
Proof. apply sweepL. intros L R. rr 1. r0. Qed.

Definition CA k := forall L Y,
  Reach1 tm (StA, (L, S0, rep P1 k ++ P0 ++ Y)) (StA, (L, S0, rep P0 k ++ P1 ++ Y)).

Lemma count_of : forall w, (forall j, j < w -> CA j) -> forall L Y,
  Reach0 tm (StA, (L, S0, rep P0 w ++ Y)) (StA, (L, S0, rep P1 w ++ Y)).
Proof.
  intros w H L. apply (count_from_carry_lt tm (fun l => (StA, (L, S0, l))) P0 P1 w).
  intros k Y Hk. exact (H k Hk L Y).
Qed.

Definition QQ j := forall L Y,
  Reach0 tm (StA, (S0 :: rep P3 j ++ L, S0, P0 ++ S1 :: Y))
            (StA, (S0 :: rep P0 j ++ L, S0, P1 ++ S1 :: Y)).

Lemma t1 : forall j L Y,
  Reach0 tm (StA, (S0 :: rep P0 j ++ S1 :: S1 :: L, S0, P1 ++ S1 :: Y))
            (StA, (S0 :: L, S0, rep P0 (S (S j)) ++ S1 :: Y)).
Proof.
  intros j L Y. rewrite rep_pair.
  rr_upto 20 ltac:(rt (dsweep (4 + (j + j)) (S1 :: S1 :: L) (S1 :: Y))). rr 2.
  rewrite rep_pair. replace (S (S j) + S (S j)) with (4 + (j + j)) by lia. r0.
Qed.

Lemma t2 : forall j L Y,
  Reach0 tm (StA, (S0 :: L, S0, rep P1 (S (S j)) ++ S1 :: Y))
            (StA, (S0 :: rep P3 j ++ S0 :: S0 :: L, S0, P0 ++ S1 :: Y)).
Proof.
  intros j L Y. rr 1. rt (bsweep (S (S j)) (S0 :: S0 :: L) (S1 :: Y)). rgo.
Qed.

Lemma qq : forall n, (forall j, j <= n -> CA j) -> forall j, j <= n -> QQ j.
Proof.
  intros n HC j. induction j as [|j IH]; intros Hj L Y.
  - rt (reach1_0 _ _ _ (HC 0 ltac:(lia) (S0 :: L) (S1 :: Y))). r0.
  - change (rep P3 (S j)) with (P3 ++ rep P3 j). change (rep P0 (S j)) with (P0 ++ rep P0 j).
    rewrite <- (rep_comm P3 j), <- (rep_comm P0 j), <- !app_assoc.
    rt (IH ltac:(lia) (P3 ++ L) Y). rt (t1 j L Y).
    rt (count_of (S (S j)) (fun i Hi => HC i ltac:(lia)) (S0 :: L) (S1 :: Y)).
    rt (t2 j L Y). rt (IH ltac:(lia) (P0 ++ L) Y).
    r0.
Qed.

Lemma setup : forall j L Y,
  Reach1 tm (StA, (L, S0, rep P1 (S (S j)) ++ P0 ++ Y))
            (StA, (S0 :: S1 :: rep P3 j ++ S0 :: L, S0, P0 ++ S1 :: Y)).
Proof.
  intros j L Y. rr 1. rt (bsweep (S (S j)) (S0 :: L) (P0 ++ Y)). cbn [rep app]. rgo.
Qed.

Lemma s1_p3 : forall j l, S1 :: rep P3 j ++ l = rep P3 j ++ S1 :: l.
Proof. intros j l. rewrite rep_pair. symmetry. apply rep1_snoc. Qed.

Lemma fin : forall j L Y,
  Reach0 tm (StA, (S0 :: rep P0 j ++ S1 :: S0 :: L, S0, P1 ++ S1 :: Y))
            (StA, (L, S0, rep P0 (S (S j)) ++ P1 ++ Y)).
Proof.
  intros j L Y. rewrite rep_pair.
  rr_upto 20 ltac:(rt (dsweep (4 + (j + j)) (S1 :: S0 :: L) (S1 :: Y))). rr 1.
  rewrite rep_pair. replace (S (S j) + S (S j)) with (4 + (j + j)) by lia.
  change ([S0; S1] ++ Y) with (S0 :: S1 :: Y). rewrite rep1_snoc. r0.
Qed.

Lemma ca : forall n, forall k, k <= n -> CA k.
Proof.
  induction n as [|n IH]; intros k Hk.
  - replace k with 0 by lia. intros L Y. rr 1. rgo.
  - destruct k as [|[|j]].
    + intros L Y. rr 1. rgo.
    + intros L Y. rr 1. rgo.
    + intros L Y. rt1 (setup j L Y). rewrite s1_p3.
      rt (qq n IH j ltac:(lia) (S1 :: S0 :: L) Y). exact (fin j L Y).
Qed.

Definition Cf (i : nat) : cconf := (StA, ([], S0, rep P0 (S (S (S i))) ++ P1)).

Lemma lap : forall i, Reach1 tm (Cf i) (Cf (S i)).
Proof.
  intros i. unfold Cf.
  eapply reach01; [exact (count_of (S (S (S i))) (fun j _ => ca j j (le_n j)) [] P1)|].
  apply (reach1_lift_l tm _ (StA, ([], S0, rep P1 (S (S (S (S i)))) ++ P0 ++ []))).
  { change (rep P1 (S (S (S (S i))))) with (P1 ++ rep P1 (S (S (S i)))).
    rewrite <- rep_comm, <- app_assoc, app_nil_r, app_assoc. symmetry. exact (lift_padR 2 _ _ _ _). }
  eapply reach10; [exact (ca _ _ (le_n _) [] [])|]. rewrite app_nil_r. r0.
Qed.

Lemma fires : forall t, ~ In t [] -> forall i, Fires tm (Cf i) t.
Proof. intros [q s] _ i. unfold Cf. destruct q, s; fire_find. Qed.

Theorem nqhtr_0RB0RA_1RC1LD_1LD1RB_0LD0LA : NeverQuasiHaltsTr tm_0RB0RA_1RC1LD_1LD1RB_0LD0LA.
Proof.
  apply (boardS_neverqhtr _ [] Cf lap fires 160).
  apply boot_ok. vm_compute. reflexivity.
Qed.
