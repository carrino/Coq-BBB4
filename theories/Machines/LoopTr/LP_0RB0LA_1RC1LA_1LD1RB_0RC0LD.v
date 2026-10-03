(** * LP_0RB0LA_1RC1LA_1LD1RB_0RC0LD (SCOPING_INSTR 7.4.LE10)

    LE8's "ruler sequence of counts".  A binary counter over [00] / [01]
    at the anchor [A [0]].  Its carry over [k] digits ([ca], no
    induction) walks [B] right over the digits, sweeps [D] back, and then
    runs a full count of a second binary counter of [k] digits at the
    [D [0] 0] anchor ([ic], from [dc], whose carries are linear).  Then [B]
    walks right again and [A] sweeps the digits to zero.  The lap is a count
    of the [A] counter and one carry against the blank:
    [A [0] (00)^(i+3) 01] becomes [A [0] (00)^(i+4) 01].

    Hand-stated, kernel-checked.  Axiom footprint: [functional_extensionality_dep]. *)
From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Definition tm_0RB0LA_1RC1LA_1LD1RB_0RC0LD : TM := fun q s => match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB) | StA, S1 => Some (mkTrans S0 DL StA)
  | StB, S0 => Some (mkTrans S1 DR StC) | StB, S1 => Some (mkTrans S1 DL StA)
  | StC, S0 => Some (mkTrans S1 DL StD) | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S0 DR StC) | StD, S1 => Some (mkTrans S0 DL StD)
  end.
Local Notation tm := (tm_wrap_trs tm_0RB0LA_1RC1LA_1LD1RB_0RC0LD []).
Local Notation P0 := [S0; S0].
Local Notation P1 := [S0; S1].
Local Notation P3 := [S1; S1].

Lemma bsweep : forall n L R, Reach0 tm (cR StB L (rep P1 n ++ R)) (cR StB (rep P3 n ++ L) R).
Proof. apply sweepR. intros L R. rr 2. r0. Qed.

Lemma dsweep : forall n L R, Reach0 tm (cL StD (rep [S1] n ++ L) R) (cL StD L (rep [S0] n ++ R)).
Proof. apply sweepL. intros L R. rr 1. r0. Qed.

Lemma asweep : forall n L R, Reach0 tm (cL StA (rep [S1] n ++ L) R) (cL StA L (rep [S0] n ++ R)).
Proof. apply sweepL. intros L R. rr 1. r0. Qed.

(** the inner counter at the [D] anchor: linear carries *)
Lemma dc : forall j L Y,
  Reach1 tm (StD, (L, S0, S0 :: rep P1 j ++ P0 ++ Y)) (StD, (L, S0, S0 :: rep P0 j ++ P1 ++ Y)).
Proof.
  intros j L Y. rr 4. rt (bsweep j (S1 :: S0 :: L) (P0 ++ Y)). rr 2.
  rewrite !rep_pair, rep1_snoc.
  rt (dsweep (2 + (j + j)) (S0 :: L) (S1 :: Y)).
  change (P1 ++ Y) with (S0 :: S1 :: Y). rewrite rep1_snoc. r0.
Qed.

Lemma ic : forall w L Y,
  Reach0 tm (StD, (L, S0, S0 :: rep P0 w ++ Y)) (StD, (L, S0, S0 :: rep P1 w ++ Y)).
Proof.
  intros w L. apply (count_from_carry_lt tm (fun l => (StD, (L, S0, S0 :: l))) P0 P1 w).
  intros k Y _. exact (dc k L Y).
Qed.

Lemma ca : forall k L Y,
  Reach1 tm (StA, (L, S0, rep P1 k ++ P0 ++ Y)) (StA, (L, S0, rep P0 k ++ P1 ++ Y)).
Proof.
  intros k L Y. rr 1. rt (bsweep k (S0 :: L) (P0 ++ Y)). rr 2.
  rewrite rep_pair.
  rt (dsweep (1 + (k + k)) (S0 :: L) (S1 :: Y)).
  change (rep [S0] (1 + (k + k))) with (S0 :: rep [S0] (k + k)). rewrite <- rep_pair.
  rt (ic k L (S1 :: Y)). rr 4. rt (bsweep k (S1 :: S0 :: L) (S1 :: Y)). rr 1.
  rewrite rep_pair, rep1_snoc. rt (asweep (1 + (k + k)) (S0 :: L) (S1 :: Y)).
  rewrite rep_pair. change (P1 ++ Y) with (S0 :: S1 :: Y). rewrite rep1_snoc. r0.
Qed.

Definition Cf (i : nat) : cconf := (StA, ([], S0, rep P0 (S (S (S i))) ++ P1)).

Lemma lap : forall i, Reach1 tm (Cf i) (Cf (S i)).
Proof.
  intros i. unfold Cf.
  eapply reach01; [exact (count_from_carry_lt tm (fun l => (StA, ([], S0, l))) P0 P1 (S (S (S i)))
                            (fun k Y _ => ca k [] Y) P1)|].
  apply (reach1_lift_l tm _ (StA, ([], S0, rep P1 (S (S (S (S i)))) ++ P0 ++ []))).
  { change (rep P1 (S (S (S (S i))))) with (P1 ++ rep P1 (S (S (S i)))).
    rewrite <- rep_comm, <- app_assoc, app_nil_r, app_assoc. symmetry. exact (lift_padR 2 _ _ _ _). }
  eapply reach10; [exact (ca _ [] [])|]. rewrite app_nil_r. r0.
Qed.

Lemma fires : forall t, ~ In t [] -> forall i, Fires tm (Cf i) t.
Proof. intros [q s] _ i. unfold Cf. destruct q, s; fire_find. Qed.

Theorem nqhtr_0RB0LA_1RC1LA_1LD1RB_0RC0LD : NeverQuasiHaltsTr tm_0RB0LA_1RC1LA_1LD1RB_0RC0LD.
Proof.
  apply (boardS_neverqhtr _ [] Cf lap fires 252).
  apply boot_ok. vm_compute. reflexivity.
Qed.
